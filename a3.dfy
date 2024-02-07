class TwoStacks<T(0)(==)> {

    // abstract state
    ghost var s1: seq<T>
    ghost var s2: seq<T>
    ghost var N: nat
    ghost var Repr: set<object>

    // concrete state
    var arr: array<T>
    var size1: nat
    var size2: nat

    ghost predicate Valid()
        reads this, Repr
        ensures Valid() ==> this in Repr
    {
        // abstract state invariants:
        0 <= |s1| + |s2| <= N &&
        0 <= |s1| <= N && 0 <= |s2| <= N &&

        // abstract relation: Repr
        this in Repr &&
        arr in Repr &&

        // abstract relation: s1, s2, N
        arr.Length == N &&
        (forall i :: 0 <= i < |s1| ==> s1[i] == arr[i]) &&
        (forall i :: 0 <= i < |s2| ==> s2[i] == arr[N-1 - i]) &&
        size1 == |s1| && size2 == |s2| &&
        0 <= size1 + size2 <= N
    }

    constructor(n: nat)
        ensures Valid() && fresh(Repr) && s1 == [] && s2 == []
    {
        N := n;
        s1, s2 := [], [];
        arr := new T[n];
        size1, size2 := 0, 0;
        Repr := {this, arr};
    }

    method push1(item: T) returns (success: bool)
        requires Valid()
        modifies Repr
        ensures Valid() && fresh(Repr - old(Repr))
        ensures success ==> s1 == old(s1) + [item]
        ensures !success ==> |s1| + |s2| == N
        ensures !success ==> s1 == old(s1)
        ensures N == old(N) && s2 == old(s2)
    {
        if (0 <= size1 + size2 < arr.Length) { // has space
            arr[size1] := item;
            size1 := size1 + 1;
            s1 := s1 + [item];
            success := true;
        } else {
            success := false;
        }
    }

    method push2(item: T) returns (success: bool)
        requires Valid()
        modifies Repr
        ensures Valid() && fresh(Repr - old(Repr))
        ensures success ==> s2 == old(s2) + [item]
        ensures !success ==> |s1| + |s2| == N
        ensures !success ==> s2 == old(s2)
        ensures N == old(N) && s1 == old(s1)
    {
        if (0 <= size1 + size2 < arr.Length) {
            arr[arr.Length - 1 - size2] := item;
            s2 := s2 + [item];
            size2 := size2 + 1;
            success := true;
        } else {
            success := false;
        }
    }

    method pop1() returns (success: bool, item: T)
        requires Valid()
        modifies Repr
        ensures success ==> old(|s1|) > 0 && s1 == old(s1[..|s1|-1]) && old(s1[|s1| - 1]) == item
        ensures !success ==> s1 == [] == old(s1)
        ensures N == old(N) && s2 == old(s2)
        ensures Valid() && fresh(Repr - old(Repr))
    {
        if (size1 > 0) {
            item := arr[size1 - 1];
            s1 := s1[..|s1|-1];
            size1 := size1 - 1;
            success := true;
        } else {
            item := *;
            success := false;
        }
    }

    method pop2() returns (success: bool, item: T)
        requires Valid()
        modifies Repr
        ensures success ==> old(|s2|) > 0 && s2 == old(s2[..|s2|-1]) && old(s2[|s2| - 1]) == item
        ensures !success ==> s2 == [] == old(s2)
        ensures N == old(N) && s1 == old(s1)
        ensures Valid() && fresh(Repr - old(Repr))
    {
        if (size2 > 0) {
        item := arr[arr.Length - size2];
        s2 := s2[..|s2|-1];
        size2 := size2 - 1;
        success := true;
        } else {
            item := *;
            success := false;
        }
    }

    method peek1() returns (success: bool, item: T)
        requires Valid()
        ensures Valid()
        ensures success ==> |s1| > 0 && item == s1[|s1| - 1]
        ensures !success ==> s1 == [] 
        ensures s1 == old(s1) && s2 == old(s2) && N == old(N) // might be redundant
    {
        if (size1 > 0) {
            item := arr[size1 - 1];
            success := true;
        } else {
            item := *;
            success := false;
        }
    }

    method peek2() returns (success: bool, item: T)
        requires Valid()
        ensures Valid()
        ensures success ==> |s2| > 0 && item == s2[|s2| - 1]
        ensures !success ==> s2 == [] 
        ensures s1 == old(s1) && s2 == old(s2) && N == old(N) // might be redundant
    {
        if (size2 > 0) {
            item := arr[arr.Length - size2];
            success := true;
        } else {
            item := *;
            success := false;
        }
    }

    predicate empty1()
        requires Valid()
        reads this, Repr
        ensures Valid()
        ensures empty1() ==> s1 == []
    {
        size1 == 0
    }

    predicate empty2()
        requires Valid()
        reads this, Repr
        ensures Valid()
        ensures empty2() ==> s2 == []
    {
        size2 == 0
    }

    method search1(item: T) returns (index: int)
        requires Valid()
        ensures Valid()
        ensures -1 <= index < |s1|
        ensures index >= 0 ==> s1[index] == item
        ensures index < 0 ==> (forall i :: 0 <= i < |s1| ==> s1[i] != item) || empty1()
        ensures s1 == old(s1) && s2 == old(s2) && N == old(N) // might be redundant
    {
        if arr.Length == 0 || size1 == 0 {
            return -1;
        }
        var n := 0;
        while n != size1
            invariant 0 <= n <= size1
            invariant forall i :: 0 <= i < n ==> arr[i] != item
        {
            if arr[n] == item {
                return n;
            }
            n := n + 1;
        }
        return -1;
    }

    method search2(item: T) returns (index: int)
        requires Valid()
        ensures Valid()
        ensures -1 <= index < |s2|
        ensures index >= 0 ==> s2[index] == item
        ensures index < 0 ==> (forall i :: 0 <= i < |s2| ==> s2[i] != item) || empty2()
        ensures s1 == old(s1) && s2 == old(s2) && N == old(N) // might be redundant
    {
        if arr.Length == 0 || size2 == 0 {
            return -1;
        }
        var n := arr.Length;
        while n != arr.Length - size2
            decreases n
            invariant arr.Length - size2 <= n <= arr.Length
            invariant forall i :: n <= i < arr.Length ==> arr[i] != item
        {
            n := n - 1;
            if arr[n] == item {
                return arr.Length - 1 - n;
            }
        }
        return -1;
    }
}