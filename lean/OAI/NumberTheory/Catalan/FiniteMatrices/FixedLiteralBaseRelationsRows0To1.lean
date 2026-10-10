import Mathlib.Tactic.FinCases
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularMinusProductRows40To41
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularPlusProductRows40To41
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularZeroInvRows36To47
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularZeroModRows24To35

namespace OAI

section

namespace InternalCatalan

def fixedLiteralModZeroRow_36 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 9
  | 1 => 24
  | 2 => 13
  | 3 => 21
  | 4 => 9
  | 5 => 0
  | 6 => 73
  | 7 => 28
  | 8 => 37
  | 9 => 32
  | 10 => 74
  | 11 => 78
  | 12 => 31
  | 13 => 91
  | 14 => 31
  | 15 => 12
  | 16 => 7
  | 17 => 76
  | 18 => 89
  | 19 => 70
  | 20 => 87
  | 21 => 97
  | 22 => 87
  | 23 => 75
  | 24 => 88
  | 25 => 48
  | 26 => 62
  | 27 => 56
  | 28 => 41
  | 29 => 60
  | 30 => 42
  | 31 => 85
  | 32 => 15
  | 33 => 31
  | 34 => 49
  | 35 => 68
  | 36 => 59
  | 37 => 63
  | 38 => 80
  | 39 => 58
  | 40 => 63
  | 41 => 78
  | 42 => 64
  | 43 => 58
  | 44 => 25
  | 45 => 65
  | 46 => 66
  | 47 => 70
  | _ => 0

def fixedLiteralModZeroRow_37 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 16
  | 1 => 87
  | 2 => 15
  | 3 => 39
  | 4 => 57
  | 5 => 45
  | 6 => 41
  | 7 => 81
  | 8 => 28
  | 9 => 30
  | 10 => 36
  | 11 => 42
  | 12 => 64
  | 13 => 97
  | 14 => 19
  | 15 => 45
  | 16 => 91
  | 17 => 12
  | 18 => 7
  | 19 => 48
  | 20 => 4
  | 21 => 20
  | 22 => 72
  | 23 => 53
  | 24 => 80
  | 25 => 67
  | 26 => 83
  | 27 => 4
  | 28 => 23
  | 29 => 32
  | 30 => 48
  | 31 => 88
  | 32 => 78
  | 33 => 11
  | 34 => 88
  | 35 => 38
  | 36 => 31
  | 37 => 64
  | 38 => 20
  | 39 => 72
  | 40 => 54
  | 41 => 84
  | 42 => 71
  | 43 => 57
  | 44 => 7
  | 45 => 68
  | 46 => 42
  | 47 => 96
  | _ => 0

def fixedLiteralModZeroRow_38 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 59
  | 1 => 34
  | 2 => 83
  | 3 => 4
  | 4 => 64
  | 5 => 70
  | 6 => 13
  | 7 => 73
  | 8 => 82
  | 9 => 8
  | 10 => 22
  | 11 => 55
  | 12 => 87
  | 13 => 68
  | 14 => 13
  | 15 => 39
  | 16 => 14
  | 17 => 40
  | 18 => 92
  | 19 => 94
  | 20 => 72
  | 21 => 99
  | 22 => 99
  | 23 => 67
  | 24 => 81
  | 25 => 50
  | 26 => 73
  | 27 => 80
  | 28 => 26
  | 29 => 14
  | 30 => 4
  | 31 => 90
  | 32 => 95
  | 33 => 10
  | 34 => 45
  | 35 => 81
  | 36 => 27
  | 37 => 98
  | 38 => 82
  | 39 => 90
  | 40 => 79
  | 41 => 90
  | 42 => 10
  | 43 => 39
  | 44 => 91
  | 45 => 61
  | 46 => 39
  | 47 => 23
  | _ => 0

def fixedLiteralModZeroRow_39 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 25
  | 1 => 8
  | 2 => 70
  | 3 => 73
  | 4 => 72
  | 5 => 98
  | 6 => 38
  | 7 => 23
  | 8 => 44
  | 9 => 23
  | 10 => 58
  | 11 => 58
  | 12 => 5
  | 13 => 37
  | 14 => 53
  | 15 => 23
  | 16 => 94
  | 17 => 36
  | 18 => 34
  | 19 => 90
  | 20 => 69
  | 21 => 75
  | 22 => 90
  | 23 => 32
  | 24 => 7
  | 25 => 35
  | 26 => 76
  | 27 => 29
  | 28 => 1
  | 29 => 39
  | 30 => 36
  | 31 => 43
  | 32 => 94
  | 33 => 57
  | 34 => 50
  | 35 => 1
  | 36 => 19
  | 37 => 6
  | 38 => 35
  | 39 => 100
  | 40 => 26
  | 41 => 36
  | 42 => 94
  | 43 => 48
  | 44 => 7
  | 45 => 55
  | 46 => 19
  | 47 => 69
  | _ => 0

def fixedLiteralModZeroRow_40 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 94
  | 1 => 66
  | 2 => 95
  | 3 => 94
  | 4 => 12
  | 5 => 52
  | 6 => 55
  | 7 => 95
  | 8 => 24
  | 9 => 96
  | 10 => 48
  | 11 => 20
  | 12 => 9
  | 13 => 96
  | 14 => 41
  | 15 => 62
  | 16 => 19
  | 17 => 41
  | 18 => 82
  | 19 => 52
  | 20 => 9
  | 21 => 50
  | 22 => 96
  | 23 => 16
  | 24 => 40
  | 25 => 26
  | 26 => 20
  | 27 => 82
  | 28 => 91
  | 29 => 75
  | 30 => 8
  | 31 => 42
  | 32 => 52
  | 33 => 52
  | 34 => 90
  | 35 => 78
  | 36 => 45
  | 37 => 30
  | 38 => 49
  | 39 => 78
  | 40 => 59
  | 41 => 32
  | 42 => 71
  | 43 => 44
  | 44 => 62
  | 45 => 18
  | 46 => 79
  | 47 => 33
  | _ => 0

def fixedLiteralModZeroRow_41 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 44
  | 1 => 50
  | 2 => 62
  | 3 => 82
  | 4 => 40
  | 5 => 83
  | 6 => 63
  | 7 => 87
  | 8 => 43
  | 9 => 94
  | 10 => 12
  | 11 => 23
  | 12 => 98
  | 13 => 95
  | 14 => 57
  | 15 => 41
  | 16 => 31
  | 17 => 80
  | 18 => 30
  | 19 => 15
  | 20 => 76
  | 21 => 45
  | 22 => 41
  | 23 => 3
  | 24 => 82
  | 25 => 37
  | 26 => 52
  | 27 => 75
  | 28 => 5
  | 29 => 23
  | 30 => 26
  | 31 => 58
  | 32 => 28
  | 33 => 38
  | 34 => 50
  | 35 => 54
  | 36 => 37
  | 37 => 41
  | 38 => 65
  | 39 => 17
  | 40 => 74
  | 41 => 70
  | 42 => 96
  | 43 => 31
  | 44 => 80
  | 45 => 6
  | 46 => 82
  | 47 => 5
  | _ => 0

def fixedLiteralModZeroRow_42 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 33
  | 1 => 28
  | 2 => 93
  | 3 => 2
  | 4 => 64
  | 5 => 58
  | 6 => 85
  | 7 => 51
  | 8 => 7
  | 9 => 20
  | 10 => 14
  | 11 => 48
  | 12 => 46
  | 13 => 11
  | 14 => 47
  | 15 => 61
  | 16 => 36
  | 17 => 54
  | 18 => 95
  | 19 => 5
  | 20 => 4
  | 21 => 34
  | 22 => 84
  | 23 => 23
  | 24 => 47
  | 25 => 21
  | 26 => 30
  | 27 => 48
  | 28 => 60
  | 29 => 15
  | 30 => 2
  | 31 => 73
  | 32 => 74
  | 33 => 70
  | 34 => 42
  | 35 => 11
  | 36 => 82
  | 37 => 93
  | 38 => 9
  | 39 => 56
  | 40 => 80
  | 41 => 60
  | 42 => 5
  | 43 => 92
  | 44 => 58
  | 45 => 0
  | 46 => 17
  | 47 => 97
  | _ => 0

def fixedLiteralModZeroRow_43 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 76
  | 1 => 20
  | 2 => 55
  | 3 => 54
  | 4 => 31
  | 5 => 79
  | 6 => 22
  | 7 => 58
  | 8 => 70
  | 9 => 81
  | 10 => 92
  | 11 => 5
  | 12 => 8
  | 13 => 46
  | 14 => 68
  | 15 => 11
  | 16 => 75
  | 17 => 77
  | 18 => 3
  | 19 => 97
  | 20 => 4
  | 21 => 23
  | 22 => 92
  | 23 => 79
  | 24 => 17
  | 25 => 45
  | 26 => 95
  | 27 => 4
  | 28 => 27
  | 29 => 0
  | 30 => 67
  | 31 => 69
  | 32 => 36
  | 33 => 57
  | 34 => 85
  | 35 => 67
  | 36 => 20
  | 37 => 24
  | 38 => 59
  | 39 => 35
  | 40 => 96
  | 41 => 92
  | 42 => 95
  | 43 => 73
  | 44 => 75
  | 45 => 56
  | 46 => 54
  | 47 => 59
  | _ => 0

def fixedLiteralModZeroRow_44 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 53
  | 1 => 87
  | 2 => 11
  | 3 => 91
  | 4 => 8
  | 5 => 56
  | 6 => 3
  | 7 => 79
  | 8 => 97
  | 9 => 14
  | 10 => 27
  | 11 => 23
  | 12 => 18
  | 13 => 42
  | 14 => 75
  | 15 => 62
  | 16 => 85
  | 17 => 64
  | 18 => 24
  | 19 => 2
  | 20 => 38
  | 21 => 15
  | 22 => 45
  | 23 => 15
  | 24 => 24
  | 25 => 27
  | 26 => 62
  | 27 => 87
  | 28 => 74
  | 29 => 79
  | 30 => 19
  | 31 => 6
  | 32 => 99
  | 33 => 29
  | 34 => 88
  | 35 => 77
  | 36 => 9
  | 37 => 43
  | 38 => 57
  | 39 => 71
  | 40 => 20
  | 41 => 12
  | 42 => 4
  | 43 => 62
  | 44 => 36
  | 45 => 65
  | 46 => 53
  | 47 => 33
  | _ => 0

def fixedLiteralModZeroRow_45 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 17
  | 1 => 92
  | 2 => 55
  | 3 => 15
  | 4 => 48
  | 5 => 76
  | 6 => 36
  | 7 => 57
  | 8 => 25
  | 9 => 0
  | 10 => 7
  | 11 => 11
  | 12 => 77
  | 13 => 24
  | 14 => 38
  | 15 => 77
  | 16 => 65
  | 17 => 68
  | 18 => 65
  | 19 => 62
  | 20 => 55
  | 21 => 61
  | 22 => 22
  | 23 => 41
  | 24 => 99
  | 25 => 48
  | 26 => 76
  | 27 => 87
  | 28 => 18
  | 29 => 25
  | 30 => 61
  | 31 => 53
  | 32 => 74
  | 33 => 53
  | 34 => 98
  | 35 => 7
  | 36 => 32
  | 37 => 10
  | 38 => 11
  | 39 => 47
  | 40 => 32
  | 41 => 14
  | 42 => 88
  | 43 => 71
  | 44 => 34
  | 45 => 84
  | 46 => 57
  | 47 => 7
  | _ => 0

def fixedLiteralModZeroRow_46 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 65
  | 1 => 29
  | 2 => 95
  | 3 => 22
  | 4 => 61
  | 5 => 100
  | 6 => 37
  | 7 => 60
  | 8 => 96
  | 9 => 22
  | 10 => 12
  | 11 => 96
  | 12 => 57
  | 13 => 96
  | 14 => 98
  | 15 => 76
  | 16 => 72
  | 17 => 59
  | 18 => 10
  | 19 => 26
  | 20 => 59
  | 21 => 69
  | 22 => 83
  | 23 => 6
  | 24 => 29
  | 25 => 96
  | 26 => 31
  | 27 => 26
  | 28 => 56
  | 29 => 96
  | 30 => 88
  | 31 => 9
  | 32 => 98
  | 33 => 1
  | 34 => 2
  | 35 => 85
  | 36 => 2
  | 37 => 41
  | 38 => 12
  | 39 => 16
  | 40 => 89
  | 41 => 83
  | 42 => 14
  | 43 => 31
  | 44 => 70
  | 45 => 58
  | 46 => 65
  | 47 => 83
  | _ => 0

def fixedLiteralModZeroRow_47 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 59
  | 1 => 78
  | 2 => 5
  | 3 => 84
  | 4 => 92
  | 5 => 21
  | 6 => 95
  | 7 => 74
  | 8 => 49
  | 9 => 18
  | 10 => 61
  | 11 => 85
  | 12 => 25
  | 13 => 100
  | 14 => 17
  | 15 => 74
  | 16 => 84
  | 17 => 9
  | 18 => 85
  | 19 => 60
  | 20 => 99
  | 21 => 39
  | 22 => 5
  | 23 => 1
  | 24 => 68
  | 25 => 77
  | 26 => 44
  | 27 => 4
  | 28 => 42
  | 29 => 8
  | 30 => 21
  | 31 => 14
  | 32 => 96
  | 33 => 33
  | 34 => 88
  | 35 => 7
  | 36 => 80
  | 37 => 43
  | 38 => 37
  | 39 => 88
  | 40 => 66
  | 41 => 82
  | 42 => 17
  | 43 => 53
  | 44 => 53
  | 45 => 16
  | 46 => 99
  | 47 => 89
  | _ => 0

end InternalCatalan

end

section

namespace InternalCatalan

def fixedLiteralModZero : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  fun r => match r.val with
  | 0 => fixedLiteralModZeroRow_0
  | 1 => fixedLiteralModZeroRow_1
  | 2 => fixedLiteralModZeroRow_2
  | 3 => fixedLiteralModZeroRow_3
  | 4 => fixedLiteralModZeroRow_4
  | 5 => fixedLiteralModZeroRow_5
  | 6 => fixedLiteralModZeroRow_6
  | 7 => fixedLiteralModZeroRow_7
  | 8 => fixedLiteralModZeroRow_8
  | 9 => fixedLiteralModZeroRow_9
  | 10 => fixedLiteralModZeroRow_10
  | 11 => fixedLiteralModZeroRow_11
  | 12 => fixedLiteralModZeroRow_12
  | 13 => fixedLiteralModZeroRow_13
  | 14 => fixedLiteralModZeroRow_14
  | 15 => fixedLiteralModZeroRow_15
  | 16 => fixedLiteralModZeroRow_16
  | 17 => fixedLiteralModZeroRow_17
  | 18 => fixedLiteralModZeroRow_18
  | 19 => fixedLiteralModZeroRow_19
  | 20 => fixedLiteralModZeroRow_20
  | 21 => fixedLiteralModZeroRow_21
  | 22 => fixedLiteralModZeroRow_22
  | 23 => fixedLiteralModZeroRow_23
  | 24 => fixedLiteralModZeroRow_24
  | 25 => fixedLiteralModZeroRow_25
  | 26 => fixedLiteralModZeroRow_26
  | 27 => fixedLiteralModZeroRow_27
  | 28 => fixedLiteralModZeroRow_28
  | 29 => fixedLiteralModZeroRow_29
  | 30 => fixedLiteralModZeroRow_30
  | 31 => fixedLiteralModZeroRow_31
  | 32 => fixedLiteralModZeroRow_32
  | 33 => fixedLiteralModZeroRow_33
  | 34 => fixedLiteralModZeroRow_34
  | 35 => fixedLiteralModZeroRow_35
  | 36 => fixedLiteralModZeroRow_36
  | 37 => fixedLiteralModZeroRow_37
  | 38 => fixedLiteralModZeroRow_38
  | 39 => fixedLiteralModZeroRow_39
  | 40 => fixedLiteralModZeroRow_40
  | 41 => fixedLiteralModZeroRow_41
  | 42 => fixedLiteralModZeroRow_42
  | 43 => fixedLiteralModZeroRow_43
  | 44 => fixedLiteralModZeroRow_44
  | 45 => fixedLiteralModZeroRow_45
  | 46 => fixedLiteralModZeroRow_46
  | 47 => fixedLiteralModZeroRow_47
  | _ => fun _ => 0

def fixedLiteralInvZero : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  fun r => match r.val with
  | 0 => fixedLiteralInvZeroRow_0
  | 1 => fixedLiteralInvZeroRow_1
  | 2 => fixedLiteralInvZeroRow_2
  | 3 => fixedLiteralInvZeroRow_3
  | 4 => fixedLiteralInvZeroRow_4
  | 5 => fixedLiteralInvZeroRow_5
  | 6 => fixedLiteralInvZeroRow_6
  | 7 => fixedLiteralInvZeroRow_7
  | 8 => fixedLiteralInvZeroRow_8
  | 9 => fixedLiteralInvZeroRow_9
  | 10 => fixedLiteralInvZeroRow_10
  | 11 => fixedLiteralInvZeroRow_11
  | 12 => fixedLiteralInvZeroRow_12
  | 13 => fixedLiteralInvZeroRow_13
  | 14 => fixedLiteralInvZeroRow_14
  | 15 => fixedLiteralInvZeroRow_15
  | 16 => fixedLiteralInvZeroRow_16
  | 17 => fixedLiteralInvZeroRow_17
  | 18 => fixedLiteralInvZeroRow_18
  | 19 => fixedLiteralInvZeroRow_19
  | 20 => fixedLiteralInvZeroRow_20
  | 21 => fixedLiteralInvZeroRow_21
  | 22 => fixedLiteralInvZeroRow_22
  | 23 => fixedLiteralInvZeroRow_23
  | 24 => fixedLiteralInvZeroRow_24
  | 25 => fixedLiteralInvZeroRow_25
  | 26 => fixedLiteralInvZeroRow_26
  | 27 => fixedLiteralInvZeroRow_27
  | 28 => fixedLiteralInvZeroRow_28
  | 29 => fixedLiteralInvZeroRow_29
  | 30 => fixedLiteralInvZeroRow_30
  | 31 => fixedLiteralInvZeroRow_31
  | 32 => fixedLiteralInvZeroRow_32
  | 33 => fixedLiteralInvZeroRow_33
  | 34 => fixedLiteralInvZeroRow_34
  | 35 => fixedLiteralInvZeroRow_35
  | 36 => fixedLiteralInvZeroRow_36
  | 37 => fixedLiteralInvZeroRow_37
  | 38 => fixedLiteralInvZeroRow_38
  | 39 => fixedLiteralInvZeroRow_39
  | 40 => fixedLiteralInvZeroRow_40
  | 41 => fixedLiteralInvZeroRow_41
  | 42 => fixedLiteralInvZeroRow_42
  | 43 => fixedLiteralInvZeroRow_43
  | 44 => fixedLiteralInvZeroRow_44
  | 45 => fixedLiteralInvZeroRow_45
  | 46 => fixedLiteralInvZeroRow_46
  | 47 => fixedLiteralInvZeroRow_47
  | _ => fun _ => 0

end InternalCatalan

end

section

namespace InternalCatalan

def fixedLiteralBaseMod (r : Fin 49) (k : Fin 48) : ZMod 101 :=
  match r.val with
  | 0 => fixedLiteralModZeroRow_0 k
  | 1 => fixedLiteralModZeroRow_1 k
  | 2 => fixedLiteralModZeroRow_2 k
  | 3 => fixedLiteralModZeroRow_3 k
  | 4 => fixedLiteralModZeroRow_4 k
  | 5 => fixedLiteralModZeroRow_5 k
  | 6 => fixedLiteralModZeroRow_6 k
  | 7 => fixedLiteralModZeroRow_7 k
  | 8 => fixedLiteralModZeroRow_8 k
  | 9 => fixedLiteralModZeroRow_9 k
  | 10 => fixedLiteralModZeroRow_10 k
  | 11 => fixedLiteralModZeroRow_11 k
  | 12 => fixedLiteralModZeroRow_12 k
  | 13 => fixedLiteralModZeroRow_13 k
  | 14 => fixedLiteralModZeroRow_14 k
  | 15 => fixedLiteralModZeroRow_15 k
  | 16 => fixedLiteralModZeroRow_16 k
  | 17 => fixedLiteralModZeroRow_17 k
  | 18 => fixedLiteralModZeroRow_18 k
  | 19 => fixedLiteralModZeroRow_19 k
  | 20 => fixedLiteralModZeroRow_20 k
  | 21 => fixedLiteralModZeroRow_21 k
  | 22 => fixedLiteralModZeroRow_22 k
  | 23 => fixedLiteralModZeroRow_23 k
  | 24 => fixedLiteralModZeroRow_24 k
  | 25 => fixedLiteralModZeroRow_25 k
  | 26 => fixedLiteralModZeroRow_26 k
  | 27 => fixedLiteralModZeroRow_27 k
  | 28 => fixedLiteralModZeroRow_28 k
  | 29 => fixedLiteralModZeroRow_29 k
  | 30 => fixedLiteralModZeroRow_30 k
  | 31 => fixedLiteralModZeroRow_31 k
  | 32 => fixedLiteralModZeroRow_32 k
  | 33 => fixedLiteralModZeroRow_33 k
  | 34 => fixedLiteralModZeroRow_34 k
  | 35 => fixedLiteralModZeroRow_35 k
  | 36 => fixedLiteralModZeroRow_36 k
  | 37 => fixedLiteralModZeroRow_37 k
  | 38 => fixedLiteralModZeroRow_38 k
  | 39 => fixedLiteralModZeroRow_39 k
  | 40 => fixedLiteralModZeroRow_40 k
  | 41 => fixedLiteralModZeroRow_41 k
  | 42 => fixedLiteralModZeroRow_42 k
  | 43 => fixedLiteralModZeroRow_43 k
  | 44 => fixedLiteralModZeroRow_44 k
  | 45 => fixedLiteralModZeroRow_45 k
  | 46 => fixedLiteralModZeroRow_46 k
  | 47 => fixedLiteralModZeroRow_47 k
  | _ => fixedLiteralModPlusRow_47 k - fixedLiteralModZeroRow_47 k

theorem fixedLiteralBaseMod_zero (r k : Fin 48) :
    fixedLiteralBaseMod r.castSucc k = fixedLiteralModZero r k := by
  fin_cases r <;> rfl

theorem fixedLiteralBaseMod_auxiliary (k : Fin 48) :
    fixedLiteralBaseMod 48 k = fixedLiteralModPlusRow_47 k - fixedLiteralModZeroRow_47 k := by
  rfl

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_0 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 0 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 0 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_1 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 1 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 1 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_10 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 10 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 10 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_11 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 11 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 11 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_12 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 12 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 12 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_13 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 13 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 13 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_14 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 14 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 14 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_15 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 15 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 15 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_16 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 16 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 16 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_17 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 17 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 17 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_18 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 18 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 18 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_19 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 19 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 19 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_20 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 20 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 20 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_21 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 21 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 21 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_22 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 22 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 22 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_23 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 23 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 23 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_24 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 24 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 24 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_25 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 25 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 25 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_26 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 26 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 26 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_27 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 27 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 27 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_28 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 28 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 28 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_29 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 29 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 29 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_2 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 2 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 2 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_3 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 3 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 3 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_30 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 30 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 30 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_31 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 31 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 31 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_32 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 32 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 32 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_33 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 33 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 33 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_34 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 34 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 34 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_35 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 35 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 35 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_36 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 36 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 36 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_37 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 37 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 37 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_38 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 38 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 38 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_39 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 39 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 39 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralBaseMod_plus_row_0 : ∀ k : Fin 48,
    fixedLiteralBaseMod (0 : Fin 48).castSucc k +
      fixedLiteralBaseMod (0 : Fin 48).succ k = fixedLiteralModPlus 0 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_0 : ∀ k : Fin 48,
    fixedLiteralBaseMod (0 : Fin 48).castSucc k -
      fixedLiteralBaseMod (0 : Fin 48).succ k = fixedLiteralModMinus 0 k := by
  decide +kernel

theorem fixedLiteralBaseMod_plus_row_1 : ∀ k : Fin 48,
    fixedLiteralBaseMod (1 : Fin 48).castSucc k +
      fixedLiteralBaseMod (1 : Fin 48).succ k = fixedLiteralModPlus 1 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_1 : ∀ k : Fin 48,
    fixedLiteralBaseMod (1 : Fin 48).castSucc k -
      fixedLiteralBaseMod (1 : Fin 48).succ k = fixedLiteralModMinus 1 k := by
  decide +kernel

end InternalCatalan

end

end OAI
