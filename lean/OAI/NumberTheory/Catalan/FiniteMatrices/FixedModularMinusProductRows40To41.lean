import Mathlib.Tactic.FinCases
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularMinusInvRows36To47
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularMinusModRows24To35

namespace OAI

section

namespace InternalCatalan

def fixedLiteralModMinusRow_36 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 94
  | 1 => 38
  | 2 => 99
  | 3 => 83
  | 4 => 53
  | 5 => 56
  | 6 => 32
  | 7 => 48
  | 8 => 9
  | 9 => 2
  | 10 => 38
  | 11 => 36
  | 12 => 68
  | 13 => 95
  | 14 => 12
  | 15 => 68
  | 16 => 17
  | 17 => 64
  | 18 => 82
  | 19 => 22
  | 20 => 83
  | 21 => 77
  | 22 => 15
  | 23 => 22
  | 24 => 8
  | 25 => 82
  | 26 => 80
  | 27 => 52
  | 28 => 18
  | 29 => 28
  | 30 => 95
  | 31 => 98
  | 32 => 38
  | 33 => 20
  | 34 => 62
  | 35 => 30
  | 36 => 28
  | 37 => 100
  | 38 => 60
  | 39 => 87
  | 40 => 9
  | 41 => 95
  | 42 => 94
  | 43 => 1
  | 44 => 18
  | 45 => 98
  | 46 => 24
  | 47 => 75
  | _ => 0

def fixedLiteralModMinusRow_37 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 58
  | 1 => 53
  | 2 => 33
  | 3 => 35
  | 4 => 94
  | 5 => 76
  | 6 => 28
  | 7 => 8
  | 8 => 47
  | 9 => 22
  | 10 => 14
  | 11 => 88
  | 12 => 78
  | 13 => 29
  | 14 => 6
  | 15 => 6
  | 16 => 77
  | 17 => 73
  | 18 => 16
  | 19 => 55
  | 20 => 33
  | 21 => 22
  | 22 => 74
  | 23 => 87
  | 24 => 100
  | 25 => 17
  | 26 => 10
  | 27 => 25
  | 28 => 98
  | 29 => 18
  | 30 => 44
  | 31 => 99
  | 32 => 84
  | 33 => 1
  | 34 => 43
  | 35 => 58
  | 36 => 4
  | 37 => 67
  | 38 => 39
  | 39 => 83
  | 40 => 76
  | 41 => 95
  | 42 => 61
  | 43 => 18
  | 44 => 17
  | 45 => 7
  | 46 => 3
  | 47 => 73
  | _ => 0

def fixedLiteralModMinusRow_38 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 34
  | 1 => 26
  | 2 => 13
  | 3 => 32
  | 4 => 93
  | 5 => 73
  | 6 => 76
  | 7 => 50
  | 8 => 38
  | 9 => 86
  | 10 => 65
  | 11 => 98
  | 12 => 82
  | 13 => 31
  | 14 => 61
  | 15 => 16
  | 16 => 21
  | 17 => 4
  | 18 => 58
  | 19 => 4
  | 20 => 3
  | 21 => 24
  | 22 => 9
  | 23 => 35
  | 24 => 74
  | 25 => 15
  | 26 => 98
  | 27 => 51
  | 28 => 25
  | 29 => 76
  | 30 => 69
  | 31 => 47
  | 32 => 1
  | 33 => 54
  | 34 => 96
  | 35 => 80
  | 36 => 8
  | 37 => 92
  | 38 => 47
  | 39 => 91
  | 40 => 53
  | 41 => 54
  | 42 => 17
  | 43 => 92
  | 44 => 84
  | 45 => 6
  | 46 => 20
  | 47 => 55
  | _ => 0

def fixedLiteralModMinusRow_39 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 32
  | 1 => 43
  | 2 => 76
  | 3 => 80
  | 4 => 60
  | 5 => 46
  | 6 => 84
  | 7 => 29
  | 8 => 20
  | 9 => 28
  | 10 => 10
  | 11 => 38
  | 12 => 97
  | 13 => 42
  | 14 => 12
  | 15 => 62
  | 16 => 75
  | 17 => 96
  | 18 => 53
  | 19 => 38
  | 20 => 60
  | 21 => 25
  | 22 => 95
  | 23 => 16
  | 24 => 68
  | 25 => 9
  | 26 => 56
  | 27 => 48
  | 28 => 11
  | 29 => 65
  | 30 => 28
  | 31 => 1
  | 32 => 42
  | 33 => 5
  | 34 => 61
  | 35 => 24
  | 36 => 75
  | 37 => 77
  | 38 => 87
  | 39 => 22
  | 40 => 68
  | 41 => 4
  | 42 => 23
  | 43 => 4
  | 44 => 46
  | 45 => 37
  | 46 => 41
  | 47 => 36
  | _ => 0

def fixedLiteralModMinusRow_40 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 50
  | 1 => 16
  | 2 => 33
  | 3 => 12
  | 4 => 73
  | 5 => 70
  | 6 => 93
  | 7 => 8
  | 8 => 82
  | 9 => 2
  | 10 => 36
  | 11 => 98
  | 12 => 12
  | 13 => 1
  | 14 => 85
  | 15 => 21
  | 16 => 89
  | 17 => 62
  | 18 => 52
  | 19 => 37
  | 20 => 34
  | 21 => 5
  | 22 => 55
  | 23 => 13
  | 24 => 59
  | 25 => 90
  | 26 => 69
  | 27 => 7
  | 28 => 86
  | 29 => 52
  | 30 => 83
  | 31 => 85
  | 32 => 24
  | 33 => 14
  | 34 => 40
  | 35 => 24
  | 36 => 8
  | 37 => 90
  | 38 => 85
  | 39 => 61
  | 40 => 86
  | 41 => 63
  | 42 => 76
  | 43 => 13
  | 44 => 83
  | 45 => 12
  | 46 => 98
  | 47 => 28
  | _ => 0

def fixedLiteralModMinusRow_41 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 11
  | 1 => 22
  | 2 => 70
  | 3 => 80
  | 4 => 77
  | 5 => 25
  | 6 => 79
  | 7 => 36
  | 8 => 36
  | 9 => 74
  | 10 => 99
  | 11 => 76
  | 12 => 52
  | 13 => 84
  | 14 => 10
  | 15 => 81
  | 16 => 96
  | 17 => 26
  | 18 => 36
  | 19 => 10
  | 20 => 72
  | 21 => 11
  | 22 => 58
  | 23 => 81
  | 24 => 35
  | 25 => 16
  | 26 => 22
  | 27 => 27
  | 28 => 46
  | 29 => 8
  | 30 => 24
  | 31 => 86
  | 32 => 55
  | 33 => 69
  | 34 => 8
  | 35 => 43
  | 36 => 56
  | 37 => 49
  | 38 => 56
  | 39 => 62
  | 40 => 95
  | 41 => 10
  | 42 => 91
  | 43 => 40
  | 44 => 22
  | 45 => 6
  | 46 => 65
  | 47 => 9
  | _ => 0

def fixedLiteralModMinusRow_42 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 58
  | 1 => 8
  | 2 => 38
  | 3 => 49
  | 4 => 33
  | 5 => 80
  | 6 => 63
  | 7 => 94
  | 8 => 38
  | 9 => 40
  | 10 => 23
  | 11 => 43
  | 12 => 38
  | 13 => 66
  | 14 => 80
  | 15 => 50
  | 16 => 62
  | 17 => 78
  | 18 => 92
  | 19 => 9
  | 20 => 0
  | 21 => 11
  | 22 => 93
  | 23 => 45
  | 24 => 30
  | 25 => 77
  | 26 => 36
  | 27 => 44
  | 28 => 33
  | 29 => 15
  | 30 => 36
  | 31 => 4
  | 32 => 38
  | 33 => 13
  | 34 => 58
  | 35 => 45
  | 36 => 62
  | 37 => 69
  | 38 => 51
  | 39 => 21
  | 40 => 85
  | 41 => 69
  | 42 => 11
  | 43 => 19
  | 44 => 84
  | 45 => 45
  | 46 => 64
  | 47 => 38
  | _ => 0

def fixedLiteralModMinusRow_43 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 23
  | 1 => 34
  | 2 => 44
  | 3 => 64
  | 4 => 23
  | 5 => 23
  | 6 => 19
  | 7 => 80
  | 8 => 74
  | 9 => 67
  | 10 => 65
  | 11 => 83
  | 12 => 91
  | 13 => 4
  | 14 => 94
  | 15 => 50
  | 16 => 91
  | 17 => 13
  | 18 => 80
  | 19 => 95
  | 20 => 67
  | 21 => 8
  | 22 => 47
  | 23 => 64
  | 24 => 94
  | 25 => 18
  | 26 => 33
  | 27 => 18
  | 28 => 54
  | 29 => 22
  | 30 => 48
  | 31 => 63
  | 32 => 38
  | 33 => 28
  | 34 => 98
  | 35 => 91
  | 36 => 11
  | 37 => 82
  | 38 => 2
  | 39 => 65
  | 40 => 76
  | 41 => 80
  | 42 => 91
  | 43 => 11
  | 44 => 39
  | 45 => 92
  | 46 => 1
  | 47 => 26
  | _ => 0

def fixedLiteralModMinusRow_44 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 36
  | 1 => 96
  | 2 => 57
  | 3 => 76
  | 4 => 61
  | 5 => 81
  | 6 => 68
  | 7 => 22
  | 8 => 72
  | 9 => 14
  | 10 => 20
  | 11 => 12
  | 12 => 42
  | 13 => 18
  | 14 => 37
  | 15 => 86
  | 16 => 20
  | 17 => 97
  | 18 => 60
  | 19 => 41
  | 20 => 84
  | 21 => 55
  | 22 => 23
  | 23 => 75
  | 24 => 26
  | 25 => 80
  | 26 => 87
  | 27 => 0
  | 28 => 56
  | 29 => 54
  | 30 => 59
  | 31 => 54
  | 32 => 25
  | 33 => 77
  | 34 => 91
  | 35 => 70
  | 36 => 78
  | 37 => 33
  | 38 => 46
  | 39 => 24
  | 40 => 89
  | 41 => 99
  | 42 => 17
  | 43 => 92
  | 44 => 2
  | 45 => 82
  | 46 => 97
  | 47 => 26
  | _ => 0

def fixedLiteralModMinusRow_45 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 53
  | 1 => 63
  | 2 => 61
  | 3 => 94
  | 4 => 88
  | 5 => 77
  | 6 => 100
  | 7 => 98
  | 8 => 30
  | 9 => 79
  | 10 => 96
  | 11 => 16
  | 12 => 20
  | 13 => 29
  | 14 => 41
  | 15 => 1
  | 16 => 94
  | 17 => 9
  | 18 => 55
  | 19 => 36
  | 20 => 97
  | 21 => 93
  | 22 => 40
  | 23 => 35
  | 24 => 70
  | 25 => 53
  | 26 => 45
  | 27 => 61
  | 28 => 63
  | 29 => 30
  | 30 => 74
  | 31 => 44
  | 32 => 77
  | 33 => 52
  | 34 => 96
  | 35 => 23
  | 36 => 30
  | 37 => 70
  | 38 => 100
  | 39 => 31
  | 40 => 44
  | 41 => 32
  | 42 => 74
  | 43 => 40
  | 44 => 65
  | 45 => 26
  | 46 => 93
  | 47 => 25
  | _ => 0

def fixedLiteralModMinusRow_46 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 6
  | 1 => 52
  | 2 => 90
  | 3 => 39
  | 4 => 70
  | 5 => 79
  | 6 => 43
  | 7 => 87
  | 8 => 47
  | 9 => 4
  | 10 => 52
  | 11 => 11
  | 12 => 32
  | 13 => 97
  | 14 => 81
  | 15 => 2
  | 16 => 89
  | 17 => 50
  | 18 => 26
  | 19 => 67
  | 20 => 61
  | 21 => 30
  | 22 => 78
  | 23 => 5
  | 24 => 62
  | 25 => 19
  | 26 => 88
  | 27 => 22
  | 28 => 14
  | 29 => 88
  | 30 => 67
  | 31 => 96
  | 32 => 2
  | 33 => 69
  | 34 => 15
  | 35 => 78
  | 36 => 23
  | 37 => 99
  | 38 => 76
  | 39 => 29
  | 40 => 23
  | 41 => 1
  | 42 => 98
  | 43 => 79
  | 44 => 17
  | 45 => 42
  | 46 => 67
  | 47 => 95
  | _ => 0

def fixedLiteralModMinusRow_47 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 11
  | 1 => 38
  | 2 => 60
  | 3 => 41
  | 4 => 35
  | 5 => 14
  | 6 => 72
  | 7 => 53
  | 8 => 46
  | 9 => 72
  | 10 => 22
  | 11 => 88
  | 12 => 71
  | 13 => 91
  | 14 => 100
  | 15 => 38
  | 16 => 83
  | 17 => 51
  | 18 => 52
  | 19 => 21
  | 20 => 6
  | 21 => 75
  | 22 => 4
  | 23 => 46
  | 24 => 46
  | 25 => 84
  | 26 => 5
  | 27 => 81
  | 28 => 36
  | 29 => 29
  | 30 => 88
  | 31 => 11
  | 32 => 58
  | 33 => 9
  | 34 => 2
  | 35 => 12
  | 36 => 34
  | 37 => 40
  | 38 => 1
  | 39 => 32
  | 40 => 53
  | 41 => 69
  | 42 => 67
  | 43 => 52
  | 44 => 61
  | 45 => 40
  | 46 => 7
  | 47 => 63
  | _ => 0

end InternalCatalan

end

section

namespace InternalCatalan

def fixedLiteralModMinus : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  fun r => match r.val with
  | 0 => fixedLiteralModMinusRow_0
  | 1 => fixedLiteralModMinusRow_1
  | 2 => fixedLiteralModMinusRow_2
  | 3 => fixedLiteralModMinusRow_3
  | 4 => fixedLiteralModMinusRow_4
  | 5 => fixedLiteralModMinusRow_5
  | 6 => fixedLiteralModMinusRow_6
  | 7 => fixedLiteralModMinusRow_7
  | 8 => fixedLiteralModMinusRow_8
  | 9 => fixedLiteralModMinusRow_9
  | 10 => fixedLiteralModMinusRow_10
  | 11 => fixedLiteralModMinusRow_11
  | 12 => fixedLiteralModMinusRow_12
  | 13 => fixedLiteralModMinusRow_13
  | 14 => fixedLiteralModMinusRow_14
  | 15 => fixedLiteralModMinusRow_15
  | 16 => fixedLiteralModMinusRow_16
  | 17 => fixedLiteralModMinusRow_17
  | 18 => fixedLiteralModMinusRow_18
  | 19 => fixedLiteralModMinusRow_19
  | 20 => fixedLiteralModMinusRow_20
  | 21 => fixedLiteralModMinusRow_21
  | 22 => fixedLiteralModMinusRow_22
  | 23 => fixedLiteralModMinusRow_23
  | 24 => fixedLiteralModMinusRow_24
  | 25 => fixedLiteralModMinusRow_25
  | 26 => fixedLiteralModMinusRow_26
  | 27 => fixedLiteralModMinusRow_27
  | 28 => fixedLiteralModMinusRow_28
  | 29 => fixedLiteralModMinusRow_29
  | 30 => fixedLiteralModMinusRow_30
  | 31 => fixedLiteralModMinusRow_31
  | 32 => fixedLiteralModMinusRow_32
  | 33 => fixedLiteralModMinusRow_33
  | 34 => fixedLiteralModMinusRow_34
  | 35 => fixedLiteralModMinusRow_35
  | 36 => fixedLiteralModMinusRow_36
  | 37 => fixedLiteralModMinusRow_37
  | 38 => fixedLiteralModMinusRow_38
  | 39 => fixedLiteralModMinusRow_39
  | 40 => fixedLiteralModMinusRow_40
  | 41 => fixedLiteralModMinusRow_41
  | 42 => fixedLiteralModMinusRow_42
  | 43 => fixedLiteralModMinusRow_43
  | 44 => fixedLiteralModMinusRow_44
  | 45 => fixedLiteralModMinusRow_45
  | 46 => fixedLiteralModMinusRow_46
  | 47 => fixedLiteralModMinusRow_47
  | _ => fun _ => 0

def fixedLiteralInvMinus : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  fun r => match r.val with
  | 0 => fixedLiteralInvMinusRow_0
  | 1 => fixedLiteralInvMinusRow_1
  | 2 => fixedLiteralInvMinusRow_2
  | 3 => fixedLiteralInvMinusRow_3
  | 4 => fixedLiteralInvMinusRow_4
  | 5 => fixedLiteralInvMinusRow_5
  | 6 => fixedLiteralInvMinusRow_6
  | 7 => fixedLiteralInvMinusRow_7
  | 8 => fixedLiteralInvMinusRow_8
  | 9 => fixedLiteralInvMinusRow_9
  | 10 => fixedLiteralInvMinusRow_10
  | 11 => fixedLiteralInvMinusRow_11
  | 12 => fixedLiteralInvMinusRow_12
  | 13 => fixedLiteralInvMinusRow_13
  | 14 => fixedLiteralInvMinusRow_14
  | 15 => fixedLiteralInvMinusRow_15
  | 16 => fixedLiteralInvMinusRow_16
  | 17 => fixedLiteralInvMinusRow_17
  | 18 => fixedLiteralInvMinusRow_18
  | 19 => fixedLiteralInvMinusRow_19
  | 20 => fixedLiteralInvMinusRow_20
  | 21 => fixedLiteralInvMinusRow_21
  | 22 => fixedLiteralInvMinusRow_22
  | 23 => fixedLiteralInvMinusRow_23
  | 24 => fixedLiteralInvMinusRow_24
  | 25 => fixedLiteralInvMinusRow_25
  | 26 => fixedLiteralInvMinusRow_26
  | 27 => fixedLiteralInvMinusRow_27
  | 28 => fixedLiteralInvMinusRow_28
  | 29 => fixedLiteralInvMinusRow_29
  | 30 => fixedLiteralInvMinusRow_30
  | 31 => fixedLiteralInvMinusRow_31
  | 32 => fixedLiteralInvMinusRow_32
  | 33 => fixedLiteralInvMinusRow_33
  | 34 => fixedLiteralInvMinusRow_34
  | 35 => fixedLiteralInvMinusRow_35
  | 36 => fixedLiteralInvMinusRow_36
  | 37 => fixedLiteralInvMinusRow_37
  | 38 => fixedLiteralInvMinusRow_38
  | 39 => fixedLiteralInvMinusRow_39
  | 40 => fixedLiteralInvMinusRow_40
  | 41 => fixedLiteralInvMinusRow_41
  | 42 => fixedLiteralInvMinusRow_42
  | 43 => fixedLiteralInvMinusRow_43
  | 44 => fixedLiteralInvMinusRow_44
  | 45 => fixedLiteralInvMinusRow_45
  | 46 => fixedLiteralInvMinusRow_46
  | 47 => fixedLiteralInvMinusRow_47
  | _ => fun _ => 0

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_0 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 0 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 0 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_1 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 1 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 1 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_10 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 10 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 10 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_11 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 11 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 11 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_12 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 12 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 12 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_13 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 13 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 13 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_14 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 14 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 14 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_15 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 15 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 15 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_16 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 16 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 16 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_17 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 17 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 17 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_18 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 18 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 18 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_19 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 19 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 19 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_20 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 20 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 20 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_21 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 21 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 21 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_22 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 22 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 22 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_23 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 23 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 23 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_24 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 24 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 24 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_25 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 25 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 25 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_26 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 26 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 26 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_27 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 27 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 27 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_28 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 28 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 28 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_29 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 29 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 29 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_2 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 2 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 2 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_3 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 3 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 3 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_30 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 30 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 30 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_31 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 31 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 31 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_32 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 32 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 32 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_33 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 33 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 33 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_34 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 34 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 34 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_35 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 35 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 35 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_36 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 36 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 36 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_37 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 37 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 37 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_38 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 38 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 38 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_39 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 39 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 39 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_40 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 40 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 40 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_41 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 41 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 41 k := by
  decide +kernel

end InternalCatalan

end

end OAI
