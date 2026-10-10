import Mathlib.Tactic.FinCases
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularPlusInvRows36To47
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularPlusModRows24To35

namespace OAI

section

namespace InternalCatalan

def fixedLiteralModPlusRow_36 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 25
  | 1 => 10
  | 2 => 28
  | 3 => 60
  | 4 => 66
  | 5 => 45
  | 6 => 13
  | 7 => 8
  | 8 => 65
  | 9 => 62
  | 10 => 9
  | 11 => 19
  | 12 => 95
  | 13 => 87
  | 14 => 50
  | 15 => 57
  | 16 => 98
  | 17 => 88
  | 18 => 96
  | 19 => 17
  | 20 => 91
  | 21 => 16
  | 22 => 58
  | 23 => 27
  | 24 => 67
  | 25 => 14
  | 26 => 44
  | 27 => 60
  | 28 => 64
  | 29 => 92
  | 30 => 90
  | 31 => 72
  | 32 => 93
  | 33 => 42
  | 34 => 36
  | 35 => 5
  | 36 => 90
  | 37 => 26
  | 38 => 100
  | 39 => 29
  | 40 => 16
  | 41 => 61
  | 42 => 34
  | 43 => 14
  | 44 => 32
  | 45 => 32
  | 46 => 7
  | 47 => 65
  | _ => 0

def fixedLiteralModPlusRow_37 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 75
  | 1 => 20
  | 2 => 98
  | 3 => 43
  | 4 => 20
  | 5 => 14
  | 6 => 54
  | 7 => 53
  | 8 => 9
  | 9 => 38
  | 10 => 58
  | 11 => 97
  | 12 => 50
  | 13 => 64
  | 14 => 32
  | 15 => 84
  | 16 => 4
  | 17 => 52
  | 18 => 99
  | 19 => 41
  | 20 => 76
  | 21 => 18
  | 22 => 70
  | 23 => 19
  | 24 => 60
  | 25 => 16
  | 26 => 55
  | 27 => 84
  | 28 => 49
  | 29 => 46
  | 30 => 52
  | 31 => 77
  | 32 => 72
  | 33 => 21
  | 34 => 32
  | 35 => 18
  | 36 => 58
  | 37 => 61
  | 38 => 1
  | 39 => 61
  | 40 => 32
  | 41 => 73
  | 42 => 81
  | 43 => 96
  | 44 => 98
  | 45 => 28
  | 46 => 81
  | 47 => 18
  | _ => 0

def fixedLiteralModPlusRow_38 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 84
  | 1 => 42
  | 2 => 52
  | 3 => 77
  | 4 => 35
  | 5 => 67
  | 6 => 51
  | 7 => 96
  | 8 => 25
  | 9 => 31
  | 10 => 80
  | 11 => 12
  | 12 => 92
  | 13 => 4
  | 14 => 66
  | 15 => 62
  | 16 => 7
  | 17 => 76
  | 18 => 25
  | 19 => 83
  | 20 => 40
  | 21 => 73
  | 22 => 88
  | 23 => 99
  | 24 => 88
  | 25 => 85
  | 26 => 48
  | 27 => 8
  | 28 => 27
  | 29 => 53
  | 30 => 40
  | 31 => 32
  | 32 => 88
  | 33 => 67
  | 34 => 95
  | 35 => 82
  | 36 => 46
  | 37 => 3
  | 38 => 16
  | 39 => 89
  | 40 => 4
  | 41 => 25
  | 42 => 3
  | 43 => 87
  | 44 => 98
  | 45 => 15
  | 46 => 58
  | 47 => 92
  | _ => 0

def fixedLiteralModPlusRow_39 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 18
  | 1 => 74
  | 2 => 64
  | 3 => 66
  | 4 => 84
  | 5 => 49
  | 6 => 93
  | 7 => 17
  | 8 => 68
  | 9 => 18
  | 10 => 5
  | 11 => 78
  | 12 => 14
  | 13 => 32
  | 14 => 94
  | 15 => 85
  | 16 => 12
  | 17 => 77
  | 18 => 15
  | 19 => 41
  | 20 => 78
  | 21 => 24
  | 22 => 85
  | 23 => 48
  | 24 => 47
  | 25 => 61
  | 26 => 96
  | 27 => 10
  | 28 => 92
  | 29 => 13
  | 30 => 44
  | 31 => 85
  | 32 => 45
  | 33 => 8
  | 34 => 39
  | 35 => 79
  | 36 => 64
  | 37 => 36
  | 38 => 84
  | 39 => 77
  | 40 => 85
  | 41 => 68
  | 42 => 64
  | 43 => 92
  | 44 => 69
  | 45 => 73
  | 46 => 98
  | 47 => 1
  | _ => 0

def fixedLiteralModPlusRow_40 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 37
  | 1 => 15
  | 2 => 56
  | 3 => 75
  | 4 => 52
  | 5 => 34
  | 6 => 17
  | 7 => 81
  | 8 => 67
  | 9 => 89
  | 10 => 60
  | 11 => 43
  | 12 => 6
  | 13 => 90
  | 14 => 98
  | 15 => 2
  | 16 => 50
  | 17 => 20
  | 18 => 11
  | 19 => 67
  | 20 => 85
  | 21 => 95
  | 22 => 36
  | 23 => 19
  | 24 => 21
  | 25 => 63
  | 26 => 72
  | 27 => 56
  | 28 => 96
  | 29 => 98
  | 30 => 34
  | 31 => 100
  | 32 => 80
  | 33 => 90
  | 34 => 39
  | 35 => 31
  | 36 => 82
  | 37 => 71
  | 38 => 13
  | 39 => 95
  | 40 => 32
  | 41 => 1
  | 42 => 66
  | 43 => 75
  | 44 => 41
  | 45 => 24
  | 46 => 60
  | 47 => 38
  | _ => 0

def fixedLiteralModPlusRow_41 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 77
  | 1 => 78
  | 2 => 54
  | 3 => 84
  | 4 => 3
  | 5 => 40
  | 6 => 47
  | 7 => 37
  | 8 => 50
  | 9 => 13
  | 10 => 26
  | 11 => 71
  | 12 => 43
  | 13 => 5
  | 14 => 3
  | 15 => 1
  | 16 => 67
  | 17 => 33
  | 18 => 24
  | 19 => 20
  | 20 => 80
  | 21 => 79
  | 22 => 24
  | 23 => 26
  | 24 => 28
  | 25 => 58
  | 26 => 82
  | 27 => 22
  | 28 => 65
  | 29 => 38
  | 30 => 28
  | 31 => 30
  | 32 => 1
  | 33 => 7
  | 34 => 92
  | 35 => 65
  | 36 => 18
  | 37 => 33
  | 38 => 74
  | 39 => 73
  | 40 => 53
  | 41 => 29
  | 42 => 0
  | 43 => 22
  | 44 => 37
  | 45 => 6
  | 46 => 99
  | 47 => 1
  | _ => 0

def fixedLiteralModPlusRow_42 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 8
  | 1 => 48
  | 2 => 47
  | 3 => 56
  | 4 => 95
  | 5 => 36
  | 6 => 6
  | 7 => 8
  | 8 => 77
  | 9 => 0
  | 10 => 5
  | 11 => 53
  | 12 => 54
  | 13 => 57
  | 14 => 14
  | 15 => 72
  | 16 => 10
  | 17 => 30
  | 18 => 98
  | 19 => 1
  | 20 => 8
  | 21 => 57
  | 22 => 75
  | 23 => 1
  | 24 => 64
  | 25 => 66
  | 26 => 24
  | 27 => 52
  | 28 => 87
  | 29 => 15
  | 30 => 69
  | 31 => 41
  | 32 => 9
  | 33 => 26
  | 34 => 26
  | 35 => 78
  | 36 => 1
  | 37 => 16
  | 38 => 68
  | 39 => 91
  | 40 => 75
  | 41 => 51
  | 42 => 100
  | 43 => 64
  | 44 => 32
  | 45 => 56
  | 46 => 71
  | 47 => 55
  | _ => 0

def fixedLiteralModPlusRow_43 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 28
  | 1 => 6
  | 2 => 66
  | 3 => 44
  | 4 => 39
  | 5 => 34
  | 6 => 25
  | 7 => 36
  | 8 => 66
  | 9 => 95
  | 10 => 18
  | 11 => 28
  | 12 => 26
  | 13 => 88
  | 14 => 42
  | 15 => 73
  | 16 => 59
  | 17 => 40
  | 18 => 27
  | 19 => 99
  | 20 => 42
  | 21 => 38
  | 22 => 36
  | 23 => 94
  | 24 => 41
  | 25 => 72
  | 26 => 56
  | 27 => 91
  | 28 => 0
  | 29 => 79
  | 30 => 86
  | 31 => 75
  | 32 => 34
  | 33 => 86
  | 34 => 72
  | 35 => 43
  | 36 => 29
  | 37 => 67
  | 38 => 15
  | 39 => 5
  | 40 => 15
  | 41 => 3
  | 42 => 99
  | 43 => 34
  | 44 => 10
  | 45 => 20
  | 46 => 6
  | 47 => 92
  | _ => 0

def fixedLiteralModPlusRow_44 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 70
  | 1 => 78
  | 2 => 66
  | 3 => 5
  | 4 => 56
  | 5 => 31
  | 6 => 39
  | 7 => 35
  | 8 => 21
  | 9 => 14
  | 10 => 34
  | 11 => 34
  | 12 => 95
  | 13 => 66
  | 14 => 12
  | 15 => 38
  | 16 => 49
  | 17 => 31
  | 18 => 89
  | 19 => 64
  | 20 => 93
  | 21 => 76
  | 22 => 67
  | 23 => 56
  | 24 => 22
  | 25 => 75
  | 26 => 37
  | 27 => 73
  | 28 => 92
  | 29 => 3
  | 30 => 80
  | 31 => 59
  | 32 => 72
  | 33 => 82
  | 34 => 85
  | 35 => 84
  | 36 => 41
  | 37 => 53
  | 38 => 68
  | 39 => 17
  | 40 => 52
  | 41 => 26
  | 42 => 92
  | 43 => 32
  | 44 => 70
  | 45 => 48
  | 46 => 9
  | 47 => 40
  | _ => 0

def fixedLiteralModPlusRow_45 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 82
  | 1 => 20
  | 2 => 49
  | 3 => 37
  | 4 => 8
  | 5 => 75
  | 6 => 73
  | 7 => 16
  | 8 => 20
  | 9 => 22
  | 10 => 19
  | 11 => 6
  | 12 => 33
  | 13 => 19
  | 14 => 35
  | 15 => 52
  | 16 => 36
  | 17 => 26
  | 18 => 75
  | 19 => 88
  | 20 => 13
  | 21 => 29
  | 22 => 4
  | 23 => 47
  | 24 => 27
  | 25 => 43
  | 26 => 6
  | 27 => 12
  | 28 => 74
  | 29 => 20
  | 30 => 48
  | 31 => 62
  | 32 => 71
  | 33 => 54
  | 34 => 100
  | 35 => 92
  | 36 => 34
  | 37 => 51
  | 38 => 23
  | 39 => 63
  | 40 => 20
  | 41 => 97
  | 42 => 1
  | 43 => 1
  | 44 => 3
  | 45 => 41
  | 46 => 21
  | 47 => 90
  | _ => 0

def fixedLiteralModPlusRow_46 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 23
  | 1 => 6
  | 2 => 100
  | 3 => 5
  | 4 => 52
  | 5 => 20
  | 6 => 31
  | 7 => 33
  | 8 => 44
  | 9 => 40
  | 10 => 73
  | 11 => 80
  | 12 => 82
  | 13 => 95
  | 14 => 14
  | 15 => 49
  | 16 => 55
  | 17 => 68
  | 18 => 95
  | 19 => 86
  | 20 => 57
  | 21 => 7
  | 22 => 88
  | 23 => 7
  | 24 => 97
  | 25 => 72
  | 26 => 75
  | 27 => 30
  | 28 => 98
  | 29 => 3
  | 30 => 8
  | 31 => 23
  | 32 => 93
  | 33 => 34
  | 34 => 90
  | 35 => 92
  | 36 => 82
  | 37 => 84
  | 38 => 49
  | 39 => 3
  | 40 => 54
  | 41 => 64
  | 42 => 31
  | 43 => 84
  | 44 => 22
  | 45 => 74
  | 46 => 63
  | 47 => 71
  | _ => 0

def fixedLiteralModPlusRow_47 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 6
  | 1 => 17
  | 2 => 51
  | 3 => 26
  | 4 => 48
  | 5 => 28
  | 6 => 17
  | 7 => 95
  | 8 => 52
  | 9 => 65
  | 10 => 100
  | 11 => 82
  | 12 => 80
  | 13 => 8
  | 14 => 35
  | 15 => 9
  | 16 => 85
  | 17 => 68
  | 18 => 17
  | 19 => 99
  | 20 => 91
  | 21 => 3
  | 22 => 6
  | 23 => 57
  | 24 => 90
  | 25 => 70
  | 26 => 83
  | 27 => 28
  | 28 => 48
  | 29 => 88
  | 30 => 55
  | 31 => 17
  | 32 => 33
  | 33 => 57
  | 34 => 73
  | 35 => 2
  | 36 => 25
  | 37 => 46
  | 38 => 73
  | 39 => 43
  | 40 => 79
  | 41 => 95
  | 42 => 68
  | 43 => 54
  | 44 => 45
  | 45 => 93
  | 46 => 90
  | 47 => 14
  | _ => 0

end InternalCatalan

end

section

namespace InternalCatalan

def fixedLiteralModPlus : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  fun r => match r.val with
  | 0 => fixedLiteralModPlusRow_0
  | 1 => fixedLiteralModPlusRow_1
  | 2 => fixedLiteralModPlusRow_2
  | 3 => fixedLiteralModPlusRow_3
  | 4 => fixedLiteralModPlusRow_4
  | 5 => fixedLiteralModPlusRow_5
  | 6 => fixedLiteralModPlusRow_6
  | 7 => fixedLiteralModPlusRow_7
  | 8 => fixedLiteralModPlusRow_8
  | 9 => fixedLiteralModPlusRow_9
  | 10 => fixedLiteralModPlusRow_10
  | 11 => fixedLiteralModPlusRow_11
  | 12 => fixedLiteralModPlusRow_12
  | 13 => fixedLiteralModPlusRow_13
  | 14 => fixedLiteralModPlusRow_14
  | 15 => fixedLiteralModPlusRow_15
  | 16 => fixedLiteralModPlusRow_16
  | 17 => fixedLiteralModPlusRow_17
  | 18 => fixedLiteralModPlusRow_18
  | 19 => fixedLiteralModPlusRow_19
  | 20 => fixedLiteralModPlusRow_20
  | 21 => fixedLiteralModPlusRow_21
  | 22 => fixedLiteralModPlusRow_22
  | 23 => fixedLiteralModPlusRow_23
  | 24 => fixedLiteralModPlusRow_24
  | 25 => fixedLiteralModPlusRow_25
  | 26 => fixedLiteralModPlusRow_26
  | 27 => fixedLiteralModPlusRow_27
  | 28 => fixedLiteralModPlusRow_28
  | 29 => fixedLiteralModPlusRow_29
  | 30 => fixedLiteralModPlusRow_30
  | 31 => fixedLiteralModPlusRow_31
  | 32 => fixedLiteralModPlusRow_32
  | 33 => fixedLiteralModPlusRow_33
  | 34 => fixedLiteralModPlusRow_34
  | 35 => fixedLiteralModPlusRow_35
  | 36 => fixedLiteralModPlusRow_36
  | 37 => fixedLiteralModPlusRow_37
  | 38 => fixedLiteralModPlusRow_38
  | 39 => fixedLiteralModPlusRow_39
  | 40 => fixedLiteralModPlusRow_40
  | 41 => fixedLiteralModPlusRow_41
  | 42 => fixedLiteralModPlusRow_42
  | 43 => fixedLiteralModPlusRow_43
  | 44 => fixedLiteralModPlusRow_44
  | 45 => fixedLiteralModPlusRow_45
  | 46 => fixedLiteralModPlusRow_46
  | 47 => fixedLiteralModPlusRow_47
  | _ => fun _ => 0

def fixedLiteralInvPlus : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  fun r => match r.val with
  | 0 => fixedLiteralInvPlusRow_0
  | 1 => fixedLiteralInvPlusRow_1
  | 2 => fixedLiteralInvPlusRow_2
  | 3 => fixedLiteralInvPlusRow_3
  | 4 => fixedLiteralInvPlusRow_4
  | 5 => fixedLiteralInvPlusRow_5
  | 6 => fixedLiteralInvPlusRow_6
  | 7 => fixedLiteralInvPlusRow_7
  | 8 => fixedLiteralInvPlusRow_8
  | 9 => fixedLiteralInvPlusRow_9
  | 10 => fixedLiteralInvPlusRow_10
  | 11 => fixedLiteralInvPlusRow_11
  | 12 => fixedLiteralInvPlusRow_12
  | 13 => fixedLiteralInvPlusRow_13
  | 14 => fixedLiteralInvPlusRow_14
  | 15 => fixedLiteralInvPlusRow_15
  | 16 => fixedLiteralInvPlusRow_16
  | 17 => fixedLiteralInvPlusRow_17
  | 18 => fixedLiteralInvPlusRow_18
  | 19 => fixedLiteralInvPlusRow_19
  | 20 => fixedLiteralInvPlusRow_20
  | 21 => fixedLiteralInvPlusRow_21
  | 22 => fixedLiteralInvPlusRow_22
  | 23 => fixedLiteralInvPlusRow_23
  | 24 => fixedLiteralInvPlusRow_24
  | 25 => fixedLiteralInvPlusRow_25
  | 26 => fixedLiteralInvPlusRow_26
  | 27 => fixedLiteralInvPlusRow_27
  | 28 => fixedLiteralInvPlusRow_28
  | 29 => fixedLiteralInvPlusRow_29
  | 30 => fixedLiteralInvPlusRow_30
  | 31 => fixedLiteralInvPlusRow_31
  | 32 => fixedLiteralInvPlusRow_32
  | 33 => fixedLiteralInvPlusRow_33
  | 34 => fixedLiteralInvPlusRow_34
  | 35 => fixedLiteralInvPlusRow_35
  | 36 => fixedLiteralInvPlusRow_36
  | 37 => fixedLiteralInvPlusRow_37
  | 38 => fixedLiteralInvPlusRow_38
  | 39 => fixedLiteralInvPlusRow_39
  | 40 => fixedLiteralInvPlusRow_40
  | 41 => fixedLiteralInvPlusRow_41
  | 42 => fixedLiteralInvPlusRow_42
  | 43 => fixedLiteralInvPlusRow_43
  | 44 => fixedLiteralInvPlusRow_44
  | 45 => fixedLiteralInvPlusRow_45
  | 46 => fixedLiteralInvPlusRow_46
  | 47 => fixedLiteralInvPlusRow_47
  | _ => fun _ => 0

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_0 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 0 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 0 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_1 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 1 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 1 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_10 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 10 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 10 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_11 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 11 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 11 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_12 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 12 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 12 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_13 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 13 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 13 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_14 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 14 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 14 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_15 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 15 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 15 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_16 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 16 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 16 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_17 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 17 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 17 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_18 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 18 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 18 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_19 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 19 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 19 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_20 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 20 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 20 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_21 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 21 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 21 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_22 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 22 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 22 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_23 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 23 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 23 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_24 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 24 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 24 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_25 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 25 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 25 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_26 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 26 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 26 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_27 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 27 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 27 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_28 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 28 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 28 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_29 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 29 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 29 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_2 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 2 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 2 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_3 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 3 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 3 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_30 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 30 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 30 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_31 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 31 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 31 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_32 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 32 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 32 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_33 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 33 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 33 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_34 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 34 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 34 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_35 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 35 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 35 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_36 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 36 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 36 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_37 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 37 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 37 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_38 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 38 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 38 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_39 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 39 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 39 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_40 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 40 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 40 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_41 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 41 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 41 k := by
  decide +kernel

end InternalCatalan

end

end OAI
