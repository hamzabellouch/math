import Mathlib.Tactic.FinCases
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedGaussianMinusStep47
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedGaussianPlusStep47
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedGaussianZeroStep47

namespace OAI

section

namespace InternalCatalan

def fixedGaussianMinusStates (i : Fin 49) : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  match i.val with
  | 0 => fixedGaussianMinusState0
  | 1 => fixedGaussianMinusState1
  | 2 => fixedGaussianMinusState2
  | 3 => fixedGaussianMinusState3
  | 4 => fixedGaussianMinusState4
  | 5 => fixedGaussianMinusState5
  | 6 => fixedGaussianMinusState6
  | 7 => fixedGaussianMinusState7
  | 8 => fixedGaussianMinusState8
  | 9 => fixedGaussianMinusState9
  | 10 => fixedGaussianMinusState10
  | 11 => fixedGaussianMinusState11
  | 12 => fixedGaussianMinusState12
  | 13 => fixedGaussianMinusState13
  | 14 => fixedGaussianMinusState14
  | 15 => fixedGaussianMinusState15
  | 16 => fixedGaussianMinusState16
  | 17 => fixedGaussianMinusState17
  | 18 => fixedGaussianMinusState18
  | 19 => fixedGaussianMinusState19
  | 20 => fixedGaussianMinusState20
  | 21 => fixedGaussianMinusState21
  | 22 => fixedGaussianMinusState22
  | 23 => fixedGaussianMinusState23
  | 24 => fixedGaussianMinusState24
  | 25 => fixedGaussianMinusState25
  | 26 => fixedGaussianMinusState26
  | 27 => fixedGaussianMinusState27
  | 28 => fixedGaussianMinusState28
  | 29 => fixedGaussianMinusState29
  | 30 => fixedGaussianMinusState30
  | 31 => fixedGaussianMinusState31
  | 32 => fixedGaussianMinusState32
  | 33 => fixedGaussianMinusState33
  | 34 => fixedGaussianMinusState34
  | 35 => fixedGaussianMinusState35
  | 36 => fixedGaussianMinusState36
  | 37 => fixedGaussianMinusState37
  | 38 => fixedGaussianMinusState38
  | 39 => fixedGaussianMinusState39
  | 40 => fixedGaussianMinusState40
  | 41 => fixedGaussianMinusState41
  | 42 => fixedGaussianMinusState42
  | 43 => fixedGaussianMinusState43
  | 44 => fixedGaussianMinusState44
  | 45 => fixedGaussianMinusState45
  | 46 => fixedGaussianMinusState46
  | 47 => fixedGaussianMinusState47
  | 48 => fixedGaussianMinusState48
  | _ => 0

theorem fixedGaussianMinus_trace :
    fixedGaussianTrace (fixedGaussianUnscaled (-1)) fixedGaussianMinusStates
      fixedGaussianMinusRows fixedGaussianMinusPivots := by
  unfold fixedGaussianTrace
  constructor
  · exact fixedGaussianMinusState0_eq
  · intro i
    fin_cases i
    · exact ⟨fixedGaussianMinusStep0_pivot, fixedGaussianMinusStep0_eq⟩
    · exact ⟨fixedGaussianMinusStep1_pivot, fixedGaussianMinusStep1_eq⟩
    · exact ⟨fixedGaussianMinusStep2_pivot, fixedGaussianMinusStep2_eq⟩
    · exact ⟨fixedGaussianMinusStep3_pivot, fixedGaussianMinusStep3_eq⟩
    · exact ⟨fixedGaussianMinusStep4_pivot, fixedGaussianMinusStep4_eq⟩
    · exact ⟨fixedGaussianMinusStep5_pivot, fixedGaussianMinusStep5_eq⟩
    · exact ⟨fixedGaussianMinusStep6_pivot, fixedGaussianMinusStep6_eq⟩
    · exact ⟨fixedGaussianMinusStep7_pivot, fixedGaussianMinusStep7_eq⟩
    · exact ⟨fixedGaussianMinusStep8_pivot, fixedGaussianMinusStep8_eq⟩
    · exact ⟨fixedGaussianMinusStep9_pivot, fixedGaussianMinusStep9_eq⟩
    · exact ⟨fixedGaussianMinusStep10_pivot, fixedGaussianMinusStep10_eq⟩
    · exact ⟨fixedGaussianMinusStep11_pivot, fixedGaussianMinusStep11_eq⟩
    · exact ⟨fixedGaussianMinusStep12_pivot, fixedGaussianMinusStep12_eq⟩
    · exact ⟨fixedGaussianMinusStep13_pivot, fixedGaussianMinusStep13_eq⟩
    · exact ⟨fixedGaussianMinusStep14_pivot, fixedGaussianMinusStep14_eq⟩
    · exact ⟨fixedGaussianMinusStep15_pivot, fixedGaussianMinusStep15_eq⟩
    · exact ⟨fixedGaussianMinusStep16_pivot, fixedGaussianMinusStep16_eq⟩
    · exact ⟨fixedGaussianMinusStep17_pivot, fixedGaussianMinusStep17_eq⟩
    · exact ⟨fixedGaussianMinusStep18_pivot, fixedGaussianMinusStep18_eq⟩
    · exact ⟨fixedGaussianMinusStep19_pivot, fixedGaussianMinusStep19_eq⟩
    · exact ⟨fixedGaussianMinusStep20_pivot, fixedGaussianMinusStep20_eq⟩
    · exact ⟨fixedGaussianMinusStep21_pivot, fixedGaussianMinusStep21_eq⟩
    · exact ⟨fixedGaussianMinusStep22_pivot, fixedGaussianMinusStep22_eq⟩
    · exact ⟨fixedGaussianMinusStep23_pivot, fixedGaussianMinusStep23_eq⟩
    · exact ⟨fixedGaussianMinusStep24_pivot, fixedGaussianMinusStep24_eq⟩
    · exact ⟨fixedGaussianMinusStep25_pivot, fixedGaussianMinusStep25_eq⟩
    · exact ⟨fixedGaussianMinusStep26_pivot, fixedGaussianMinusStep26_eq⟩
    · exact ⟨fixedGaussianMinusStep27_pivot, fixedGaussianMinusStep27_eq⟩
    · exact ⟨fixedGaussianMinusStep28_pivot, fixedGaussianMinusStep28_eq⟩
    · exact ⟨fixedGaussianMinusStep29_pivot, fixedGaussianMinusStep29_eq⟩
    · exact ⟨fixedGaussianMinusStep30_pivot, fixedGaussianMinusStep30_eq⟩
    · exact ⟨fixedGaussianMinusStep31_pivot, fixedGaussianMinusStep31_eq⟩
    · exact ⟨fixedGaussianMinusStep32_pivot, fixedGaussianMinusStep32_eq⟩
    · exact ⟨fixedGaussianMinusStep33_pivot, fixedGaussianMinusStep33_eq⟩
    · exact ⟨fixedGaussianMinusStep34_pivot, fixedGaussianMinusStep34_eq⟩
    · exact ⟨fixedGaussianMinusStep35_pivot, fixedGaussianMinusStep35_eq⟩
    · exact ⟨fixedGaussianMinusStep36_pivot, fixedGaussianMinusStep36_eq⟩
    · exact ⟨fixedGaussianMinusStep37_pivot, fixedGaussianMinusStep37_eq⟩
    · exact ⟨fixedGaussianMinusStep38_pivot, fixedGaussianMinusStep38_eq⟩
    · exact ⟨fixedGaussianMinusStep39_pivot, fixedGaussianMinusStep39_eq⟩
    · exact ⟨fixedGaussianMinusStep40_pivot, fixedGaussianMinusStep40_eq⟩
    · exact ⟨fixedGaussianMinusStep41_pivot, fixedGaussianMinusStep41_eq⟩
    · exact ⟨fixedGaussianMinusStep42_pivot, fixedGaussianMinusStep42_eq⟩
    · exact ⟨fixedGaussianMinusStep43_pivot, fixedGaussianMinusStep43_eq⟩
    · exact ⟨fixedGaussianMinusStep44_pivot, fixedGaussianMinusStep44_eq⟩
    · exact ⟨fixedGaussianMinusStep45_pivot, fixedGaussianMinusStep45_eq⟩
    · exact ⟨fixedGaussianMinusStep46_pivot, fixedGaussianMinusStep46_eq⟩
    · exact ⟨fixedGaussianMinusStep47_pivot, fixedGaussianMinusStep47_eq⟩

end InternalCatalan

end

section

namespace InternalCatalan

def fixedGaussianPlusStates (i : Fin 49) : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  match i.val with
  | 0 => fixedGaussianPlusState0
  | 1 => fixedGaussianPlusState1
  | 2 => fixedGaussianPlusState2
  | 3 => fixedGaussianPlusState3
  | 4 => fixedGaussianPlusState4
  | 5 => fixedGaussianPlusState5
  | 6 => fixedGaussianPlusState6
  | 7 => fixedGaussianPlusState7
  | 8 => fixedGaussianPlusState8
  | 9 => fixedGaussianPlusState9
  | 10 => fixedGaussianPlusState10
  | 11 => fixedGaussianPlusState11
  | 12 => fixedGaussianPlusState12
  | 13 => fixedGaussianPlusState13
  | 14 => fixedGaussianPlusState14
  | 15 => fixedGaussianPlusState15
  | 16 => fixedGaussianPlusState16
  | 17 => fixedGaussianPlusState17
  | 18 => fixedGaussianPlusState18
  | 19 => fixedGaussianPlusState19
  | 20 => fixedGaussianPlusState20
  | 21 => fixedGaussianPlusState21
  | 22 => fixedGaussianPlusState22
  | 23 => fixedGaussianPlusState23
  | 24 => fixedGaussianPlusState24
  | 25 => fixedGaussianPlusState25
  | 26 => fixedGaussianPlusState26
  | 27 => fixedGaussianPlusState27
  | 28 => fixedGaussianPlusState28
  | 29 => fixedGaussianPlusState29
  | 30 => fixedGaussianPlusState30
  | 31 => fixedGaussianPlusState31
  | 32 => fixedGaussianPlusState32
  | 33 => fixedGaussianPlusState33
  | 34 => fixedGaussianPlusState34
  | 35 => fixedGaussianPlusState35
  | 36 => fixedGaussianPlusState36
  | 37 => fixedGaussianPlusState37
  | 38 => fixedGaussianPlusState38
  | 39 => fixedGaussianPlusState39
  | 40 => fixedGaussianPlusState40
  | 41 => fixedGaussianPlusState41
  | 42 => fixedGaussianPlusState42
  | 43 => fixedGaussianPlusState43
  | 44 => fixedGaussianPlusState44
  | 45 => fixedGaussianPlusState45
  | 46 => fixedGaussianPlusState46
  | 47 => fixedGaussianPlusState47
  | 48 => fixedGaussianPlusState48
  | _ => 0

theorem fixedGaussianPlus_trace :
    fixedGaussianTrace (fixedGaussianUnscaled 1) fixedGaussianPlusStates
      fixedGaussianPlusRows fixedGaussianPlusPivots := by
  unfold fixedGaussianTrace
  constructor
  · exact fixedGaussianPlusState0_eq
  · intro i
    fin_cases i
    · exact ⟨fixedGaussianPlusStep0_pivot, fixedGaussianPlusStep0_eq⟩
    · exact ⟨fixedGaussianPlusStep1_pivot, fixedGaussianPlusStep1_eq⟩
    · exact ⟨fixedGaussianPlusStep2_pivot, fixedGaussianPlusStep2_eq⟩
    · exact ⟨fixedGaussianPlusStep3_pivot, fixedGaussianPlusStep3_eq⟩
    · exact ⟨fixedGaussianPlusStep4_pivot, fixedGaussianPlusStep4_eq⟩
    · exact ⟨fixedGaussianPlusStep5_pivot, fixedGaussianPlusStep5_eq⟩
    · exact ⟨fixedGaussianPlusStep6_pivot, fixedGaussianPlusStep6_eq⟩
    · exact ⟨fixedGaussianPlusStep7_pivot, fixedGaussianPlusStep7_eq⟩
    · exact ⟨fixedGaussianPlusStep8_pivot, fixedGaussianPlusStep8_eq⟩
    · exact ⟨fixedGaussianPlusStep9_pivot, fixedGaussianPlusStep9_eq⟩
    · exact ⟨fixedGaussianPlusStep10_pivot, fixedGaussianPlusStep10_eq⟩
    · exact ⟨fixedGaussianPlusStep11_pivot, fixedGaussianPlusStep11_eq⟩
    · exact ⟨fixedGaussianPlusStep12_pivot, fixedGaussianPlusStep12_eq⟩
    · exact ⟨fixedGaussianPlusStep13_pivot, fixedGaussianPlusStep13_eq⟩
    · exact ⟨fixedGaussianPlusStep14_pivot, fixedGaussianPlusStep14_eq⟩
    · exact ⟨fixedGaussianPlusStep15_pivot, fixedGaussianPlusStep15_eq⟩
    · exact ⟨fixedGaussianPlusStep16_pivot, fixedGaussianPlusStep16_eq⟩
    · exact ⟨fixedGaussianPlusStep17_pivot, fixedGaussianPlusStep17_eq⟩
    · exact ⟨fixedGaussianPlusStep18_pivot, fixedGaussianPlusStep18_eq⟩
    · exact ⟨fixedGaussianPlusStep19_pivot, fixedGaussianPlusStep19_eq⟩
    · exact ⟨fixedGaussianPlusStep20_pivot, fixedGaussianPlusStep20_eq⟩
    · exact ⟨fixedGaussianPlusStep21_pivot, fixedGaussianPlusStep21_eq⟩
    · exact ⟨fixedGaussianPlusStep22_pivot, fixedGaussianPlusStep22_eq⟩
    · exact ⟨fixedGaussianPlusStep23_pivot, fixedGaussianPlusStep23_eq⟩
    · exact ⟨fixedGaussianPlusStep24_pivot, fixedGaussianPlusStep24_eq⟩
    · exact ⟨fixedGaussianPlusStep25_pivot, fixedGaussianPlusStep25_eq⟩
    · exact ⟨fixedGaussianPlusStep26_pivot, fixedGaussianPlusStep26_eq⟩
    · exact ⟨fixedGaussianPlusStep27_pivot, fixedGaussianPlusStep27_eq⟩
    · exact ⟨fixedGaussianPlusStep28_pivot, fixedGaussianPlusStep28_eq⟩
    · exact ⟨fixedGaussianPlusStep29_pivot, fixedGaussianPlusStep29_eq⟩
    · exact ⟨fixedGaussianPlusStep30_pivot, fixedGaussianPlusStep30_eq⟩
    · exact ⟨fixedGaussianPlusStep31_pivot, fixedGaussianPlusStep31_eq⟩
    · exact ⟨fixedGaussianPlusStep32_pivot, fixedGaussianPlusStep32_eq⟩
    · exact ⟨fixedGaussianPlusStep33_pivot, fixedGaussianPlusStep33_eq⟩
    · exact ⟨fixedGaussianPlusStep34_pivot, fixedGaussianPlusStep34_eq⟩
    · exact ⟨fixedGaussianPlusStep35_pivot, fixedGaussianPlusStep35_eq⟩
    · exact ⟨fixedGaussianPlusStep36_pivot, fixedGaussianPlusStep36_eq⟩
    · exact ⟨fixedGaussianPlusStep37_pivot, fixedGaussianPlusStep37_eq⟩
    · exact ⟨fixedGaussianPlusStep38_pivot, fixedGaussianPlusStep38_eq⟩
    · exact ⟨fixedGaussianPlusStep39_pivot, fixedGaussianPlusStep39_eq⟩
    · exact ⟨fixedGaussianPlusStep40_pivot, fixedGaussianPlusStep40_eq⟩
    · exact ⟨fixedGaussianPlusStep41_pivot, fixedGaussianPlusStep41_eq⟩
    · exact ⟨fixedGaussianPlusStep42_pivot, fixedGaussianPlusStep42_eq⟩
    · exact ⟨fixedGaussianPlusStep43_pivot, fixedGaussianPlusStep43_eq⟩
    · exact ⟨fixedGaussianPlusStep44_pivot, fixedGaussianPlusStep44_eq⟩
    · exact ⟨fixedGaussianPlusStep45_pivot, fixedGaussianPlusStep45_eq⟩
    · exact ⟨fixedGaussianPlusStep46_pivot, fixedGaussianPlusStep46_eq⟩
    · exact ⟨fixedGaussianPlusStep47_pivot, fixedGaussianPlusStep47_eq⟩

end InternalCatalan

end

section

namespace InternalCatalan

def fixedGaussianZeroStates (i : Fin 49) : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  match i.val with
  | 0 => fixedGaussianZeroState0
  | 1 => fixedGaussianZeroState1
  | 2 => fixedGaussianZeroState2
  | 3 => fixedGaussianZeroState3
  | 4 => fixedGaussianZeroState4
  | 5 => fixedGaussianZeroState5
  | 6 => fixedGaussianZeroState6
  | 7 => fixedGaussianZeroState7
  | 8 => fixedGaussianZeroState8
  | 9 => fixedGaussianZeroState9
  | 10 => fixedGaussianZeroState10
  | 11 => fixedGaussianZeroState11
  | 12 => fixedGaussianZeroState12
  | 13 => fixedGaussianZeroState13
  | 14 => fixedGaussianZeroState14
  | 15 => fixedGaussianZeroState15
  | 16 => fixedGaussianZeroState16
  | 17 => fixedGaussianZeroState17
  | 18 => fixedGaussianZeroState18
  | 19 => fixedGaussianZeroState19
  | 20 => fixedGaussianZeroState20
  | 21 => fixedGaussianZeroState21
  | 22 => fixedGaussianZeroState22
  | 23 => fixedGaussianZeroState23
  | 24 => fixedGaussianZeroState24
  | 25 => fixedGaussianZeroState25
  | 26 => fixedGaussianZeroState26
  | 27 => fixedGaussianZeroState27
  | 28 => fixedGaussianZeroState28
  | 29 => fixedGaussianZeroState29
  | 30 => fixedGaussianZeroState30
  | 31 => fixedGaussianZeroState31
  | 32 => fixedGaussianZeroState32
  | 33 => fixedGaussianZeroState33
  | 34 => fixedGaussianZeroState34
  | 35 => fixedGaussianZeroState35
  | 36 => fixedGaussianZeroState36
  | 37 => fixedGaussianZeroState37
  | 38 => fixedGaussianZeroState38
  | 39 => fixedGaussianZeroState39
  | 40 => fixedGaussianZeroState40
  | 41 => fixedGaussianZeroState41
  | 42 => fixedGaussianZeroState42
  | 43 => fixedGaussianZeroState43
  | 44 => fixedGaussianZeroState44
  | 45 => fixedGaussianZeroState45
  | 46 => fixedGaussianZeroState46
  | 47 => fixedGaussianZeroState47
  | 48 => fixedGaussianZeroState48
  | _ => 0

theorem fixedGaussianZero_trace :
    fixedGaussianTrace (fixedGaussianUnscaled 0) fixedGaussianZeroStates
      fixedGaussianZeroRows fixedGaussianZeroPivots := by
  unfold fixedGaussianTrace
  constructor
  · exact fixedGaussianZeroState0_eq
  · intro i
    fin_cases i
    · exact ⟨fixedGaussianZeroStep0_pivot, fixedGaussianZeroStep0_eq⟩
    · exact ⟨fixedGaussianZeroStep1_pivot, fixedGaussianZeroStep1_eq⟩
    · exact ⟨fixedGaussianZeroStep2_pivot, fixedGaussianZeroStep2_eq⟩
    · exact ⟨fixedGaussianZeroStep3_pivot, fixedGaussianZeroStep3_eq⟩
    · exact ⟨fixedGaussianZeroStep4_pivot, fixedGaussianZeroStep4_eq⟩
    · exact ⟨fixedGaussianZeroStep5_pivot, fixedGaussianZeroStep5_eq⟩
    · exact ⟨fixedGaussianZeroStep6_pivot, fixedGaussianZeroStep6_eq⟩
    · exact ⟨fixedGaussianZeroStep7_pivot, fixedGaussianZeroStep7_eq⟩
    · exact ⟨fixedGaussianZeroStep8_pivot, fixedGaussianZeroStep8_eq⟩
    · exact ⟨fixedGaussianZeroStep9_pivot, fixedGaussianZeroStep9_eq⟩
    · exact ⟨fixedGaussianZeroStep10_pivot, fixedGaussianZeroStep10_eq⟩
    · exact ⟨fixedGaussianZeroStep11_pivot, fixedGaussianZeroStep11_eq⟩
    · exact ⟨fixedGaussianZeroStep12_pivot, fixedGaussianZeroStep12_eq⟩
    · exact ⟨fixedGaussianZeroStep13_pivot, fixedGaussianZeroStep13_eq⟩
    · exact ⟨fixedGaussianZeroStep14_pivot, fixedGaussianZeroStep14_eq⟩
    · exact ⟨fixedGaussianZeroStep15_pivot, fixedGaussianZeroStep15_eq⟩
    · exact ⟨fixedGaussianZeroStep16_pivot, fixedGaussianZeroStep16_eq⟩
    · exact ⟨fixedGaussianZeroStep17_pivot, fixedGaussianZeroStep17_eq⟩
    · exact ⟨fixedGaussianZeroStep18_pivot, fixedGaussianZeroStep18_eq⟩
    · exact ⟨fixedGaussianZeroStep19_pivot, fixedGaussianZeroStep19_eq⟩
    · exact ⟨fixedGaussianZeroStep20_pivot, fixedGaussianZeroStep20_eq⟩
    · exact ⟨fixedGaussianZeroStep21_pivot, fixedGaussianZeroStep21_eq⟩
    · exact ⟨fixedGaussianZeroStep22_pivot, fixedGaussianZeroStep22_eq⟩
    · exact ⟨fixedGaussianZeroStep23_pivot, fixedGaussianZeroStep23_eq⟩
    · exact ⟨fixedGaussianZeroStep24_pivot, fixedGaussianZeroStep24_eq⟩
    · exact ⟨fixedGaussianZeroStep25_pivot, fixedGaussianZeroStep25_eq⟩
    · exact ⟨fixedGaussianZeroStep26_pivot, fixedGaussianZeroStep26_eq⟩
    · exact ⟨fixedGaussianZeroStep27_pivot, fixedGaussianZeroStep27_eq⟩
    · exact ⟨fixedGaussianZeroStep28_pivot, fixedGaussianZeroStep28_eq⟩
    · exact ⟨fixedGaussianZeroStep29_pivot, fixedGaussianZeroStep29_eq⟩
    · exact ⟨fixedGaussianZeroStep30_pivot, fixedGaussianZeroStep30_eq⟩
    · exact ⟨fixedGaussianZeroStep31_pivot, fixedGaussianZeroStep31_eq⟩
    · exact ⟨fixedGaussianZeroStep32_pivot, fixedGaussianZeroStep32_eq⟩
    · exact ⟨fixedGaussianZeroStep33_pivot, fixedGaussianZeroStep33_eq⟩
    · exact ⟨fixedGaussianZeroStep34_pivot, fixedGaussianZeroStep34_eq⟩
    · exact ⟨fixedGaussianZeroStep35_pivot, fixedGaussianZeroStep35_eq⟩
    · exact ⟨fixedGaussianZeroStep36_pivot, fixedGaussianZeroStep36_eq⟩
    · exact ⟨fixedGaussianZeroStep37_pivot, fixedGaussianZeroStep37_eq⟩
    · exact ⟨fixedGaussianZeroStep38_pivot, fixedGaussianZeroStep38_eq⟩
    · exact ⟨fixedGaussianZeroStep39_pivot, fixedGaussianZeroStep39_eq⟩
    · exact ⟨fixedGaussianZeroStep40_pivot, fixedGaussianZeroStep40_eq⟩
    · exact ⟨fixedGaussianZeroStep41_pivot, fixedGaussianZeroStep41_eq⟩
    · exact ⟨fixedGaussianZeroStep42_pivot, fixedGaussianZeroStep42_eq⟩
    · exact ⟨fixedGaussianZeroStep43_pivot, fixedGaussianZeroStep43_eq⟩
    · exact ⟨fixedGaussianZeroStep44_pivot, fixedGaussianZeroStep44_eq⟩
    · exact ⟨fixedGaussianZeroStep45_pivot, fixedGaussianZeroStep45_eq⟩
    · exact ⟨fixedGaussianZeroStep46_pivot, fixedGaussianZeroStep46_eq⟩
    · exact ⟨fixedGaussianZeroStep47_pivot, fixedGaussianZeroStep47_eq⟩

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedGaussian_manuscript_trace :
    fixedGaussianTrace (fixedGaussianUnscaled 0) fixedGaussianZeroStates
      fixedGaussianZeroRows fixedGaussianZeroPivots ∧
    fixedGaussianTrace (fixedGaussianUnscaled 1) fixedGaussianPlusStates
      fixedGaussianPlusRows fixedGaussianPlusPivots ∧
    fixedGaussianTrace (fixedGaussianUnscaled (-1)) fixedGaussianMinusStates
      fixedGaussianMinusRows fixedGaussianMinusPivots :=
  ⟨fixedGaussianZero_trace, fixedGaussianPlus_trace, fixedGaussianMinus_trace⟩

end InternalCatalan

end

end OAI
