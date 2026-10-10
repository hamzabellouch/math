import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationIBP
import OAI.Probability.InvariantIsing.Fields.FieldSecondFamily

namespace OAI

/-! The fixed terminal potential as an actual two-coordinate family.
This permits use of the established affine Gaussian differentiation theorem
for the inverse-coordinate time comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def magneticStationaryFamily (I : Set ℝ) (F : ℝ → ℝ) (P : MagneticContinuationJet)
    (hF : Measurable F) (K L : ℝ) (bK : ∀ z, |P.value z| ≤ K)
    (bL : ∀ z, |P.first z| ≤ L) (dF : ∀ z, HasDerivAt F (P.value z) z) :
    FieldSecondFamily I where
  U := fun p => F p.2
  X := fun p => P.value p.2
  XX := fun p => P.first p.2
  T := fun _ => 0
  KX := K
  KXX := L
  KT := 0
  mU := hF.comp measurable_snd
  mX := P.mValue.comp measurable_snd
  mXX := P.mFirst.comp measurable_snd
  mT := measurable_const
  bX := fun p => bK p.2
  bXX := fun p => bL p.2
  bT := fun _ _ => by simp
  derivative := fun p _ => by
    convert (dF p.2).hasFDerivAt.comp p hasFDerivAt_snd using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro q
      simp [pairLinear, mul_comm]
  spatial := fun _ => dF
  second := fun _ => P.dValue
  TX := fun _ => 0
  TT := fun _ => 0
  KTX := 0
  KTT := 0
  mTX := measurable_const
  mTT := measurable_const
  bTX := fun _ _ => by simp
  bTT := fun _ _ => by simp
  derivativeX := fun p _ => by
    convert (P.dValue p.2).hasFDerivAt.comp p hasFDerivAt_snd using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro q
      simp [pairLinear, mul_comm]
  derivativeT := fun p _ => by
    convert hasFDerivAt_const (0 : ℝ) p using 1
    apply ContinuousLinearMap.ext
    intro q
    simp [pairLinear]

end InvariantIsing

end

end OAI
