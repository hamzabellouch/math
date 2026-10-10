import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationRegular

namespace OAI

/-! A bounded third-order spatial jet for the finite Ising continuation.
Only the square and actual Gaussian transition operations are required. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

structure MagneticContinuationJet where
  value : ℝ → ℝ
  first : ℝ → ℝ
  second : ℝ → ℝ
  third : ℝ → ℝ
  mValue : Measurable value
  mFirst : Measurable first
  mSecond : Measurable second
  mThird : Measurable third
  bValue : MagneticContinuationBound value
  bFirst : MagneticContinuationBound first
  bSecond : MagneticContinuationBound second
  bThird : MagneticContinuationBound third
  dValue : ∀ z, HasDerivAt value (first z) z
  dFirst : ∀ z, HasDerivAt first (second z) z
  dSecond : ∀ z, HasDerivAt second (third z) z

namespace MagneticContinuationJet

def square (A : MagneticContinuationJet) : MagneticContinuationJet where
  value := fun z => (A.value z) ^ 2
  first := fun z => 2 * A.value z * A.first z
  second := fun z => 2 * (A.first z) ^ 2 + 2 * A.value z * A.second z
  third := fun z => 6 * A.first z * A.second z + 2 * A.value z * A.third z
  mValue := A.mValue.pow_const 2
  mFirst := (measurable_const.mul A.mValue).mul A.mFirst
  mSecond := (measurable_const.mul (A.mFirst.pow_const 2)).add
    ((measurable_const.mul A.mValue).mul A.mSecond)
  mThird := ((measurable_const.mul A.mFirst).mul A.mSecond).add
    ((measurable_const.mul A.mValue).mul A.mThird)
  bValue := by simpa only [pow_two] using A.bValue.mul A.bValue
  bFirst := ((MagneticContinuationBound.const 2).mul A.bValue).mul A.bFirst
  bSecond := by
    have hs : MagneticContinuationBound (fun z => (A.first z) ^ 2) := by
      simpa only [pow_two] using A.bFirst.mul A.bFirst
    exact ((MagneticContinuationBound.const 2).mul hs).add
      (((MagneticContinuationBound.const 2).mul A.bValue).mul A.bSecond)
  bThird := (((MagneticContinuationBound.const 6).mul A.bFirst).mul A.bSecond).add
    (((MagneticContinuationBound.const 2).mul A.bValue).mul A.bThird)
  dValue := fun z => by
    convert (A.dValue z).pow 2 using 1
    ring
  dFirst := fun z => by
    convert ((A.dValue z).const_mul 2).mul (A.dFirst z) using 1
    ring
  dSecond := fun z => by
    convert (((A.dFirst z).pow 2).const_mul 2).add
      (((A.dValue z).const_mul 2).mul (A.dSecond z)) using 1
    ring

def transition (A P : MagneticContinuationJet) (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) : MagneticContinuationJet where
  value := fieldSpinTransition ζ v F A.value
  first := fieldTiltSpatial ζ v F P.value A.value A.first
  second := magneticContinuationSecond ζ v F P.value P.first A.value A.first A.second
  third := magneticContinuationThird ζ v F P.value P.first P.second
    A.value A.first A.second A.third
  mValue := measurable_fieldSpinTransition ζ v hF A.mValue
  mFirst := measurable_fieldTiltSpatial ζ v hF P.mValue A.mValue A.mFirst
  mSecond := measurable_magneticContinuationSecond ζ v hF P.mValue P.mFirst
    A.mValue A.mFirst A.mSecond
  mThird := measurable_magneticContinuationThird ζ v hF P.mValue P.mFirst P.mSecond
    A.mValue A.mFirst A.mSecond A.mThird
  bValue := A.bValue.transition ζ v hF hG
  bFirst := MagneticContinuationBound.spatial ζ v hF hG P.bValue A.bValue A.bFirst
  bSecond := magneticContinuationSecond_bounded ζ v hF hG P.bValue P.bFirst
    A.bValue A.bFirst A.bSecond
  bThird := magneticContinuationThird_bounded ζ v hF hG P.bValue P.bFirst P.bSecond
    A.bValue A.bFirst A.bSecond A.bThird
  dValue := fun z => by
    obtain ⟨K, hK, bK⟩ := P.bValue
    obtain ⟨L, hL, bL⟩ := A.bValue
    obtain ⟨C, _, bC⟩ := A.bFirst
    exact hasDerivAt_fieldSpinTransition ζ v hF hG P.mValue A.mValue A.mFirst
      hK hL bK bL bC dF A.dValue z
  dFirst := fun z => by
    obtain ⟨K, hK, bK⟩ := P.bValue
    obtain ⟨L, hL, bL⟩ := P.bFirst
    obtain ⟨a, ha, ba⟩ := A.bValue
    obtain ⟨b, hb, bb⟩ := A.bFirst
    obtain ⟨c, _, bc⟩ := A.bSecond
    exact hasDerivAt_magneticContinuationSecond ζ v hF hG P.mValue P.mFirst
      A.mValue A.mFirst A.mSecond hK hL ha hb bK bL ba bb bc dF P.dValue
      A.dValue A.dFirst z
  dSecond := fun z => by
    obtain ⟨K, hK, bK⟩ := P.bValue
    obtain ⟨L, hL, bL⟩ := P.bFirst
    obtain ⟨J, _, bJ⟩ := P.bSecond
    obtain ⟨a, ha, ba⟩ := A.bValue
    obtain ⟨b, hb, bb⟩ := A.bFirst
    obtain ⟨c, hc, bc⟩ := A.bSecond
    obtain ⟨d, _, bd⟩ := A.bThird
    exact hasDerivAt_magneticContinuationThird ζ v hF hG P.mValue P.mFirst P.mSecond
      A.mValue A.mFirst A.mSecond A.mThird hK hL ha hb hc bK bL bJ ba bb bc bd
      dF P.dValue P.dFirst A.dValue A.dFirst A.dSecond z

end MagneticContinuationJet
end InvariantIsing

end

end OAI
