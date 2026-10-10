import OAI.Probability.InvariantIsing.Magnetic.MagneticJetProduct

namespace OAI

/-! One additional bounded spatial derivative, exactly as needed to
differentiate the inverse-coordinate curvature equation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

structure MagneticContinuationFourJet extends MagneticContinuationJet where
  fourth : ℝ → ℝ
  mFourth : Measurable fourth
  bFourth : MagneticContinuationBound fourth
  dThird : ∀ z, HasDerivAt third (fourth z) z

namespace MagneticContinuationFourJet

def slope (A : MagneticContinuationFourJet) : MagneticContinuationJet where
  value := A.first
  first := A.second
  second := A.third
  third := A.fourth
  mValue := A.mFirst
  mFirst := A.mSecond
  mSecond := A.mThird
  mThird := A.mFourth
  bValue := A.bFirst
  bFirst := A.bSecond
  bSecond := A.bThird
  bThird := A.bFourth
  dValue := A.dFirst
  dFirst := A.dSecond
  dSecond := A.dThird

def square (A : MagneticContinuationFourJet) : MagneticContinuationFourJet where
  toMagneticContinuationJet := A.toMagneticContinuationJet.square
  fourth := fun z => 6 * (A.second z) ^ 2 + 8 * A.first z * A.third z + 2 * A.value z * A.fourth z
  mFourth := ((measurable_const.mul (A.mSecond.pow_const 2)).add
    ((measurable_const.mul A.mFirst).mul A.mThird)).add
      ((measurable_const.mul A.mValue).mul A.mFourth)
  bFourth := by
    have h2 : MagneticContinuationBound (fun z => (A.second z) ^ 2) := by
      simpa only [pow_two] using A.bSecond.mul A.bSecond
    exact (((MagneticContinuationBound.const 6).mul h2).add
      (((MagneticContinuationBound.const 8).mul A.bFirst).mul A.bThird)).add
        (((MagneticContinuationBound.const 2).mul A.bValue).mul A.bFourth)
  dThird := fun z => by
    convert (((A.dFirst z).const_mul 6).mul (A.dSecond z)).add
      (((A.dValue z).const_mul 2).mul (A.dThird z)) using 1
    · funext y
      dsimp only [MagneticContinuationJet.square, Pi.add_apply, Pi.mul_apply]
    · ring

def transitionFourth (A : MagneticContinuationFourJet) (P : MagneticContinuationJet)
    (ζ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (z : ℝ) : ℝ :=
  let U := A.toMagneticContinuationJet.transition P ζ v F hF hG dF
  let V := P.transition P ζ v F hF hG dF
  let W := (A.toMagneticContinuationJet.mul P).transition P ζ v F hF hG dF
  let R := A.slope.transition P ζ v F hF hG dF
  R.third z + ζ * (W.third z - (U.third z * V.value z +
    3 * U.second z * V.first z + 3 * U.first z * V.second z + U.value z * V.third z))

lemma transition_third_eq (A : MagneticContinuationFourJet) (P : MagneticContinuationJet)
    (ζ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) :
    let U := A.toMagneticContinuationJet.transition P ζ v F hF hG dF
    let V := P.transition P ζ v F hF hG dF
    let W := (A.toMagneticContinuationJet.mul P).transition P ζ v F hF hG dF
    let R := A.slope.transition P ζ v F hF hG dF
    U.third = fun z => R.second z + ζ * (W.second z -
      (U.second z * V.value z + 2 * U.first z * V.first z + U.value z * V.second z)) := by
  rfl

lemma transitionFourth_measurable (A : MagneticContinuationFourJet) (P : MagneticContinuationJet)
    (ζ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) :
    Measurable (A.transitionFourth P ζ v F hF hG dF) := by
  let U := A.toMagneticContinuationJet.transition P ζ v F hF hG dF
  let V := P.transition P ζ v F hF hG dF
  let W := (A.toMagneticContinuationJet.mul P).transition P ζ v F hF hG dF
  let R := A.slope.transition P ζ v F hF hG dF
  exact R.mThird.add ((W.mThird.sub ((((U.mThird.mul V.mValue).add
    ((measurable_const.mul U.mSecond).mul V.mFirst)).add
      ((measurable_const.mul U.mFirst).mul V.mSecond)).add (U.mValue.mul V.mThird))).const_mul ζ)

lemma transitionFourth_bounded (A : MagneticContinuationFourJet) (P : MagneticContinuationJet)
    (ζ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) :
    MagneticContinuationBound (A.transitionFourth P ζ v F hF hG dF) := by
  let U := A.toMagneticContinuationJet.transition P ζ v F hF hG dF
  let V := P.transition P ζ v F hF hG dF
  let W := (A.toMagneticContinuationJet.mul P).transition P ζ v F hF hG dF
  let R := A.slope.transition P ζ v F hF hG dF
  exact R.bThird.add ((MagneticContinuationBound.const ζ).mul
    (W.bThird.sub ((((U.bThird.mul V.bValue).add
      (((MagneticContinuationBound.const 3).mul U.bSecond).mul V.bFirst)).add
        (((MagneticContinuationBound.const 3).mul U.bFirst).mul V.bSecond)).add
          (U.bValue.mul V.bThird))))

lemma transition_hasDerivAt_third (A : MagneticContinuationFourJet) (P : MagneticContinuationJet)
    (ζ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (z : ℝ) :
    HasDerivAt (A.toMagneticContinuationJet.transition P ζ v F hF hG dF).third
      (A.transitionFourth P ζ v F hF hG dF z) z := by
  let U := A.toMagneticContinuationJet.transition P ζ v F hF hG dF
  let V := P.transition P ζ v F hF hG dF
  let W := (A.toMagneticContinuationJet.mul P).transition P ζ v F hF hG dF
  let R := A.slope.transition P ζ v F hF hG dF
  rw [transition_third_eq]
  have hd := (R.dSecond z).add (((W.dSecond z).sub
    ((((U.dSecond z).mul (V.dValue z)).add
      (((U.dFirst z).const_mul 2).mul (V.dFirst z))).add
        ((U.dValue z).mul (V.dSecond z)))).const_mul ζ)
  convert hd using 1
  dsimp only [transitionFourth]
  ring

def transition (A : MagneticContinuationFourJet) (P : MagneticContinuationJet)
    (ζ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) : MagneticContinuationFourJet where
  toMagneticContinuationJet := A.toMagneticContinuationJet.transition P ζ v F hF hG dF
  fourth := A.transitionFourth P ζ v F hF hG dF
  mFourth := A.transitionFourth_measurable P ζ v F hF hG dF
  bFourth := A.transitionFourth_bounded P ζ v F hF hG dF
  dThird := A.transition_hasDerivAt_third P ζ v F hF hG dF

end MagneticContinuationFourJet
end InvariantIsing

end

end OAI
