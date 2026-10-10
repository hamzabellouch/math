import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProductReorder

namespace OAI

/-! # The homeomorphism exchanging the selected root and remaining group -/

noncomputable section
open Matrix MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

lemma nextConjugation_neg_cancel (d : ℕ) (q : InitialRootStep (d+1)) (r : ℝ)
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) :
    q.nextConjugation d r (q.nextConjugation d (-r) w) = w := by
  apply Subtype.ext
  change Matrix.SpecialLinearGroup.transvection q.distinct (-r) *
      (Matrix.SpecialLinearGroup.transvection q.distinct (-(-r)) * w.val *
        Matrix.SpecialLinearGroup.transvection q.distinct (-r)) *
      Matrix.SpecialLinearGroup.transvection q.distinct r = w.val
  rw [neg_neg,←Matrix.SpecialLinearGroup.transvection_inv]
  group

def rootOrderCoordinates (d : ℕ) (q : InitialRootStep (d+1)) :
    (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) ≃ₜ
      (ℝ × positiveRootGeneratedGroup (q.remaining.erase q.root)) where
  toFun z := (z.2,q.nextConjugation d z.2 z.1)
  invFun z := (q.nextConjugation d (-z.1) z.2,z.1)
  left_inv z := by
    apply Prod.ext
    · simpa only [neg_neg] using q.nextConjugation_neg_cancel d (-z.2) z.1
    · rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · exact q.nextConjugation_neg_cancel d z.1 z.2
  continuous_toFun := (q.continuous_conjugationSkew d).comp continuous_swap
  continuous_invFun := by
    have h := (q.continuous_conjugationSkew d).comp (continuous_fst.neg.prodMk continuous_snd)
    exact h.snd.prodMk continuous_fst

lemma rootOrderCoordinates_param (d : ℕ) (q : InitialRootStep (d+1))
    (z : positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) :
    q.rootBeforeRemaining d (q.rootOrderCoordinates d z) = q.remainingBeforeRoot d z := by
  change Matrix.SpecialLinearGroup.transvection q.distinct z.2 *
      (Matrix.SpecialLinearGroup.transvection q.distinct (-z.2) * z.1.val *
        Matrix.SpecialLinearGroup.transvection q.distinct z.2) =
    z.1.val * Matrix.SpecialLinearGroup.transvection q.distinct z.2
  rw [←Matrix.SpecialLinearGroup.transvection_inv]
  group

end InitialRootStep
end DukePrimeDegree

end

end OAI
