import OAI.Analysis.KadisonKastler.PoissonNormContinuity
import OAI.Analysis.KadisonKastler.PoissonBoundaryLimit

namespace OAI

/-! # Operator norm continuity of the demodulated boundary comparison -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem continuous_poissonBoundaryApprox
    (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    {r : ℝ} (hr : 0 < r) : Continuous (fun t => poissonBoundaryApprox W hW t r) := by
  unfold poissonBoundaryApprox
  apply Continuous.smul (M := ℂ) (X := H →L[ℂ] H)
    (f := fun t : ℝ => (Real.exp r : ℂ) * star (Circle.exp t : ℂ))
    (g := fun t => poissonVectorAverage (modulatedUnitaryField W)
      (modulatedUnitaryField_continuous W hW) 1 (norm_modulatedUnitaryField_le_one W) t r)
  · exact continuous_const.mul
      (continuous_subtype_val.comp Circle.exp.continuous).star
  · exact continuous_poissonVectorAverage (modulatedUnitaryField W)
      (modulatedUnitaryField_continuous W hW) zero_le_one
      (norm_modulatedUnitaryField_le_one W) hr

theorem continuous_poissonBoundaryQuotient
    (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    {r : ℝ} (hr : 0 < r) : Continuous (fun t => poissonBoundaryQuotient W hW t r) :=
  (continuous_poissonBoundaryApprox W hW hr).mul continuous_const

end

end KadisonKastler

end OAI
