import OAI.Analysis.KadisonKastler.GaussianKMSBoundary
import OAI.Analysis.KadisonKastler.EntireRealUniqueness

namespace OAI

/-! # The imaginary KMS shift for all points of an entire Gaussian orbit -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (Ω : H)
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem gaussianStateAverage_kms_shift
    (hnormal : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hkms : VectorStateKMS M Ω U) (a : H →L[ℂ] H) (ha : a ∈ M)
    (b : H →L[ℂ] H) (hb : b ∈ M) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    productVectorState Ω (gaussianStateAverage U hU a r hr (z + Complex.I) * b) =
      productVectorState Ω (b * gaussianStateAverage U hU a r hr z) := by
  have hl := (gaussianStateAverage_coefficient_differentiable U hU a r hr (b Ω) Ω).comp
    (show Differentiable ℂ (fun w : ℂ => w + Complex.I) from differentiable_id.add_const _)
  have hr' := (innerSL ℂ Ω).differentiable.comp
    (b.differentiable.comp (gaussianStateAverage_vector_differentiable U hU a r hr Ω))
  have he := entire_eq_of_real hl hr' (fun t =>
    gaussianStateAverage_kms_boundary Ω U hU hnormal hkms a ha b hb r hr t)
  exact congrFun he z

end

end KadisonKastler

end OAI
