import OAI.Analysis.KadisonKastler.GaussianStateAnalytic
import OAI.Analysis.KadisonKastler.GaussianStateCovariance
import OAI.Analysis.KadisonKastler.StripBoundaryUniqueness
import OAI.Analysis.KadisonKastler.ModularStateAction

namespace OAI

/-! # The KMS identity on concrete entire Gaussian elements -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (Ω : H)
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem gaussianStateAverage_kms_boundary
    (hnormal : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hkms : VectorStateKMS M Ω U) (a : H →L[ℂ] H) (ha : a ∈ M)
    (b : H →L[ℂ] H) (hb : b ∈ M) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    productVectorState Ω (gaussianStateAverage U hU a r hr ((t : ℂ) + Complex.I) * b) =
      productVectorState Ω (b * gaussianStateAverage U hU a r hr t) := by
  let A := gaussianStateAverage U hU a r hr
  let f : ℂ → ℂ := fun z => productVectorState Ω (A z * b)
  have hfd : Differentiable ℂ f :=
    gaussianStateAverage_coefficient_differentiable U hU a r hr (b Ω) Ω
  obtain ⟨g, hgc, hgd, _, hlo, hhi⟩ := hkms (A 0)
    (gaussianStateAverage_mem U hU M hnormal a ha r hr 0) b hb
  have hreal (s : ℝ) : g s = f s := by
    rw [hlo]
    dsimp [f, A]
    rw [gaussianStateAverage_covariance, zero_add]
  have he := strip_eq_of_lower_boundary hgc hgd hfd.continuous.continuousOn
    hfd.differentiableOn hreal ((t : ℂ) + Complex.I) (by simp) (by simp)
  change f ((t : ℂ) + Complex.I) = _
  rw [← he, hhi]
  dsimp [A]
  rw [gaussianStateAverage_covariance, zero_add]

end

end KadisonKastler

end OAI
