import OAI.Analysis.CircleDomains.Reflection.PrincipalComplexBeltrami

namespace OAI

/-! Retain the actual smooth coefficient convergence together with the
principal homeomorphism limit. It comes from the same bounded mollification
used in constructing the principal solution. -/
open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma exists_principal_complex_coefficient_data (μ : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) {k R : ℝ}
    (hk : 0≤k) (hk1 : k<1) (hb : ∀z,‖μ z‖≤k)
    (hs : ∀z,R≤‖z‖ → μ z=0) :
    ∃ (g : PlaneL2) (S : PrincipalSmoothApproximation g k R) (_L : PrincipalMapLimit S),
      (∀ᵐz ∂volume,g z=μ z*(1+beurling g z)) ∧
      ∀ᵐz ∂volume,Tendsto (fun n => S.coefficient n z) atTop (𝓝 (μ z)) := by
  obtain ⟨g,he⟩ := exists_compact_complex_beltrami_density μ hm hk hk1 hb hs
  obtain ⟨S,hc⟩ := exists_principal_smooth_approximation_with_coefficient μ hm hk hk1 hb hs g he
  let T := max (R+2) 1
  have hT : 0<T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨L⟩ := S.exists_principal_limit_data
    (exteriorCoefficientAreaTheorem planarSchoenflies unorientedFiniteCircleGreenFormula)
    hk hk1 hT (le_max_left _ _)
  exact ⟨g,S,L,he,hc⟩

end CircleDomainRigidity

end

end OAI
