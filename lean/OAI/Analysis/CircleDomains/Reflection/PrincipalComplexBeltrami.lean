import OAI.Analysis.CircleDomains.Sobolev.PrincipalSmoothLimit
import OAI.Analysis.CircleDomains.Sobolev.ExteriorCoefficientAreaProof
import OAI.Analysis.CircleDomains.Topology.PlanarSchoenfliesProof
import OAI.Analysis.CircleDomains.Topology.FiniteCircleGreenProof

namespace OAI

/-! The compactly supported complex-coefficient principal solution used in
finite reflection constructions. The L2 density is solved by the actual
Beurling contraction and the homeomorphism is the strong smooth limit. -/
open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma exists_compact_complex_beltrami_density (μ : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) {k R : ℝ}
    (hk : 0≤k) (hk1 : k<1) (hb : ∀z,‖μ z‖≤k)
    (hs : ∀z,R≤‖z‖ → μ z=0) :
    ∃g : PlaneL2, ∀ᵐ z ∂volume,g z=μ z*(1+beurling g z) := by
  let hμ := compact_coefficient_memLp hm (isCompact_closedBall 0 R) hk hb
    (fun z hz => hs z (le_of_lt (by simpa only [mem_closedBall,dist_zero_right,not_le] using hz)))
  obtain ⟨g,he,_,_⟩ := solve_beltrami_l2 μ hm hk hk1 (.of_forall hb) (hμ.toLp μ)
  refine ⟨g,?_⟩
  have hea := Lp.ext_iff.mp he
  filter_upwards [hea,Lp.coeFn_sub g (multiplier μ hm hk (.of_forall hb) (beurling g)),
    multiplier_ae μ hm hk (.of_forall hb) (beurling g),hμ.coeFn_toLp] with z hz hsub hmul hval
  simp only [Pi.sub_apply] at hsub
  rw [hsub,hmul,hval] at hz
  linear_combination hz

lemma exists_principal_complex_beltrami_limit (μ : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) {k R : ℝ}
    (hk : 0≤k) (hk1 : k<1) (hb : ∀z,‖μ z‖≤k)
    (hs : ∀z,R≤‖z‖ → μ z=0) :
    ∃(g : PlaneL2) (H : ℂ ≃ₜ ℂ),
      (∀ᵐ z ∂volume,g z=μ z*(1+beurling g z)) ∧
      Tendsto (fun z => H z-z) (Bornology.cobounded ℂ) (𝓝 0) ∧
      ∀(v : ℂ) (φ : SchwartzMap ℂ ℂ),HasCompactSupport (φ : ℂ → ℂ) →
        (∫z,H z*fderiv ℝ (φ : ℂ → ℂ) z v)=
          -(∫z,(v+principalDirectionalCorrection g v z)*φ z) := by
  obtain ⟨g,he⟩ := exists_compact_complex_beltrami_density μ hm hk hk1 hb hs
  obtain ⟨S⟩ := exists_principal_smooth_approximation μ hm hk hk1 hb hs g he
  let T := max (R+2) 1
  have hT : 0<T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨H,hp,hw⟩ := S.exists_principal_homeomorph_limit
    (exteriorCoefficientAreaTheorem planarSchoenflies unorientedFiniteCircleGreenFormula)
    hk hk1 hT (le_max_left _ _)
  exact ⟨g,H,he,hp,hw⟩

lemma exists_principal_complex_beltrami_data (μ : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) {k R : ℝ}
    (hk : 0≤k) (hk1 : k<1) (hb : ∀z,‖μ z‖≤k)
    (hs : ∀z,R≤‖z‖ → μ z=0) :
    ∃ (g : PlaneL2) (S : PrincipalSmoothApproximation g k R) (_L : PrincipalMapLimit S),
      ∀ᵐz ∂volume,g z=μ z*(1+beurling g z) := by
  obtain ⟨g,he⟩ := exists_compact_complex_beltrami_density μ hm hk hk1 hb hs
  obtain ⟨S⟩ := exists_principal_smooth_approximation μ hm hk hk1 hb hs g he
  let T := max (R+2) 1
  have hT : 0<T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨L⟩ := S.exists_principal_limit_data
    (exteriorCoefficientAreaTheorem planarSchoenflies unorientedFiniteCircleGreenFormula)
    hk hk1 hT (le_max_left _ _)
  exact ⟨g,S,L,he⟩

end CircleDomainRigidity

end

end OAI
