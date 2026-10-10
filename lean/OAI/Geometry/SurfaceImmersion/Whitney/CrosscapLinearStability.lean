import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceDirectionJet

namespace OAI

/-! A uniform local injectivity estimate for a nondegenerate direction map.
It will allow the quadratic jet to replace the original map near a crosscap. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance : ContinuousSMul ℝ (Base × ℝ) := Prod.continuousSMul

lemma near_equiv_derivative_injOn (L : (Base × ℝ) ≃L[ℝ] ProjectionTarget 3)
    {g : Base × ℝ → ProjectionTarget 3} {S : Set (Base × ℝ)}
    (hg : ∀ x ∈ S, DifferentiableAt ℝ g x) (hS : Convex ℝ S)
    {c : ℝ} (_hc : 0 ≤ c) (hsmall : ‖L.symm.toContinuousLinearMap‖*c < 1)
    (hbound : ∀ x ∈ S, ‖fderiv ℝ g x-L.toContinuousLinearMap‖ ≤ c) :
    S.InjOn g := by
  intro x hx y hy heq
  have hd : ∀ z ∈ S, DifferentiableAt ℝ (fun z => g z-L z) z :=
    fun z hz => (hg z hz).sub L.differentiableAt
  have hb : ∀ z ∈ S, ‖fderiv ℝ (fun z => g z-L z) z‖ ≤ c := by
    intro z hz
    rw [fderiv_fun_sub (hg z hz) L.differentiableAt,L.fderiv]
    exact hbound z hz
  have herr := hS.norm_image_sub_le_of_norm_fderiv_le hd hb hx hy
  have hL : ‖L (y-x)‖ ≤ c*‖y-x‖ := by
    have he : (g y-L y)-(g x-L x) = -L (y-x) := by
      rw [← heq,map_sub]
      abel
    rw [he,norm_neg] at herr
    exact herr
  have hback : ‖y-x‖ ≤ ‖L.symm.toContinuousLinearMap‖*‖L (y-x)‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe,L.symm_apply_apply] using
      L.symm.toContinuousLinearMap.le_opNorm (L (y-x))
  have hn : ‖y-x‖ = 0 := by
    have hh := hback.trans (mul_le_mul_of_nonneg_left hL (norm_nonneg _))
    nlinarith [norm_nonneg (y-x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

theorem local_linearization_stability_on
    {f : Base × ℝ → ProjectionTarget 3} (hf : ContDiff ℝ ∞ f) (z : Base × ℝ)
    (hreg : Function.Bijective (fderiv ℝ f z)) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
      ∀ S : Set (Base × ℝ), Convex ℝ S → S ⊆ Metric.ball z r →
      ∀ g : Base × ℝ → ProjectionTarget 3, ContDiff ℝ ∞ g →
        (∀ x ∈ S, ‖fderiv ℝ g x-fderiv ℝ f x‖ ≤ ε) → S.InjOn g := by
  let L := ContinuousLinearEquiv.ofBijective (fderiv ℝ f z)
    (LinearMap.ker_eq_bot.mpr hreg.1) (LinearMap.range_eq_top.mpr hreg.2)
  let c := (2*(‖L.symm.toContinuousLinearMap‖+1))⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall : ‖L.symm.toContinuousLinearMap‖*c < 1 := by
    dsimp [c]
    rw [← div_eq_mul_inv]
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith [norm_nonneg L.symm.toContinuousLinearMap]
  have hcont : ContinuousAt (fderiv ℝ f) z := (hf.continuous_fderiv (by simp)).continuousAt
  have hevent : ∀ᶠ x in 𝓝 z, ‖fderiv ℝ f x-fderiv ℝ f z‖ < c/2 := by
    simpa only [Metric.mem_ball,dist_eq_norm] using
      hcont.eventually (Metric.ball_mem_nhds _ (half_pos hc))
  obtain ⟨r,hr,hclose⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨r,c/2,hr,half_pos hc,?_⟩
  intro S hS hsub g hg hnear
  apply near_equiv_derivative_injOn L
    (fun x _ => hg.differentiable (by simp) x) hS hc.le hsmall
  intro x hx
  have hx' : dist x z < r := hsub hx
  change ‖fderiv ℝ g x-fderiv ℝ f z‖ ≤ c
  calc
    _ ≤ ‖fderiv ℝ g x-fderiv ℝ f x‖+‖fderiv ℝ f x-fderiv ℝ f z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ c/2+c/2 := add_le_add (hnear x hx) (hclose hx').le
    _ = c := by ring


theorem local_linearization_stability
    {f : Base × ℝ → ProjectionTarget 3} (hf : ContDiff ℝ ∞ f) (z : Base × ℝ)
    (hreg : Function.Bijective (fderiv ℝ f z)) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
      ∀ g : Base × ℝ → ProjectionTarget 3, ContDiff ℝ ∞ g →
        (∀ x ∈ Metric.ball z r, ‖fderiv ℝ g x-fderiv ℝ f x‖ ≤ ε) →
        (Metric.ball z r).InjOn g := by
  obtain ⟨r,ε,hr,hε,h⟩ := local_linearization_stability_on hf z hreg
  exact ⟨r,ε,hr,hε,h _ (convex_ball z r) Subset.rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
