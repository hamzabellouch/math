import OAI.Geometry.SurfaceImmersion.Geometry.CompactFixedJet

namespace OAI

/-! Quantitative local injectivity for a two-dimensional map. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma near_plane_equiv_derivative_injOn (L : Base ≃L[ℝ] Base)
    {g : Base → Base} {S : Set Base} (hg : ∀ x ∈ S, DifferentiableAt ℝ g x)
    (hS : Convex ℝ S) {c : ℝ}
    (hsmall : ‖L.symm.toContinuousLinearMap‖*c < 1)
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
      rw [←heq,map_sub]
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

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
