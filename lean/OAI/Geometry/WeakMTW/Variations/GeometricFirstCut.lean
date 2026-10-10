import Mathlib
import OAI.Geometry.WeakMTW.Variations.FocalPole
import OAI.Geometry.WeakMTW.Variations.InwardHessianBound

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem nonconjugate_middle_of_unit_segment (hMTW : HasWeakMTW (n := n) (M := M))
    (x : M) {p e : TangentSpace (model n) x} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (he : inner ℝ e e = 1)
    (hseg : ∀ s ∈ Icc (-a) b, p+s•e ∈ minimizingDomain x)
    (hleft : Nonconjugate x (p+(-a)•e)) (hright : Nonconjugate x (p+b•e)) :
    Nonconjugate x p := by
  unfold Nonconjugate
  rw [injective_iff_map_eq_zero]
  intro k hk
  let A : ℝ → ℝ → LinearMap.BilinForm ℝ (TangentSpace (model n) x) :=
    fun h s => actionHessian x ((1-h)•(p+s•e))
  have hI (h : ℝ) (hh : 0 < h) (hh₁ : h < 1) (s : ℝ) (hs : s ∈ Icc (-a) b) :
      (1-h)•(p+s•e) ∈ injectivityDomain x :=
    strict_radial_mem_injectivity (hseg s hs) (by linarith) (by linarith)
  apply FirstCut.no_first_cut_kernel (A := A) ha hb he
    (fibre_kernel_perp_radial x (exp x p) (mem_chart_source (Model n) (exp x p)) hk)
  · intro h hh hh₁ s hs v w
    exact actionHessian_symmetric x (hI h hh hh₁ s hs) v w
  · intro h hh hh₁ s hs v
    have hrad := actionHessian_radial x (hI h hh hh₁ s hs) v
    rw [LinearMap.BilinForm.smul_right,inner_smul_right] at hrad
    have hne : (1-h) ≠ 0 := ne_of_gt (by linarith)
    have hr := mul_left_cancel₀ hne hrad
    change actionHessian x ((1-h)•(p+s•e)) (p+s•e) v = _
    rw [actionHessian_symmetric x (hI h hh hh₁ s hs)]
    exact hr.trans (real_inner_comm v (p+s•e)).symm
  · intro h hh hh₁ ξ hξ
    have hξη : inner ℝ ξ ((1-h)•e) = 0 := by rw [inner_smul_right,hξ,mul_zero]
    have hid (s : ℝ) : (1-h)•p+s•((1-h)•e) = (1-h)•(p+s•e) := by
      rw [smul_add,smul_smul,smul_smul,mul_comm s (1-h)]
    have hc := transverse_action_concave hMTW x ((1-h)•p) ξ ((1-h)•e) hξη
      (convex_Icc (-a) b) (fun s hs => (hid s).symm ▸ hI h hh hh₁ s hs)
    apply hc.congr
    intro s hs
    change actionHessianDiag x ((1-h)•p+s•((1-h)•e)) ξ =
      actionHessian x ((1-h)•(p+s•e)) ξ ξ
    rw [hid s,← actionHessian_diag x (hI h hh hh₁ s hs)]
  · intro ξ
    have hab : -a ≤ b := by linarith
    obtain ⟨L₀,δ₀,hδ₀,h₀⟩ := nonconjugate_inward_hessian_bound x (hseg (-a) ⟨le_rfl,hab⟩) hleft ξ
    obtain ⟨L₁,δ₁,hδ₁,h₁⟩ := nonconjugate_inward_hessian_bound x (hseg b ⟨hab,le_rfl⟩) hright ξ
    refine ⟨max L₀ L₁,min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
    intro h hh hhδ
    constructor
    · exact (neg_le_neg (le_max_left _ _)).trans (h₀ h hh (lt_of_lt_of_le hhδ (min_le_left _ _)))
    · exact (neg_le_neg (le_max_right _ _)).trans (h₁ h hh (lt_of_lt_of_le hhδ (min_le_right _ _)))
  · intro ξ hξ
    exact actual_focal_trial_pole x ha hb hseg hk ξ hξ

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
