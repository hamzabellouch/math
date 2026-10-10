import OAI.Geometry.Relativity.CKS.SchwarzschildConnection

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma maximum_radius_tangent {f : E2 → E3} {y : E2}
    (hf : DifferentiableAt ℝ f y) (hm : IsLocalMax (fun z => ‖f z‖^2) y) (a : E2) :
    ⟪radialUnit (f y),fderiv ℝ f y a⟫_ℝ = 0 := by
  have hh := congrArg (fun L : E2 →L[ℝ] ℝ => L a) (hm.hasFDerivAt_eq_zero hf.hasFDerivAt.norm_sq)
  have hzero : ⟪f y,fderiv ℝ f y a⟫_ℝ = 0 := by
    simp only [smul_apply,ContinuousLinearMap.comp_apply,
      zero_apply] at hh
    change (2:ℕ) • ⟪f y,fderiv ℝ f y a⟫_ℝ = 0 at hh
    simpa only [two_nsmul,add_self_eq_zero] using hh
  simp only [radialUnit,real_inner_smul_left,hzero,mul_zero]

lemma tangent_range (x : E3) (hx : x ≠ 0) (T : E2 →L[ℝ] E3)
    (hT : Function.Injective T) (ht : ∀ a, ⟪radialUnit x,T a⟫_ℝ = 0) :
    LinearMap.range T.toLinearMap = (ℝ ∙ radialUnit x)ᗮ := by
  have hn : radialUnit x ≠ 0 := norm_ne_zero_iff.mp (by rw [norm_radialUnit hx]; norm_num)
  let : Fact (Module.finrank ℝ E3 = 2+1) := ⟨by simp [E3]⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro v ⟨a,rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (ht a)
  · rw [LinearMap.finrank_range_of_inj hT,Submodule.finrank_orthogonal_span_singleton (n := 2) hn]
    simp [E2]

lemma normal_radial_at_tangent {m : ℝ} (hm : 0 < m) {x : E3} (hx : 2*m ≤ ‖x‖)
    (T : E2 →L[ℝ] E3) (hT : Function.Injective T)
    (ht : ∀ a, ⟪radialUnit x,T a⟫_ℝ = 0) (N : E3)
    (hunit : cartMetric m x N N = 1) (horth : ∀ a, cartMetric m x N (T a) = 0) :
    N = radialNormal m x ∨ N = -radialNormal m x := by
  have hxn : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hx)
  let q := ⟪radialUnit x,N⟫_ℝ
  let d := N-q•radialUnit x
  have hd : ⟪radialUnit x,d⟫_ℝ = 0 := by
    simp only [d,inner_sub_right,inner_smul_right,radialUnit_inner_self hxn,mul_one]
    exact sub_self _
  have hdr : d ∈ LinearMap.range T.toLinearMap := by
    rw [tangent_range x hxn T hT ht]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hd
  obtain ⟨a,ha⟩ := hdr
  change T a = d at ha
  have ho : ⟪N,d⟫_ℝ = 0 := by
    have hh := horth a
    change cartMetric m x N (T a) = 0 at hh
    rw [ha,cartMetric_apply,hd] at hh
    simpa using hh
  have hdd : ⟪d,d⟫_ℝ = 0 := by
    change ⟪N-q•radialUnit x,d⟫_ℝ = 0
    rw [inner_sub_left,real_inner_smul_left,ho,hd]
    ring
  have he : N = q•radialUnit x := sub_eq_zero.mp (inner_self_eq_zero.mp hdd)
  have hu := lapse_pos hm hx
  have hu2 := lapseSquared_pos hm hx
  have hq : q^2 = (lapse m ‖x‖)^2 := by
    rw [he,cartMetric_apply] at hunit
    simp only [real_inner_smul_left,inner_smul_right,radialUnit_inner_self hxn,mul_one] at hunit
    rw [← lapse_sq hm hx] at hunit
    field_simp at hunit
    nlinarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hq) with hh | hh
  · left
    rw [he,hh]
    rfl
  · right
    rw [he,hh]
    simp [radialNormal,neg_smul]

end CKSSchwarzschild

end

end OAI
