import OAI.Geometry.Perimeter.Regularity.SingleGraph

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

def graphTangentLinear (v w : Euc n) : normalPlane v →L[ℝ] ℝ :=
  (-(inner ℝ w v)⁻¹) • ((innerSL ℝ w).comp (normalPlane v).subtypeL)

@[simp] theorem graphTangentLinear_apply (v w : Euc n) (y : normalPlane v) :
    graphTangentLinear v w y= -(inner ℝ w v)⁻¹ * inner ℝ w (y:Euc n) := rfl

theorem inner_near_unit_lower {v w : Euc n} (hv : ‖v‖=1) (hwv : ‖w-v‖≤1/2) :
    1/2 ≤ inner ℝ w v := by
  have hh := abs_real_inner_le_norm (w-v) v
  rw [inner_sub_left,real_inner_self_eq_norm_sq,hv,mul_one] at hh
  norm_num only [one_pow] at hh
  have hlo := (abs_le.mp hh).1
  linarith

theorem graph_tangent_remainder {E : Set (Euc n)} {v w : Euc n} (hv : ‖v‖=1)
    {f : normalPlane v → ℝ} {y z : normalPlane v} {C q : ℝ} {j : ℕ}
    (hwv : ‖w-v‖≤1/2)
    (hzS : (z:Euc n)+f z•v∈perimeterSupport E)
    (hlip : |f z-f y|≤‖z-y‖) (hzq : ‖z-y‖≤q^j)
    (htan : ∀ x, x∈perimeterSupport E →
      ‖x-((y:Euc n)+f y•v)‖≤2*q^j →
      |inner ℝ w (x-((y:Euc n)+f y•v))|≤C*(1/2)^j*‖x-((y:Euc n)+f y•v)‖)
    (hC : 0≤C) :
    |f z-f y-graphTangentLinear v w (z-y)|≤4*C*(1/2)^j*‖z-y‖ := by
  let d := inner ℝ w v
  have hd : 1/2≤d := inner_near_unit_lower hv hwv
  have hdp : 0<d := by linarith
  have hnorm := fiber_chord_norm hv z y (f z) (f y)
  have hn : ‖((z:Euc n)+f z•v)-((y:Euc n)+f y•v)‖≤2*‖z-y‖ := by linarith
  have hh := htan _ hzS (hn.trans (mul_le_mul_of_nonneg_left hzq (by norm_num)))
  have he : inner ℝ w (((z:Euc n)+f z•v)-((y:Euc n)+f y•v))=
      d*(f z-f y-graphTangentLinear v w (z-y)) := by
    simp only [graphTangentLinear_apply,Submodule.coe_sub,inner_sub_right,inner_add_right,
      real_inner_smul_right]
    dsimp [d]
    field_simp [show inner ℝ w v ≠ 0 from hdp.ne']
    ring
  rw [he,abs_mul,abs_of_pos hdp] at hh
  have hm := mul_le_mul_of_nonneg_left hn (show 0≤C*(1/2:ℝ)^j by positivity)
  nlinarith [abs_nonneg (f z-f y-graphTangentLinear v w (z-y))]

theorem hasFDerivAt_of_geometric_remainder {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : V → ℝ} {D : V →L[ℝ] ℝ} {U : Set V} (hU : IsOpen U)
    {y : V} (hy : y∈U) {q C : ℝ} (hq : 0<q)
    (hrem : ∀ j z, z∈U → ‖z-y‖≤q^j →
      |f z-f y-D (z-y)|≤C*(1/2)^j*‖z-y‖) : HasFDerivAt f D y := by
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  have ht : Tendsto (fun j : ℕ ↦ C*(1/2:ℝ)^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).const_mul C
  obtain ⟨j,hj⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  filter_upwards [hU.mem_nhds hy,Metric.ball_mem_nhds y (pow_pos hq j)] with z hz hzB
  have hzy : ‖z-y‖≤q^j := by
    have hh : ‖z-y‖<q^j := by simpa only [Metric.mem_ball,dist_eq_norm] using hzB
    exact hh.le
  exact (show ‖f z-f y-D (z-y)‖≤C*(1/2)^j*‖z-y‖ by
    simpa only [Real.norm_eq_abs] using hrem j z hz hzy).trans
      (mul_le_mul_of_nonneg_right hj.le (norm_nonneg _))

end RPISingularHarnack

end

end OAI
