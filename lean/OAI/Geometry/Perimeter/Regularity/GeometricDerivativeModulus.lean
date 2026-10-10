import OAI.Geometry.Perimeter.Regularity.UniformDerivativeContinuity

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack

 theorem geometricHolder_derivative_of_remainder {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {D : V → V →L[ℝ] ℝ} {U : Set V} (hU : IsOpen U)
    {q C : ℝ} (hq : 0<q) (hq1 : q ≤ 1) (hC : 0 ≤ C)
    (hlip : ∀ x∈U, ∀ y∈U, |f x-f y|≤‖x-y‖)
    (hrem : ∀ j x, x∈U → ∀ z, z∈U → ‖z-x‖≤q^j →
      |f z-f x-D x (z-x)|≤C*(1/2)^j*‖z-x‖)
    {p : V} (hp : p∈U) : GeometricHolderAt (q/2) D p := by
  obtain ⟨s,hs,hsU⟩ := Metric.isOpen_iff.mp hU p hp
  let r := min (s/4) 1
  have hr : 0<r := lt_min (by positivity) (by norm_num)
  have hrs : r ≤ s/4 := min_le_left _ _
  have hr1 : r ≤ 1 := min_le_right _ _
  refine ⟨r,2+2*C,hr,by positivity,fun j x hx y hy hxy ↦ ?_⟩
  let t := q^j*r
  have ht : 0<t := by dsimp [t]; positivity
  have htq : t ≤ q^j := by dsimp [t]; nlinarith [pow_pos hq j]
  have htr : t ≤ r := by dsimp [t]; nlinarith [pow_le_one₀ (n := j) hq.le hq1]
  have hxU : x∈U := hsU (Metric.ball_subset_ball (by linarith) hx)
  have hyU : y∈U := hsU (Metric.ball_subset_ball (by linarith) hy)
  have hshift (z : V) (hz : z∈Metric.ball p r) (u : V) (hu : ‖u‖=1) : z+t•u∈U := by
    apply hsU
    rw [Metric.mem_ball,dist_eq_norm]
    have he : z+t•u-p=(z-p)+t•u := by abel
    rw [he]
    have hh := norm_add_le (z-p) (t•u)
    rw [norm_smul,Real.norm_of_nonneg ht.le,hu,mul_one] at hh
    have hz' := Metric.mem_ball.mp hz
    rw [dist_eq_norm] at hz'
    linarith
  rw [dist_eq_norm]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro u hu
  have hxu := hshift x hx u hu
  have hyu := hshift y hy u hu
  have hnx : ‖(x+t•u)-x‖=t := by simp [norm_smul,Real.norm_of_nonneg ht.le,hu]
  have hny : ‖(y+t•u)-y‖=t := by simp [norm_smul,Real.norm_of_nonneg ht.le,hu]
  have hxR := hrem j x hxU (x+t•u) hxu (by rw [hnx]; exact htq)
  have hyR := hrem j y hyU (y+t•u) hyu (by rw [hny]; exact htq)
  simp only [add_sub_cancel_left,map_smul,smul_eq_mul] at hxR hyR
  rw [norm_smul,Real.norm_of_nonneg ht.le,hu,mul_one] at hxR hyR
  have hsh : ‖(x+t•u)-(y+t•u)‖=‖x-y‖ := by congr 1; abel
  have hb := four_point_linear_bound ht hxR hyR (hlip x hxU y hyU)
    (by simpa only [hsh] using hlip (x+t•u) hxu (y+t•u) hyu)
  change ‖D x u-D y u‖ ≤ _
  rw [Real.norm_eq_abs]
  apply hb.trans
  have hd : ‖x-y‖ ≤ (1/2)^j*t := by
    rw [←dist_eq_norm]
    have he : (q/2)^j*r=(1/2:ℝ)^j*t := by
      dsimp [t]
      rw [show q/2=(1/2:ℝ)*q by ring,mul_pow]
      ring
    rwa [←he]
  have hd' : 2*‖x-y‖/t ≤ 2*(1/2)^j := by
    apply (div_le_iff₀ ht).mpr
    nlinarith
  nlinarith

end RPISingularHarnack

end

end OAI
