import OAI.Geometry.Perimeter.Regularity.EllipticLocality

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack

theorem four_point_linear_bound {t e d A B X X' Y Y' : ℝ} (ht : 0<t)
    (hx : |X'-X-t*A|≤e*t) (hy : |Y'-Y-t*B|≤e*t)
    (hxy : |X-Y|≤d) (hxy' : |X'-Y'|≤d) :
    |A-B|≤2*d/t+2*e := by
  have he : t*(A-B)= -(X'-X-t*A)+(Y'-Y-t*B)+(X'-Y')-(X-Y) := by ring
  have hh : t*|A-B|≤e*t+e*t+d+d := by
    calc
      t*|A-B| = |t*(A-B)| := by rw [abs_mul,abs_of_pos ht]
      _ = |-(X'-X-t*A)+(Y'-Y-t*B)+(X'-Y')-(X-Y)| := by rw [he]
      _ ≤ |X'-X-t*A|+|Y'-Y-t*B|+|X'-Y'|+|X-Y| := by
        have h1 := abs_add_le (-(X'-X-t*A)) (Y'-Y-t*B)
        have h2 := abs_add_le (-(X'-X-t*A)+(Y'-Y-t*B)) (X'-Y')
        have h3 := abs_add_le (-(X'-X-t*A)+(Y'-Y-t*B)+(X'-Y')) (-(X-Y))
        simp only [abs_neg,← sub_eq_add_neg] at h1 h2 h3
        linarith
      _ ≤ e*t+e*t+d+d := by linarith
  have heq : (2*d/t+2*e)*t=2*d+2*e*t := by field_simp
  apply (le_of_mul_le_mul_right ?_ ht)
  rw [heq]
  nlinarith

theorem continuous_derivative_of_geometric_remainder {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {D : V → V →L[ℝ] ℝ} {U : Set V} (hU : IsOpen U)
    {q C : ℝ} (hq : 0<q)
    (hlip : ∀ x∈U, ∀ y∈U, |f x-f y|≤‖x-y‖)
    (hrem : ∀ j x, x∈U → ∀ z, z∈U → ‖z-x‖≤q^j →
      |f z-f x-D x (z-x)|≤C*(1/2)^j*‖z-x‖) :
    ∀ y∈U, ContinuousAt D y := by
  intro y hy
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp hU y hy
  have hp : Tendsto (fun j : ℕ ↦ C*(1/2:ℝ)^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).const_mul C
  obtain ⟨j,hj⟩ := (hp.eventually (gt_mem_nhds (by positivity : 0<ε/8))).exists
  let t := min (q^j) (r/4)
  have ht : 0<t := lt_min (pow_pos hq _) (by positivity)
  have htq : t≤q^j := min_le_left _ _
  have htr : t≤r/4 := min_le_right _ _
  let δ := min (r/4) (ε*t/16)
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  refine ⟨δ,hδ,fun x hx ↦ ?_⟩
  have hxy : ‖x-y‖<δ := by simpa only [dist_eq_norm] using hx
  have hxyr : ‖x-y‖<r/4 := hxy.trans_le (min_le_left _ _)
  have hxyε : ‖x-y‖<ε*t/16 := hxy.trans_le (min_le_right _ _)
  have hxU : x∈U := hrU (by simpa only [Metric.mem_ball,dist_eq_norm] using (by linarith : ‖x-y‖<r))
  have hnorm : ‖D x-D y‖≤ε/2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro u hu
    have hyu : y+t•u∈U := by
      apply hrU
      simp only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg ht.le,hu,mul_one]
      linarith
    have hxu : x+t•u∈U := by
      apply hrU
      rw [Metric.mem_ball,dist_eq_norm]
      have he : x+t•u-y=(x-y)+t•u := by abel
      rw [he]
      have hh := norm_add_le (x-y) (t•u)
      rw [norm_smul,Real.norm_of_nonneg ht.le,hu,mul_one] at hh
      linarith
    have hnx : ‖(x+t•u)-x‖=t := by simp [norm_smul,Real.norm_of_nonneg ht.le,hu]
    have hny : ‖(y+t•u)-y‖=t := by simp [norm_smul,Real.norm_of_nonneg ht.le,hu]
    have hxR := hrem j x hxU (x+t•u) hxu (by rw [hnx]; exact htq)
    have hyR := hrem j y hy (y+t•u) hyu (by rw [hny]; exact htq)
    simp only [add_sub_cancel_left,map_smul,smul_eq_mul] at hxR hyR
    rw [norm_smul,Real.norm_of_nonneg ht.le,hu,mul_one] at hxR hyR
    have hsh : ‖(x+t•u)-(y+t•u)‖=‖x-y‖ := by congr 1; abel
    have hb := four_point_linear_bound ht hxR hyR (hlip x hxU y hy)
      (by simpa only [hsh] using hlip (x+t•u) hxu (y+t•u) hyu)
    change ‖D x u-D y u‖≤ε/2
    rw [Real.norm_eq_abs]
    apply hb.trans
    have hd : 2*‖x-y‖/t<ε/8 := by
      apply (div_lt_iff₀ ht).mpr
      nlinarith
    linarith
  rw [dist_eq_norm]
  exact hnorm.trans_lt (by linarith)

end RPISingularHarnack

end

end OAI
