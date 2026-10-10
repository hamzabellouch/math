import OAI.Analysis.HenonEmden.LayerRecovery

namespace OAI

universe uE

section WeightedEndpoints

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.WeightedLayers

lemma rpow_annulus_bound {r : ℝ} (hr : r ∈ Icc (1:ℝ) 2) (s : ℝ) : r^s ≤ 2^|s| := by
  have hr0 : 0 ≤ r := by linarith [hr.1]
  calc
    _ ≤ r^|s| := Real.rpow_le_rpow_of_exponent_le hr.1 (le_abs_self s)
    _ ≤ _ := Real.rpow_le_rpow hr0 hr.2 (abs_nonneg s)

lemma rpow_annulus_lipschitz {r r' : ℝ} (hr : r ∈ Icc (1:ℝ) 2)
    (hr' : r' ∈ Icc (1:ℝ) 2) (s : ℝ) :
    |r'^s-r^s| ≤ (|s| *2^|s-1|)*|r'-r| := by
  have hd (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) := Real.hasStrictDerivAt_rpow_const_of_ne
    (ne_of_gt (show 0 < x by linarith [hx.1])) s |>.hasDerivAt
  have hh := (convex_Icc (1:ℝ) 2).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hd x hx).hasDerivWithinAt)
    (show ∀ x ∈ Icc (1:ℝ) 2, ‖s*x^(s-1)‖ ≤ |s| *2^|s-1| from by
      intro x hx
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1]) _)]
      exact mul_le_mul_of_nonneg_left (rpow_annulus_bound hx (s-1)) (abs_nonneg s)) hr hr'
  simpa only [Real.norm_eq_abs] using hh

lemma rpow_annulus_relative {r r' : ℝ} (hr : r ∈ Icc (1:ℝ) 2)
    (hr' : r' ∈ Icc (1:ℝ) 2) (s : ℝ) :
    |r'^s-r^s| ≤ (|s| *2^|s-1| *2^|s|)*|r'-r| *r^s := by
  have hr0 : 0 < r := by linarith [hr.1]
  have hp : 1 ≤ 2^|s| *r^s := by
    have hh := mul_le_mul_of_nonneg_right (rpow_annulus_bound hr (-s)) (Real.rpow_nonneg hr0.le s)
    rw [abs_neg,← Real.rpow_add hr0,neg_add_cancel,Real.rpow_zero] at hh
    exact hh
  calc
    _ ≤ (|s| *2^|s-1|)*|r'-r| := rpow_annulus_lipschitz hr hr' s
    _ ≤ (|s| *2^|s-1|)*|r'-r| *(2^|s| *r^s) := by
      exact le_mul_of_one_le_right (by positivity) hp
    _ = _ := by ring

lemma layer_root_radial {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) (q B : ℝ) :
    (t/r^B)^(1/q) = t^(1/q)*r^(-B/q) := by
  rw [Real.div_rpow ht (Real.rpow_nonneg hr.le _),← Real.rpow_mul hr.le,
    show -B/q = -(B*(1/q)) by ring,Real.rpow_neg hr.le,div_eq_mul_inv]

lemma source_level_root {n : ℕ} {u : Space n → ℝ} {q B t : ℝ}
    (hq : 0 < q) (hu : ∀ x, 0 < u x) {x : Space n} (hx : x ≠ 0)
    (ht : source u q B x = t) : u x = (t/‖x‖^B)^(1/q) := by
  rw [← ht,source_off_zero _ _ _ hx,mul_div_cancel_left₀ _
    (ne_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _)),← Real.rpow_mul (hu x).le]
  have he : q*(1/q) = 1 := by field_simp
  rw [he,Real.rpow_one]

lemma radial_layer_endpoint_error {E : Type uE} [NormedAddCommGroup E]
    {x y : E} (hx : ‖x‖ ∈ Icc (1:ℝ) 2) (hy : ‖y‖ ∈ Icc (1:ℝ) 2)
    {q B t : ℝ} (ht : 0 ≤ t) :
    |(t/‖y‖^B)^(1/q)-(t/‖x‖^B)^(1/q)| ≤
      (|-B/q| *2^|-B/q-1| *2^|-B/q|)*dist y x*(t/‖x‖^B)^(1/q) := by
  have hx0 : 0 < ‖x‖ := by linarith [hx.1]
  have hy0 : 0 < ‖y‖ := by linarith [hy.1]
  rw [layer_root_radial hx0 ht,layer_root_radial hy0 ht,← mul_sub,abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ht _)]
  have hh := rpow_annulus_relative hx hy (-B/q)
  have hh' := hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le y x) (by positivity))
    (Real.rpow_nonneg hx0.le (-B/q)))
  calc
    _ ≤ t^(1/q)*((|-B/q| *2^|-B/q-1| *2^|-B/q|)*‖y-x‖*‖x‖^(-B/q)) :=
      mul_le_mul_of_nonneg_left hh' (Real.rpow_nonneg ht _)
    _ = _ := by rw [dist_eq_norm]; ring

lemma average_endpoint_error {a b τ ε : ℝ}
    (ha : |a-τ| ≤ ε) (hb : |b-τ| ≤ ε) : |(a+b)/2-τ| ≤ ε := by
  have hh := abs_add_le (a-τ) (b-τ)
  rw [show (a+b)/2-τ = ((a-τ)+(b-τ))/2 by ring,abs_div]
  norm_num
  linarith

end HenonLaneEmden.WeightedLayers
end
end WeightedEndpoints

end OAI
