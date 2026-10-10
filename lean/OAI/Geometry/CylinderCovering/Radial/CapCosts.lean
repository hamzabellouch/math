import OAI.Geometry.CylinderCovering.Radial.CapsDefinitions
import OAI.Geometry.CylinderCovering.Angular.Taylor

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace CylinderCovering.RadialCaps

theorem H_nonneg (r : ℝ) : 0 ≤ H r := by unfold H; positivity

theorem D0_nonneg (r : ℝ) : 0 ≤ D0 r := by unfold D0; positivity

theorem H_le_one {r : ℝ} (hr : r ∈ Icc (-1) 1) : H r ≤ 1 := by
  have hr2 : r ^ 2 ≤ 1 := by nlinarith [hr.1, hr.2]
  have hr4 : r ^ 4 ≤ 1 := by nlinarith [sq_nonneg (r ^ 2 - 1)]
  unfold H
  linarith

theorem D0_le_three {r : ℝ} (hr : r ∈ Icc (-1) 1) : D0 r ≤ 3 := by
  have hr2 : r ^ 2 ≤ 1 := by nlinarith [hr.1, hr.2]
  have hG0 : 0 ≤ G r := by unfold G; positivity
  have hG1 : G r ≤ 1 := by unfold G; linarith
  unfold D0
  nlinarith [sq_nonneg (G r - 1)]

theorem density_integral :
    (∫ r in (-1 : ℝ)..1, H r - D0 r / 4) = -1 / 30 := by
  have he : (fun r : ℝ => H r - D0 r / 4) =
      (fun r => (-1 / 16 : ℝ) + (-1 / 8) * r ^ 2 + (7 / 16) * r ^ 4) := by
    funext r
    unfold H D0 G
    ring
  rw [he, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun r : ℝ => (-1 / 16 : ℝ) + (-1 / 8) * r ^ 2)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun r : ℝ => (7 / 16 : ℝ) * r ^ 4)).intervalIntegrable _ _),
    intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous (fun r : ℝ => (-1 / 8 : ℝ) * r ^ 2)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  norm_num

theorem scalar_remainder {a D c ε : ℝ}
    (hc : 0 ≤ c) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 + c)
    (hD0 : 0 ≤ D) (hD1 : D ≤ 3) (hsmall : 4 * (c + 2) * ε ^ 2 ≤ 1) :
    |(1 + ε ^ 2 * a) ^ 2 / (2 * Real.sqrt (1 + ε ^ 2 * D)) -
      (1 / 2 + ε ^ 2 * (a - D / 4))| ≤ 12 * (c + 2) ^ 2 * ε ^ 4 := by
  let S : ℝ := 4 * (c + 2)
  have hS : 0 < S := by dsimp [S]; linarith
  have hS0 := le_of_lt hS
  have hz : 0 ≤ S * ε ^ 2 := mul_nonneg hS0 (sq_nonneg ε)
  have ha : a / (2 * S) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * S)).2
    dsimp [S]
    linarith
  have hD : D / S ≤ 1 := by
    apply (div_le_iff₀ hS).2
    dsimp [S]
    linarith
  have h := AngularTaylor.bounded_product_remainder hz hsmall
    (div_nonneg ha0 (by positivity)) ha (div_nonneg hD0 hS0) hD
  have hid : (1 + ε ^ 2 * a) ^ 2 / (2 * Real.sqrt (1 + ε ^ 2 * D)) -
      (1 / 2 + ε ^ 2 * (a - D / 4)) =
      2 * ((1 / 2 + (S * ε ^ 2) * (a / (2 * S))) ^ 2 /
        Real.sqrt (1 + (S * ε ^ 2) * (D / S)) -
        (1 / 4 + (S * ε ^ 2) * (a / (2 * S) - (D / S) / 8))) := by
    have hzD : S * ε ^ 2 * (D / S) = ε ^ 2 * D := by field_simp
    rw [hzD]
    field_simp
    ring
  rw [hid, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |(1 / 2 + (S * ε ^ 2) * (a / (2 * S))) ^ 2 /
        Real.sqrt (1 + S * ε ^ 2 * (D / S)) -
        (1 / 4 + (S * ε ^ 2) * (a / (2 * S) - D / S / 8))| ≤
        2 * ((47 / 128) * (S * ε ^ 2) ^ 2) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ 12 * (c + 2) ^ 2 * ε ^ 4 := by
      dsimp [S]
      nlinarith [mul_nonneg (sq_nonneg (c + 2)) (pow_nonneg (sq_nonneg ε) 2)]

theorem continuous_Q_integrand {R : ℝ → ℝ} (hR : Continuous R) (ε : ℝ) :
    Continuous (fun r => R r ^ 2 / (2 * Real.sqrt (1 + ε ^ 2 * D0 r))) := by
  apply (hR.pow 2).div
  · unfold D0 G
    fun_prop
  · intro r
    apply mul_ne_zero (by norm_num)
    apply ne_of_gt
    apply Real.sqrt_pos.2
    exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (sq_nonneg ε) (D0_nonneg r))

theorem padded_cost_remainder {b c ε : ℝ}
    (hb : 0 ≤ b) (hbc : b ≤ c) (hc : 0 ≤ c)
    (hsmall : 4 * (c + 2) * ε ^ 2 ≤ 1) :
    |Q (fun r => 1 + ε ^ 2 * (H r + b)) ε -
      (1 + (2 * b - 1 / 30) * ε ^ 2)| ≤ 24 * (c + 2) ^ 2 * ε ^ 4 := by
  let f : ℝ → ℝ := fun r => (1 + ε ^ 2 * (H r + b)) ^ 2 /
    (2 * Real.sqrt (1 + ε ^ 2 * D0 r))
  let g : ℝ → ℝ := fun r => 1 / 2 + ε ^ 2 * (H r - D0 r / 4) + ε ^ 2 * b
  have hf : Continuous f := continuous_Q_integrand (by unfold H; fun_prop) ε
  have hg : Continuous g := by dsimp [g]; unfold H D0 G; fun_prop
  have hgint : (∫ r in (-1 : ℝ)..1, g r) = 1 + (2 * b - 1 / 30) * ε ^ 2 := by
    dsimp [g]
    rw [intervalIntegral.integral_add
      ((by unfold H D0 G; fun_prop : Continuous (fun r : ℝ => 1 / 2 + ε ^ 2 * (H r - D0 r / 4))).intervalIntegrable _ _)
      intervalIntegrable_const,
      intervalIntegral.integral_add intervalIntegrable_const
        ((by unfold H D0 G; fun_prop : Continuous (fun r : ℝ => ε ^ 2 * (H r - D0 r / 4))).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, density_integral, intervalIntegral.integral_const,
      intervalIntegral.integral_const]
    norm_num
    ring
  have hbound : |∫ r in (-1 : ℝ)..1, f r - g r| ≤
      (12 * (c + 2) ^ 2 * ε ^ 4) * |(1 : ℝ) - (-1)| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro r hr
    have hr' : r ∈ Icc (-1 : ℝ) 1 := by
      simpa using Ioc_subset_Icc_self hr
    have hlocal := scalar_remainder hc (add_nonneg (H_nonneg r) hb)
      (by linarith [H_le_one hr']) (D0_nonneg r) (D0_le_three hr') hsmall
    rw [Real.norm_eq_abs]
    convert hlocal using 1
    dsimp [f, g]
    congr 1
    ring
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _), hgint] at hbound
  change |Q (fun r => 1 + ε ^ 2 * (H r + b)) ε - _| ≤ _ at hbound
  norm_num at hbound
  nlinarith only [hbound]

theorem linear_cost_remainder {β ε : ℝ} (hβ : 0 ≤ β)
    (hsmall : 4 * (β + 2) * ε ^ 2 ≤ 1) :
    |Q (linearCap β ε) ε - (1 + (2 * β - 1 / 30) * ε ^ 2)| ≤
      24 * (β + 2) ^ 2 * ε ^ 4 :=
  padded_cost_remainder hβ le_rfl hβ hsmall

theorem cubic_cost_remainder {c ε : ℝ} (hc : 0 ≤ c) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hsmall : 4 * (c + 2) * ε ^ 2 ≤ 1) :
    |Q (cubicCap c ε) ε - (1 - ε ^ 2 / 30 + 2 * c * ε ^ 3)| ≤
      24 * (c + 2) ^ 2 * ε ^ 4 := by
  have h := padded_cost_remainder (mul_nonneg hc hε0)
    (mul_le_of_le_one_right hc hε1) hc hsmall
  have he : (fun r => 1 + ε ^ 2 * (H r + c * ε)) = cubicCap c ε := by
    funext r
    unfold cubicCap
    ring
  rw [he] at h
  convert h using 1
  congr 1
  ring

theorem rpow_five_halves {ε : ℝ} (hε : 0 < ε) :
    ε ^ (5 / 2 : ℝ) = ε ^ 2 * Real.sqrt ε := by
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num,
    Real.rpow_add hε, ← Real.sqrt_eq_rpow, Real.rpow_two]

theorem fractional_cost_remainder {c ε : ℝ} (hc : 0 ≤ c) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : 4 * (c + 2) * ε ^ 2 ≤ 1) :
    |Q (fractionalCap c ε) ε - (1 - ε ^ 2 / 30 + 2 * c * ε ^ (5 / 2 : ℝ))| ≤
      24 * (c + 2) ^ 2 * ε ^ 4 := by
  have h := padded_cost_remainder (mul_nonneg hc (Real.sqrt_nonneg ε))
    (mul_le_of_le_one_right hc (Real.sqrt_le_one.mpr hε1)) hc hsmall
  have he : (fun r => 1 + ε ^ 2 * (H r + c * Real.sqrt ε)) = fractionalCap c ε := by
    funext r
    unfold fractionalCap
    rw [rpow_five_halves hε0]
    ring
  rw [he] at h
  rw [rpow_five_halves hε0]
  convert h using 1
  congr 1
  ring

theorem eventually_small_scale (c : ℝ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ 1 ∧ 4 * (c + 2) * ε ^ 2 ≤ 1 := by
  have hscale : ∀ᶠ ε : ℝ in 𝓝 0, 4 * (c + 2) * ε ^ 2 < 1 :=
    (show ContinuousAt (fun ε : ℝ => 4 * (c + 2) * ε ^ 2) 0 by fun_prop).eventually_lt
      continuousAt_const (by norm_num)
  have hone : ∀ᶠ ε : ℝ in 𝓝 0, ε < 1 :=
    continuousAt_id.eventually_lt continuousAt_const (by norm_num)
  filter_upwards [eventually_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hscale,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hone] with ε hε hs h1
  exact ⟨hε, h1.le, hs.le⟩

theorem linear_cost_bigO {β : ℝ} (hβ : 0 ≤ β) :
    (fun ε => Q (linearCap β ε) ε - (1 + (2 * β - 1 / 30) * ε ^ 2))
      =O[𝓝[>] (0 : ℝ)] (fun ε => ε ^ 4) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨24 * (β + 2) ^ 2, ?_⟩
  filter_upwards [eventually_small_scale β] with ε hε
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hε.1.le 4)] using
    linear_cost_remainder hβ hε.2.2

theorem cubic_cost_bigO {c : ℝ} (hc : 0 ≤ c) :
    (fun ε => Q (cubicCap c ε) ε - (1 - ε ^ 2 / 30 + 2 * c * ε ^ 3))
      =O[𝓝[>] (0 : ℝ)] (fun ε => ε ^ 4) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨24 * (c + 2) ^ 2, ?_⟩
  filter_upwards [eventually_small_scale c] with ε hε
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hε.1.le 4)] using
    cubic_cost_remainder hc hε.1.le hε.2.1 hε.2.2

theorem fractional_cost_bigO {c : ℝ} (hc : 0 ≤ c) :
    (fun ε => Q (fractionalCap c ε) ε -
      (1 - ε ^ 2 / 30 + 2 * c * ε ^ (5 / 2 : ℝ)))
      =O[𝓝[>] (0 : ℝ)] (fun ε => ε ^ 4) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨24 * (c + 2) ^ 2, ?_⟩
  filter_upwards [eventually_small_scale c] with ε hε
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hε.1.le 4)] using
    fractional_cost_remainder hc hε.1 hε.2.1 hε.2.2

theorem strict_of_remainder {q ε a K : ℝ} (hε : 0 < ε)
    (hrem : |q - (1 - a * ε ^ 2)| ≤ K * ε ^ 4)
    (hgap : K * ε ^ 2 < a) : q < 1 := by
  have hupper := (abs_le.mp hrem).2
  have hmul : K * ε ^ 4 < a * ε ^ 2 := by
    calc
      K * ε ^ 4 = (K * ε ^ 2) * ε ^ 2 := by ring
      _ < a * ε ^ 2 := mul_lt_mul_of_pos_right hgap (sq_pos_of_pos hε)
  linarith

theorem linear_cost_strict {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1 / 60) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, Q (linearCap β ε) ε < 1 := by
  have hgap : ∀ᶠ ε : ℝ in 𝓝 0,
      24 * (β + 2) ^ 2 * ε ^ 2 < 1 / 30 - 2 * β :=
    (show ContinuousAt (fun ε : ℝ => 24 * (β + 2) ^ 2 * ε ^ 2) 0 by fun_prop).eventually_lt
      continuousAt_const (by norm_num; linarith)
  filter_upwards [eventually_small_scale β,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hgap] with ε hε hg
  apply strict_of_remainder hε.1 (a := 1 / 30 - 2 * β) (K := 24 * (β + 2) ^ 2)
  · convert linear_cost_remainder hβ0.le hε.2.2 using 1
    congr 1
    ring
  · exact hg

theorem cubic_cost_strict {c : ℝ} (hc : 0 ≤ c) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, Q (cubicCap c ε) ε < 1 := by
  have hgap : ∀ᶠ ε : ℝ in 𝓝 0,
      24 * (c + 2) ^ 2 * ε ^ 2 + 2 * c * ε < 1 / 30 :=
    (show ContinuousAt (fun ε : ℝ => 24 * (c + 2) ^ 2 * ε ^ 2 + 2 * c * ε) 0 by fun_prop).eventually_lt
      continuousAt_const (by norm_num)
  filter_upwards [eventually_small_scale c,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hgap] with ε hε hg
  apply strict_of_remainder hε.1 (a := 1 / 30 - 2 * c * ε) (K := 24 * (c + 2) ^ 2)
  · convert cubic_cost_remainder hc hε.1.le hε.2.1 hε.2.2 using 1
    congr 1
    ring
  · linarith

theorem fractional_cost_strict {c : ℝ} (hc : 0 ≤ c) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, Q (fractionalCap c ε) ε < 1 := by
  have hgap : ∀ᶠ ε : ℝ in 𝓝 0,
      24 * (c + 2) ^ 2 * ε ^ 2 + 2 * c * Real.sqrt ε < 1 / 30 :=
    (show ContinuousAt (fun ε : ℝ => 24 * (c + 2) ^ 2 * ε ^ 2 + 2 * c * Real.sqrt ε) 0 by fun_prop).eventually_lt
      continuousAt_const (by norm_num)
  filter_upwards [eventually_small_scale c,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hgap] with ε hε hg
  apply strict_of_remainder hε.1 (a := 1 / 30 - 2 * c * Real.sqrt ε) (K := 24 * (c + 2) ^ 2)
  · have h := fractional_cost_remainder hc hε.1 hε.2.1 hε.2.2
    rw [rpow_five_halves hε.1] at h
    convert h using 1
    congr 1
    ring
  · linarith

theorem fixed_margin_coefficients :
    (2 * (1 / 120 : ℝ) - 1 / 30 = -1 / 60) ∧
    (2 * (1 / 125 : ℝ) - 1 / 30 = -13 / 750) ∧
    (2 * (1 / 500 : ℝ) - 1 / 30 = -11 / 375) ∧
    (2 * (4 / 625 : ℝ) - 1 / 30 = -77 / 3750) ∧
    (2 * (1 / 100 : ℝ) - 1 / 30 = -1 / 75) ∧
    (2 * (1 / 200 : ℝ) - 1 / 30 = -7 / 300) ∧
    (2 * (1 / 250 : ℝ) - 1 / 30 = -19 / 750) := by norm_num

theorem cubic_coefficients :
    (2 * (5 : ℝ) = 10) ∧ (2 * (12 : ℝ) = 24) ∧
    (2 * (20 : ℝ) = 40) ∧ (2 * (64 : ℝ) = 128) := by norm_num

theorem fractional_coefficients :
    (2 * (1 : ℝ) = 2) ∧ (2 * (4 * Real.sqrt 2) = 8 * Real.sqrt 2) ∧
    (2 * (8 * Real.sqrt 2) = 16 * Real.sqrt 2) := by
  constructor
  · norm_num
  constructor <;> ring

theorem continuous_linearCap (β ε : ℝ) : Continuous (linearCap β ε) := by
  unfold linearCap H
  fun_prop

theorem continuous_cubicCap (c ε : ℝ) : Continuous (cubicCap c ε) := by
  unfold cubicCap H
  fun_prop

theorem continuous_fractionalCap (c ε : ℝ) : Continuous (fractionalCap c ε) := by
  unfold fractionalCap H
  fun_prop

theorem linearCap_pos {β : ℝ} (hβ : 0 ≤ β) (ε r : ℝ) : 0 < linearCap β ε r := by
  unfold linearCap H
  positivity

theorem cubicCap_pos {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε) (r : ℝ) :
    0 < cubicCap c ε r := by
  unfold cubicCap H
  positivity

theorem fractionalCap_pos {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε) (r : ℝ) :
    0 < fractionalCap c ε r := by
  unfold fractionalCap H
  positivity

end CylinderCovering.RadialCaps

end

end OAI
