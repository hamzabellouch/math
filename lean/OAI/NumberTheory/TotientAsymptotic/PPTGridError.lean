import OAI.NumberTheory.TotientAsymptotic.PPTTopSlack
import OAI.NumberTheory.TotientAsymptotic.ComparisonErrorBudget

namespace OAI

/-!
The PPT grid uses a mesh of order `(log t)^5 / sqrt t`, where `t` is the
double logarithm of the comparison scale.  With logarithmically many
coordinates its rounding and normality errors fit inside the constructed
inverse-cube row margin.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- A direct bound for the three terms charged to the comparison
exponent.  The two grid widths may differ, as in Ford's PPT construction. -/
lemma ppt_grid_error_polynomial_bound {b H : ℕ} {e w η δ : ℝ}
    (hH : 1 ≤ H) (hbH : b ≤ H) (hδ : 0 ≤ δ)
    (he : e ≤ (2*(b : ℝ)+4)*δ) (hw : w ≤ (4*(b : ℝ)+3)*δ)
    (hη : η ≤ δ) :
    e*(∑ j ∈ Finset.Icc 1 (b-1), a j)+2*(b-1 : ℕ)*w+
      η*(∑ i ∈ Finset.Icc 2 b, ((i : ℝ)*Real.log i+i)) ≤
        32*(H : ℝ)^3*δ := by
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hbR : (b : ℝ) ≤ H := by exact_mod_cast hbH
  have hb' : b-1 ≤ H := (Nat.sub_le b 1).trans hbH
  have hb'R : ((b-1 : ℕ) : ℝ) ≤ H := by exact_mod_cast hb'
  have hsa0 : 0 ≤ ∑ j ∈ Finset.Icc 1 (b-1), a j :=
    Finset.sum_nonneg fun j hj => (a_pos (Finset.mem_Icc.mp hj).1).le
  have hsa : (∑ j ∈ Finset.Icc 1 (b-1), a j) ≤ (H : ℝ)^2 :=
    (sum_a_le_square (b-1)).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hb'R 2)
  have he' : e ≤ 6*(H : ℝ)*δ :=
    he.trans (mul_le_mul_of_nonneg_right (by linarith) hδ)
  have hw' : w ≤ 7*(H : ℝ)*δ :=
    hw.trans (mul_le_mul_of_nonneg_right (by linarith) hδ)
  have hfirst : e*(∑ j ∈ Finset.Icc 1 (b-1), a j) ≤ 6*(H : ℝ)^3*δ := by
    calc
      _ ≤ (6*(H : ℝ)*δ)*(H : ℝ)^2 :=
        mul_le_mul he' hsa hsa0 (by positivity)
      _ = _ := by ring
  have hsecond : 2*(b-1 : ℕ)*w ≤ 14*(H : ℝ)^2*δ := by
    calc
      _ ≤ (2*((b-1 : ℕ) : ℝ))*(7*(H : ℝ)*δ) :=
        mul_le_mul_of_nonneg_left hw' (by positivity)
      _ ≤ (2*(H : ℝ))*(7*(H : ℝ)*δ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  have hlog0 : 0 ≤ ∑ i ∈ Finset.Icc 2 b, ((i : ℝ)*Real.log i+i) := by
    apply Finset.sum_nonneg
    intro i hi
    have hiR : (1 : ℝ) ≤ i := by
      have hi2 := (Finset.mem_Icc.mp hi).1
      exact_mod_cast (show 1 ≤ i by omega)
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hiR))
      (Nat.cast_nonneg _)
  have hthird : η*(∑ i ∈ Finset.Icc 2 b, ((i : ℝ)*Real.log i+i)) ≤
      2*(H : ℝ)^3*δ := by
    calc
      _ ≤ δ*(2*(H : ℝ)^3) :=
        mul_le_mul hη (comparison_log_sum_bound hbH hH) hlog0 hδ
      _ = _ := by ring
  have hpow : (H : ℝ)^2 ≤ (H : ℝ)^3 := by nlinarith
  have hpowδ := mul_le_mul_of_nonneg_right hpow hδ
  have hnonneg : 0 ≤ (H : ℝ)^3*δ := by positivity
  nlinarith only [hfirst, hsecond, hthird, hpowδ, hnonneg]

/-- The logarithmic dimension range is uniform in the integer dimension.
Its sixth power is absorbed by the square-root denominator of the mesh. -/
theorem ppt_log_dimension_mesh_budget {C : ℝ} (_hC : 0 < C) :
    ∀ᶠ t : ℝ in atTop, ∀ H : ℕ,
      1 ≤ H → (H : ℝ) ≤ C*Real.log t →
      32*(H : ℝ)^3*((Real.log t)^5/Real.sqrt t) ≤
        1/(80*(H : ℝ)^3) := by
  have hlim : Tendsto (fun t : ℝ => (Real.log t)^11/Real.sqrt t)
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (11 : ℕ)
        (show (0 : ℝ) < 1/2 by norm_num)).tendsto_div_nhds_zero
  have hscaled : Tendsto (fun t : ℝ =>
      2560*C^6*((Real.log t)^11/Real.sqrt t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul (2560*C^6)
  filter_upwards [hscaled.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (1 : ℝ)] with t ht ht1
  intro H hH hdim
  have ht0 : 0 < t := zero_lt_one.trans ht1
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := zero_lt_one.trans_le hHR
  have hδ : 0 ≤ (Real.log t)^5/Real.sqrt t := by positivity
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg H) hdim 6
  have hbudget : 2560*(H : ℝ)^6*((Real.log t)^5/Real.sqrt t) ≤ 1 := by
    calc
      _ ≤ 2560*(C*Real.log t)^6*((Real.log t)^5/Real.sqrt t) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) hδ
      _ = 2560*C^6*((Real.log t)^11/Real.sqrt t) := by ring
      _ ≤ 1 := ht.le
  apply (le_div_iff₀ (by positivity : 0 < 80*(H : ℝ)^3)).mpr
  convert hbudget using 1
  ring

/-- All error terms fit below the exact row margin for every row index
whose remaining dimension is bounded by `H`. -/
theorem ppt_grid_error_absorbed {C : ℝ} (hC : 0 < C) :
    ∀ᶠ t : ℝ in atTop, ∀ (b H r : ℕ) (e w η δ : ℝ),
      1 ≤ H → b ≤ H → r+1 ≤ H → (H : ℝ) ≤ C*Real.log t →
      0 ≤ δ → δ ≤ (Real.log t)^5/Real.sqrt t →
      e ≤ (2*(b : ℝ)+4)*δ → w ≤ (4*(b : ℝ)+3)*δ → η ≤ δ →
      e*(∑ j ∈ Finset.Icc 1 (b-1), a j)+2*(b-1 : ℕ)*w+
        η*(∑ i ∈ Finset.Icc 2 b, ((i : ℝ)*Real.log i+i)) ≤
          rowContractionError r/16 := by
  filter_upwards [ppt_log_dimension_mesh_budget hC] with t ht
  intro b H r e w η δ hH hbH hrH hdim hδ hδmax he hw hη
  apply (ppt_grid_error_polynomial_bound hH hbH hδ he hw hη).trans
  calc
    _ ≤ 32*(H : ℝ)^3*((Real.log t)^5/Real.sqrt t) :=
      mul_le_mul_of_nonneg_left hδmax (by positivity)
    _ ≤ 1/(80*(H : ℝ)^3) := ht H hH hdim
    _ ≤ 1/(80*(r+1 : ℝ)^3) := by
      have hr : (r+1 : ℝ) ≤ H := by exact_mod_cast hrH
      exact one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hr 3) (by norm_num))
    _ = rowContractionError r/16 := by
      unfold rowContractionError
      rw [div_div]
      congr 1
      ring

end TotientAsymptotic

end

end OAI
