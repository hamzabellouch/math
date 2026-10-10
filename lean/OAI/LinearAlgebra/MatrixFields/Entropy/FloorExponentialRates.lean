import Mathlib

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.FloorExponentialRates

open Filter
open scoped BigOperators Topology Classical

def count (rate : ℝ) (m : ℕ) : ℕ := ⌊Real.exp ((m : ℝ) * rate)⌋₊

theorem count_pos {rate : ℝ} (hr : 0 ≤ rate) (m : ℕ) : 0 < count rate m := by
  have he : (1 : ℝ) ≤ Real.exp ((m : ℝ) * rate) :=
    Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) hr)
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_floor (by simpa only [Nat.cast_one] using he))

theorem log_count_bounds {rate : ℝ} (hr : 0 ≤ rate) (m : ℕ) :
    (m : ℝ) * rate - Real.log 2 ≤ Real.log (count rate m : ℝ) ∧
      Real.log (count rate m : ℝ) ≤ (m : ℝ) * rate := by
  have hp : (0 : ℝ) < count rate m := Nat.cast_pos.mpr (count_pos hr m)
  have hone : (1 : ℝ) ≤ count rate m := by exact_mod_cast count_pos hr m
  have hround := Nat.lt_floor_add_one (Real.exp ((m : ℝ) * rate))
  have hhalf : Real.exp ((m : ℝ) * rate) / 2 ≤ (count rate m : ℝ) := by
    change Real.exp ((m : ℝ) * rate) < (count rate m : ℝ) + 1 at hround
    linarith
  constructor
  · have h := Real.log_le_log (by positivity : 0 < Real.exp ((m : ℝ) * rate) / 2) hhalf
    simpa only [Real.log_div (Real.exp_ne_zero _) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_exp] using h
  · have h := Real.log_le_log hp (Nat.floor_le (Real.exp_pos _).le)
    simpa only [Real.log_exp] using h

theorem tendsto_log_count_div_nat {rate : ℝ} (hr : 0 ≤ rate) :
    Tendsto (fun m : ℕ => Real.log (count rate m : ℝ) / (m : ℝ))
      atTop (𝓝 rate) := by
  have hinv : Tendsto (fun m : ℕ => Real.log 2 / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun m : ℕ => rate - Real.log 2 / (m : ℝ)) atTop (𝓝 rate) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have h := div_le_div_of_nonneg_right (log_count_bounds hr m).1 hm'.le
    simpa only [sub_div, mul_div_cancel_left₀ rate hm'.ne'] using h
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have h := div_le_div_of_nonneg_right (log_count_bounds hr m).2 hm'.le
    simpa only [mul_div_cancel_left₀ rate hm'.ne'] using h

theorem tendsto_log_prod_count_div_nat {I : Type*} [Fintype I] (rate : I → ℝ)
    (hr : ∀ i, 0 ≤ rate i) :
    Tendsto (fun m : ℕ => Real.log ((∏ i, count (rate i) m : ℕ) : ℝ) / (m : ℝ))
      atTop (𝓝 (∑ i, rate i)) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ => tendsto_log_count_div_nat (hr i))
  apply h.congr
  intro m
  rw [Nat.cast_prod, Real.log_prod
    (fun i _ => Nat.cast_ne_zero.mpr (Nat.ne_of_gt (count_pos (hr i) m)))]
  simp only [div_eq_mul_inv, Finset.sum_mul]

abbrev Labels {I : Type*} (rate : I → ℝ) (m : ℕ) := ∀ i, Fin (count (rate i) m)

theorem card_labels {I : Type*} [Fintype I] (rate : I → ℝ) (m : ℕ) :
    Fintype.card (Labels rate m) = ∏ i, count (rate i) m := by
  simp only [Labels, Fintype.card_pi, Fintype.card_fin]

theorem card_labels_pos {I : Type*} [Fintype I] (rate : I → ℝ)
    (hr : ∀ i, 0 ≤ rate i) (m : ℕ) : 0 < Fintype.card (Labels rate m) := by
  rw [card_labels]
  exact Finset.prod_pos fun i _ => count_pos (hr i) m

theorem tendsto_log_card_labels_div_nat {I : Type*} [Fintype I] (rate : I → ℝ)
    (hr : ∀ i, 0 ≤ rate i) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card (Labels rate m) : ℝ) / (m : ℝ))
      atTop (𝓝 (∑ i, rate i)) := by
  simpa only [card_labels] using tendsto_log_prod_count_div_nat rate hr

end MatrixMultiplication.FloorExponentialRates

end

end MatrixAllFields

end OAI
