import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Basic.Real.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace InternalCatalan

section

def n (N : ℕ) : ℕ := 48 * N
def a (N : ℕ) : ℕ := 11 * N
def b (N : ℕ) : ℕ := 7 * N
def q (N : ℕ) : ℕ := 4 * N
def g (N : ℕ) : ℕ := 4 * N
def h (N : ℕ) : ℕ := 2 * N
def L (N : ℕ) : ℕ := 59 * N
def Cdegree (N : ℕ) : ℕ := 63 * N
def H (N : ℕ) : ℕ := 65 * N
def A (N : ℕ) : ℕ := 19 * N

def rowOffset (N r : ℕ) : ℤ := (r : ℤ) - (g N : ℤ)
def rowDistance (N r : ℕ) : ℕ := (rowOffset N r).natAbs

theorem L_eq_n_add_a (N : ℕ) : L N = n N + a N := by
  unfold L n a
  omega

theorem L_eq_n_add_b_add_q (N : ℕ) : L N = n N + b N + q N := by
  unfold L n b q
  omega

theorem Cdegree_eq_L_add_g (N : ℕ) : Cdegree N = L N + g N := by
  unfold Cdegree L g
  omega

theorem H_eq_Cdegree_add_h (N : ℕ) : H N = Cdegree N + h N := by
  unfold H Cdegree h
  omega

theorem A_eq_a_add_two_mul_g (N : ℕ) : A N = a N + 2 * g N := by
  unfold A a g
  omega

theorem Cdegree_pos {N : ℕ} (hN : 0 < N) : 0 < Cdegree N := by
  unfold Cdegree
  omega

theorem rawColumn_lt_L {N k v : ℕ} (hk : k < n N) (hv : v ≤ q N) :
    b N + k + v < L N := by
  rw [L_eq_n_add_b_add_q]
  omega

theorem rawColumn_ge_b (N k v : ℕ) : b N ≤ b N + k + v := by omega

theorem rowDistance_le {N r : ℕ} (hN : 0 < N) (hr : r < n N) :
    rowDistance N r ≤ n N - 1 - g N := by
  unfold rowDistance rowOffset n g at *
  omega

theorem rowDistance_lt_Cdegree {N r : ℕ} (hN : 0 < N) (hr : r < n N) :
    rowDistance N r < Cdegree N := by
  have hd := rowDistance_le hN hr
  unfold n g Cdegree at *
  omega

theorem A_le_reversed_T_min {N r : ℕ} (hN : 0 < N) (hr : r < n N) :
    A N ≤ Cdegree N - 1 - rowDistance N r := by
  have hd := rowDistance_le hN hr
  unfold n g A Cdegree at *
  omega

theorem A_add_one_le_reversed_U_min {N r : ℕ} (hN : 0 < N)
    (hr : r < n N) (hd : 0 < rowDistance N r) :
    A N + 1 ≤ Cdegree N - 1 - (rowDistance N r - 1) := by
  have hdist := rowDistance_le hN hr
  unfold n g A Cdegree at *
  omega

theorem contactOrder_eq (N r : ℕ) :
    (Cdegree N : ℤ) + rowOffset N r = (L N : ℤ) + r := by
  unfold rowOffset Cdegree L g
  push_cast
  omega

theorem contactOrder_ge_L (N r : ℕ) :
    (L N : ℤ) ≤ (Cdegree N : ℤ) + rowOffset N r := by
  rw [contactOrder_eq]
  omega

theorem auxiliary_rowDistance : rowDistance 1 48 = 44 := by decide
theorem auxiliary_reversed_T_min : Cdegree 1 - 1 - rowDistance 1 48 = 18 := by decide
theorem auxiliary_reversed_U_min : Cdegree 1 - 1 - (rowDistance 1 48 - 1) = 19 := by
  decide

theorem energy_abs_node_exponent {N : ℕ} (hN : 0 < N) :
    ((Cdegree N - 1 : ℕ) : ℤ) + (g N : ℤ) - ((n N - 1 : ℕ) : ℤ) =
      (A N : ℤ) := by
  unfold Cdegree g n A
  omega

theorem energy_parameter_ratios {N : ℕ} (hN : 0 < N) :
    (A N : ℝ) / (n N : ℝ) = 19 / 48 ∧
    ((2 * h N : ℕ) : ℝ) / (n N : ℝ) = 1 / 12 ∧
    (b N : ℝ) / (n N : ℝ) = 7 / 48 ∧
    (q N : ℝ) / (n N : ℝ) = 1 / 12 ∧
    (Cdegree N : ℝ) / (n N : ℝ) = 21 / 16 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [A, h, b, q, Cdegree, n, Nat.cast_mul, Nat.cast_ofNat] <;>
    field_simp [hN0] <;> ring

theorem energy_quadratic_exponent {N : ℕ} (hN : 0 < N) (k : ℝ) :
    (2 - (Cdegree N : ℝ) - (h N : ℝ) +
        (2 - k) * ((n N : ℝ) - 1) / 2) / (n N : ℝ) =
      -(k / 2 + 17 / 48) + (k + 2) / (2 * (n N : ℝ)) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  simp only [Cdegree, h, n, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hN0]
  ring

theorem energy_power_two_constant {N : ℕ} (hN : 0 < N) (k : ℝ) :
    ((n N : ℝ) * ((Cdegree N : ℝ) - 1) +
        (k - 1) * ((n N).choose 2 : ℝ)) / (n N : ℝ) ^ 2 - 1 / 2 =
      (Cdegree N : ℝ) / (n N : ℝ) + (k - 2) / 2 -
        (k + 1) / (2 * (n N : ℝ)) := by
  have hn0 : (n N : ℝ) ≠ 0 := by
    exact_mod_cast (show n N ≠ 0 by unfold n; omega)
  rw [Nat.cast_choose_two]
  field_simp [hn0]
  ring

theorem energy_constant_after_squares {N : ℕ} (hN : 0 < N) (k : ℝ) :
    ((Cdegree N : ℝ) / (n N : ℝ) + (k - 2) / 2 -
        (k + 1) / (2 * (n N : ℝ))) - k / 2 - 1 =
      (-1 + 11 / 48 + 4 / 48 : ℝ) - (k + 1) / (2 * (n N : ℝ)) := by
  rw [(energy_parameter_ratios hN).2.2.2.2]
  ring

end

noncomputable section
open Set
open scoped BigOperators

theorem energy_log_one_add_sq_bounds {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ Real.log (1 + x ^ 2) ∧ Real.log (1 + x ^ 2) ≤ Real.log 2 := by
  have hp : 0 < (1 - x) * (1 + x) :=
    mul_pos (sub_pos.mpr hx.2) (by linarith [hx.1])
  constructor
  · exact Real.log_nonneg (by nlinarith [sq_nonneg x])
  · exact Real.log_le_log (by positivity) (by nlinarith)

theorem realEnergyFiniteCorrection_bounds {N : ℕ} (hN : 0 < N)
    (k : ℝ) (hk : k = 1 ∨ k = 2) (x : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    (0 ≤ (1 / (n N : ℝ)) *
      ∑ i : Fin (n N), ((k + 2) / (2 * (n N : ℝ)) * Real.log (1 + x i ^ 2))) ∧
    ((1 / (n N : ℝ)) *
      ∑ i : Fin (n N), ((k + 2) / (2 * (n N : ℝ)) * Real.log (1 + x i ^ 2))) ≤
      2 * Real.log 2 / (n N : ℝ) := by
  have hn : 0 < (n N : ℝ) :=
    Nat.cast_pos.mpr (show 0 < n N by unfold n; omega)
  have hk0 : 0 ≤ k + 2 := by
    rcases hk with rfl | rfl <;> norm_num
  have hk4 : k + 2 ≤ 4 := by
    rcases hk with rfl | rfl <;> norm_num
  have hc0 : 0 ≤ (k + 2) / (2 * (n N : ℝ)) :=
    div_nonneg hk0 (by positivity)
  have hc2 : (k + 2) / (2 * (n N : ℝ)) ≤ 2 / (n N : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hn).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hk4) hn.le]
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hterm (i : Fin (n N)) :
      (k + 2) / (2 * (n N : ℝ)) * Real.log (1 + x i ^ 2) ≤
        2 * Real.log 2 / (n N : ℝ) := by
    calc
      _ ≤ (k + 2) / (2 * (n N : ℝ)) * Real.log 2 :=
        mul_le_mul_of_nonneg_left (energy_log_one_add_sq_bounds (hx i)).2 hc0
      _ ≤ (2 / (n N : ℝ)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hc2 hlog2
      _ = _ := by ring
  constructor
  · apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg hc0 (energy_log_one_add_sq_bounds (hx i)).1)
  · calc
      _ ≤ (1 / (n N : ℝ)) *
          ∑ _i : Fin (n N), (2 * Real.log 2 / (n N : ℝ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hterm i)) (by positivity)
      _ = 2 * Real.log 2 / (n N : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [hn.ne']

end

theorem twoAdicQuadratic_lower (N : ℕ) (m l : ℝ)
    (hm : 0 ≤ m) (hl : 0 ≤ l) (hml : m + l ≤ (n N : ℝ)) :
    -(505 / 4608 : ℝ) * (n N : ℝ) ^ 2 ≤
      -((H N : ℝ) - (b N : ℝ)) * m + (3 / 2 : ℝ) * m ^ 2 +
        (1 / 2 : ℝ) * l ^ 2 + (Cdegree N : ℝ) * ((n N : ℝ) - m - l) := by
  simp only [n, Nat.cast_mul, Nat.cast_ofNat] at hml
  simp only [n, H, b, Cdegree, Nat.cast_mul, Nat.cast_ofNat]
  have hN : 0 ≤ (N : ℝ) :=
    nonneg_of_mul_nonneg_right ((add_nonneg hm hl).trans hml) (by norm_num : (0 : ℝ) < 48)
  have hl_bound : l ≤ 48 * (N : ℝ) := by linarith only [hm, hml]
  have hgap : 0 ≤ 48 * (N : ℝ) - m - l := by linarith only [hml]
  have hfactor : 0 ≤ 63 * (N : ℝ) - (48 * (N : ℝ) - m + l) / 2 := by
    linarith only [hN, hm, hl, hl_bound]
  have hproduct := mul_nonneg hgap hfactor
  have hsquare := sq_nonneg (m - (53 / 2 : ℝ) * (N : ℝ))
  nlinarith only [hproduct, hsquare]

end InternalCatalan

end OAI
