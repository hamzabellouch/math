import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OAI.NumberTheory.Catalan.Estimates.RealEnergyTwoProduct

namespace OAI

noncomputable section

namespace InternalCatalan

open Set
open scoped BigOperators

private theorem energy_difference_ne_zero_of_lt {m : ℕ} (x : Fin m → ℝ)
    (hxi : Function.Injective x) {i j : Fin m} (hij : i < j) : x j - x i ≠ 0 :=
  sub_ne_zero.mpr (fun heq => (ne_of_gt hij) (hxi heq))

theorem energy_vandermonde_product_ne_zero {m : ℕ} (x : Fin m → ℝ)
    (hxi : Function.Injective x) :
    (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (x j - x i)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact energy_difference_ne_zero_of_lt x hxi (Finset.mem_Ioi.mp hj)

theorem energy_abs_vandermonde_pos {m : ℕ} (x : Fin m → ℝ)
    (hxi : Function.Injective x) :
    0 < |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (x j - x i)| :=
  abs_pos.mpr (energy_vandermonde_product_ne_zero x hxi)

theorem log_abs_vandermonde {m : ℕ} (x : Fin m → ℝ)
    (hxi : Function.Injective x) :
    Real.log |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (x j - x i)| =
      ∑ i : Fin m, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i| := by
  have hrow (i : Fin m) : (∏ j ∈ Finset.Ioi i, (x j - x i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact energy_difference_ne_zero_of_lt x hxi (Finset.mem_Ioi.mp hj)
  simp only [Real.log_abs]
  rw [Real.log_prod (s := Finset.univ)
    (f := fun i : Fin m => ∏ j ∈ Finset.Ioi i, (x j - x i))
    (fun i _ => hrow i)]
  apply Finset.sum_congr rfl
  intro i _
  exact Real.log_prod (s := Finset.Ioi i) (f := fun j => x j - x i)
    (fun j hj => energy_difference_ne_zero_of_lt x hxi (Finset.mem_Ioi.mp hj))

theorem energy_pair_product_pos {m : ℕ} (x : Fin m → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    0 < ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (1 - x i * x j) := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  exact energy_one_sub_mul_pos (hx i) (hx j)

theorem log_energy_pair_product {m : ℕ} (x : Fin m → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    Real.log (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (1 - x i * x j)) =
      ∑ i : Fin m, ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j) := by
  have hrow (i : Fin m) : (∏ j ∈ Finset.Ioi i, (1 - x i * x j)) ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro j _
    exact energy_one_sub_mul_pos (hx i) (hx j)
  rw [Real.log_prod (s := Finset.univ)
    (f := fun i : Fin m => ∏ j ∈ Finset.Ioi i, (1 - x i * x j))
    (fun i _ => hrow i)]
  apply Finset.sum_congr rfl
  intro i _
  exact Real.log_prod (s := Finset.Ioi i) (f := fun j => 1 - x i * x j)
    (fun j _ => (energy_one_sub_mul_pos (hx i) (hx j)).ne')

theorem energy_mixed_product_pos {m : ℕ} (x s : Fin m → ℝ)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    0 < ∏ i : Fin m, ∏ j : Fin m, (1 - 2 * x i * s j + x i ^ 2) := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  exact realCoordinateInv_kernel_numerator_pos (x i) (hs j)

theorem log_energy_mixed_product {m : ℕ} (x s : Fin m → ℝ)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    Real.log (∏ i : Fin m, ∏ j : Fin m, (1 - 2 * x i * s j + x i ^ 2)) =
      ∑ i : Fin m, ∑ j : Fin m, Real.log (1 - 2 * x i * s j + x i ^ 2) := by
  have hrow (i : Fin m) : (∏ j : Fin m, (1 - 2 * x i * s j + x i ^ 2)) ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro j _
    exact realCoordinateInv_kernel_numerator_pos (x i) (hs j)
  rw [Real.log_prod (s := Finset.univ)
    (f := fun i : Fin m => ∏ j : Fin m, (1 - 2 * x i * s j + x i ^ 2))
    (fun i _ => hrow i)]
  apply Finset.sum_congr rfl
  intro i _
  exact Real.log_prod (s := Finset.univ) (f := fun j : Fin m => 1 - 2 * x i * s j + x i ^ 2)
    (fun j _ => (realCoordinateInv_kernel_numerator_pos (x i) (hs j)).ne')

theorem energy_s_weight_product_pos (N : ℕ) (s : Fin (n N) → ℝ)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) :
    0 < ∏ i : Fin (n N), (s i ^ b N * (1 - s i) ^ q N) := by
  apply Finset.prod_pos
  intro i _
  exact mul_pos (pow_pos (hs i).1 _) (pow_pos (sub_pos.mpr (hs i).2) _)

theorem energy_node_weight_product_pos (N : ℕ) (k : ℝ) (x : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    0 < ∏ i : Fin (n N),
      (|x i| ^ A N * (1 - x i) ^ (2 * h N) * (1 + x i ^ 2) ^ k) := by
  apply Finset.prod_pos
  intro i _
  exact mul_pos (mul_pos (pow_pos (abs_pos.mpr (hx0 i)) _)
    (pow_pos (sub_pos.mpr (hx i).2) _))
    (Real.rpow_pos_of_pos (realCoordinateInv_denominator_pos (x i)) _)

theorem energy_plain_node_weight_product_pos (N : ℕ) (x : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    0 < ∏ i : Fin (n N), (|x i| ^ A N * (1 - x i) ^ (2 * h N)) := by
  simpa only [Real.rpow_zero, mul_one] using
    energy_node_weight_product_pos N 0 x hx hx0

theorem energy_quadratic_product_pos (N : ℕ) (x : Fin (n N) → ℝ) :
    0 < ∏ i : Fin (n N), (1 + x i ^ 2) ^ (H N - 2) := by
  exact Finset.prod_pos (fun i _ => pow_pos (realCoordinateInv_denominator_pos (x i)) _)

theorem log_energy_s_weight_product (N : ℕ) (s : Fin (n N) → ℝ)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) :
    Real.log (∏ i : Fin (n N), (s i ^ b N * (1 - s i) ^ q N)) =
      ∑ i : Fin (n N), ((b N : ℝ) * Real.log (s i) +
        (q N : ℝ) * Real.log (1 - s i)) := by
  rw [Real.log_prod (fun i _ =>
    mul_ne_zero (pow_ne_zero _ (hs i).1.ne') (pow_ne_zero _ (sub_pos.mpr (hs i).2).ne'))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.log_mul (pow_ne_zero _ (hs i).1.ne')
    (pow_ne_zero _ (sub_pos.mpr (hs i).2).ne'), Real.log_pow, Real.log_pow]

theorem log_energy_node_weight_product (N : ℕ) (k : ℝ) (x : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    Real.log (∏ i : Fin (n N),
      (|x i| ^ A N * (1 - x i) ^ (2 * h N) * (1 + x i ^ 2) ^ k)) =
      ∑ i : Fin (n N), ((A N : ℝ) * Real.log |x i| +
        ((2 * h N : ℕ) : ℝ) * Real.log (1 - x i) +
        k * Real.log (1 + x i ^ 2)) := by
  have hrow (i : Fin (n N)) :
      0 < |x i| ^ A N * (1 - x i) ^ (2 * h N) * (1 + x i ^ 2) ^ k :=
    mul_pos (mul_pos (pow_pos (abs_pos.mpr (hx0 i)) _)
      (pow_pos (sub_pos.mpr (hx i).2) _))
      (Real.rpow_pos_of_pos (realCoordinateInv_denominator_pos (x i)) _)
  rw [Real.log_prod (fun i _ => (hrow i).ne')]
  apply Finset.sum_congr rfl
  intro i _
  have ha : |x i| ^ A N ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr (hx0 i))
  have hb : (1 - x i) ^ (2 * h N) ≠ 0 := pow_ne_zero _ (sub_pos.mpr (hx i).2).ne'
  have hc : (1 + x i ^ 2) ^ k ≠ 0 :=
    (Real.rpow_pos_of_pos (realCoordinateInv_denominator_pos (x i)) k).ne'
  rw [Real.log_mul (mul_ne_zero ha hb) hc, Real.log_mul ha hb,
    Real.log_pow, Real.log_pow, Real.log_rpow (realCoordinateInv_denominator_pos (x i))]

theorem log_energy_plain_node_weight_product (N : ℕ) (x : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    Real.log (∏ i : Fin (n N), (|x i| ^ A N * (1 - x i) ^ (2 * h N))) =
      ∑ i : Fin (n N), ((A N : ℝ) * Real.log |x i| +
        ((2 * h N : ℕ) : ℝ) * Real.log (1 - x i)) := by
  simpa only [Real.rpow_zero, mul_one, zero_mul, add_zero] using
    log_energy_node_weight_product N 0 x hx hx0

theorem log_energy_quadratic_product (N : ℕ) (x : Fin (n N) → ℝ) :
    Real.log (∏ i : Fin (n N), (1 + x i ^ 2) ^ (H N - 2)) =
      ∑ i : Fin (n N), ((H N - 2 : ℕ) : ℝ) * Real.log (1 + x i ^ 2) := by
  rw [Real.log_prod (fun i _ =>
    pow_ne_zero _ (realCoordinateInv_denominator_pos (x i)).ne')]
  simp only [Real.log_pow]

open Set
open scoped BigOperators

theorem log_realEnergyMajorantOne {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (realEnergyMajorantOne N x s) =
      ((n N * (Cdegree N - 1) : ℕ) : ℝ) * Real.log 2 +
      (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) +
      2 * (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log |s j - s i|) +
      (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j)) +
      (∑ j : Fin (n N), ((b N : ℝ) * Real.log (s j) +
        (q N : ℝ) * Real.log (1 - s j))) +
      (∑ i : Fin (n N), ((A N : ℝ) * Real.log |x i| +
        ((2 * h N : ℕ) : ℝ) * Real.log (1 - x i) +
        (2 - (Cdegree N : ℝ) - (h N : ℝ) + ((n N : ℝ) - 1) / 2) *
          Real.log (1 + x i ^ 2))) -
      (∑ i : Fin (n N), ∑ j : Fin (n N), Real.log (1 - 2 * x i * s j + x i ^ 2)) := by
  have hX := energy_abs_vandermonde_pos x hxi
  have hS := energy_abs_vandermonde_pos s hsi
  have hP := energy_pair_product_pos x hx
  have hK := energy_mixed_product_pos x s hs
  have hSW := energy_s_weight_product_pos N s hs
  have hW := energy_node_weight_product_pos N
    (2 - (Cdegree N : ℝ) - (h N : ℝ) + ((n N : ℝ) - 1) / 2) x hx hx0
  rw [realEnergyMajorantOne_coordinate hN x s hx hx0]
  rw [Real.log_div (by positivity) hK.ne',
    Real.log_mul (by positivity) hW.ne',
    Real.log_mul (by positivity) hSW.ne',
    Real.log_mul (by positivity) hP.ne',
    Real.log_mul (by positivity) (pow_ne_zero _ hS.ne'),
    Real.log_mul (by positivity) hX.ne']
  rw [Real.log_pow, Real.log_pow, log_abs_vandermonde x hxi,
    log_abs_vandermonde s hsi, log_energy_pair_product x hx,
    log_energy_s_weight_product N s hs,
    log_energy_node_weight_product N _ x hx hx0,
    log_energy_mixed_product x s hs]
  norm_num

theorem log_realEnergyMajorantTwo {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (realEnergyMajorantTwo N x s) =
      ((n N * (Cdegree N - 1) + (n N).choose 2 : ℕ) : ℝ) * Real.log 2 +
      2 * (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) +
      2 * (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log |s j - s i|) +
      (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j)) +
      (∑ j : Fin (n N), ((b N : ℝ) * Real.log (s j) +
        (q N : ℝ) * Real.log (1 - s j))) +
      (∑ i : Fin (n N), ((A N : ℝ) * Real.log |x i| +
        ((2 * h N : ℕ) : ℝ) * Real.log (1 - x i) +
        (2 - (Cdegree N : ℝ) - (h N : ℝ)) * Real.log (1 + x i ^ 2))) -
      (∑ i : Fin (n N), ∑ j : Fin (n N), Real.log (1 - 2 * x i * s j + x i ^ 2)) := by
  have hX := energy_abs_vandermonde_pos x hxi
  have hS := energy_abs_vandermonde_pos s hsi
  have hP := energy_pair_product_pos x hx
  have hK := energy_mixed_product_pos x s hs
  have hSW := energy_s_weight_product_pos N s hs
  have hW := energy_plain_node_weight_product_pos N x hx hx0
  have hD := energy_quadratic_product_pos N x
  have hH : 2 ≤ H N := by unfold H; omega
  have hc : ((H N - 2 : ℕ) : ℝ) = (Cdegree N : ℝ) + (h N : ℝ) - 2 := by
    rw [Nat.cast_sub hH, H_eq_Cdegree_add_h, Nat.cast_add, Nat.cast_ofNat]
  rw [realEnergyMajorantTwo_coordinate hN x s hx hx0]
  rw [Real.log_div (by positivity) (mul_pos hK hD).ne',
    Real.log_mul (by positivity) hW.ne',
    Real.log_mul (by positivity) hSW.ne',
    Real.log_mul (by positivity) hP.ne',
    Real.log_mul (by positivity) (pow_ne_zero _ hS.ne'),
    Real.log_mul (by positivity) (pow_ne_zero _ hX.ne'),
    Real.log_mul hK.ne' hD.ne']
  rw [Real.log_pow, Real.log_pow, Real.log_pow,
    log_abs_vandermonde x hxi, log_abs_vandermonde s hsi,
    log_energy_pair_product x hx, log_energy_s_weight_product N s hs,
    log_energy_plain_node_weight_product N x hx hx0,
    log_energy_mixed_product x s hs, log_energy_quadratic_product N x]
  simp only [hc, Nat.cast_ofNat, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end InternalCatalan

end

end OAI
