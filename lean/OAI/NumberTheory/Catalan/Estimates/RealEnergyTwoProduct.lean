import OAI.NumberTheory.Catalan.Energy.RealSheetIntegral

namespace OAI

noncomputable section

namespace InternalCatalan

section

open scoped BigOperators

theorem energy_row_weight_coordinate (p q : ℕ) (x : ℝ) :
    |realCoordinateInv x| ^ p * (1 - realCoordinateInv x) ^ q =
      (2 : ℝ) ^ p * |x| ^ p * (1 - x) ^ (2 * q) /
        (1 + x ^ 2) ^ (p + q) := by
  rw [abs_realCoordinateInv, one_sub_realCoordinateInv]
  simp only [div_pow, mul_pow, pow_add, pow_mul]
  ring

theorem prod_energy_row_weight_coordinate (N : ℕ) (x : Fin (n N) → ℝ) :
    (∏ i : Fin (n N),
      (|realCoordinateInv (x i)| ^ (Cdegree N - 1) *
        (1 - realCoordinateInv (x i)) ^ h N)) =
      (2 : ℝ) ^ (n N * (Cdegree N - 1)) *
        (∏ i : Fin (n N), (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) /
        (∏ i : Fin (n N), (1 + x i ^ 2) ^ (Cdegree N - 1 + h N)) := by
  simp_rw [energy_row_weight_coordinate]
  simp only [Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_fin]
  rw [← pow_mul, Nat.mul_comm (Cdegree N - 1) (n N)]
  ring

theorem energy_quadratic_weight_cancel {N : ℕ} (hN : 0 < N) (x : ℝ) :
    (1 + x ^ 2) ^ n N /
      ((1 + x ^ 2) ^ (n N - 1) *
        (1 + x ^ 2) ^ (Cdegree N - 1 + h N)) =
      1 / (1 + x ^ 2) ^ (H N - 2) := by
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (realCoordinateInv_denominator_pos x)
  have he : (n N - 1) + (Cdegree N - 1 + h N) = n N + (H N - 2) := by
    unfold n Cdegree h H
    omega
  rw [← pow_add, he, pow_add]
  field_simp

theorem prod_energy_quadratic_weight_cancel {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) :
    (∏ i : Fin (n N), (1 + x i ^ 2) ^ n N) /
      ((∏ i : Fin (n N), (1 + x i ^ 2) ^ (n N - 1)) *
        (∏ i : Fin (n N), (1 + x i ^ 2) ^ (Cdegree N - 1 + h N))) =
      1 / (∏ i : Fin (n N), (1 + x i ^ 2) ^ (H N - 2)) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  simp_rw [energy_quadratic_weight_cancel hN]
  simp only [Finset.prod_div_distrib, Finset.prod_const_one]

theorem energy_abs_node_weight_cancel {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx0 : x ≠ 0) :
    |x| ^ (Cdegree N - 1) *
      |x| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) = |x| ^ A N := by
  have he : ((Cdegree N - 1 : ℕ) : ℤ) +
      ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) = (A N : ℤ) := by
    rw [← add_sub_assoc]
    exact energy_abs_node_exponent hN
  calc
    _ = |x| ^ (((Cdegree N - 1 : ℕ) : ℤ) +
        ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) := by
      rw [zpow_add₀ (abs_ne_zero.mpr hx0), zpow_natCast]
    _ = |x| ^ A N := by rw [he, zpow_natCast]

end

open Set
open scoped BigOperators

def realPrincipalIntegrand (N : ℕ) (x s : Fin (n N) → ℝ) : ℝ :=
  (|∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i,
      (realCoordinateInv (x j) - realCoordinateInv (x i))| *
    |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)| ^ 2 /
    (∏ i : Fin (n N), ∏ j : Fin (n N), (1 - realCoordinateInv (x i) * s j))) *
    (∏ j : Fin (n N), (s j ^ b N * (1 - s j) ^ q N)) *
    (∏ i : Fin (n N), (|realCoordinateInv (x i)| ^ (Cdegree N - 1) *
      (1 - realCoordinateInv (x i)) ^ h N))

def realEnergyMajorantOne (N : ℕ) (x s : Fin (n N) → ℝ) : ℝ :=
  realPrincipalIntegrand N x s / (2 : ℝ) ^ ((n N).choose 2) *
    (∏ i : Fin (n N), ((1 + x i ^ 2) ^ (((n N : ℝ) - 1) / 2) *
      |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))))

def realEnergyMajorantTwo (N : ℕ) (x s : Fin (n N) → ℝ) : ℝ :=
  realPrincipalIntegrand N x s *
    |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, ((x j)⁻¹ - (x i)⁻¹)| *
    (∏ i : Fin (n N), |x i| ^ g N)

private theorem principal_kernel_product_pos (N : ℕ) (x s : Fin (n N) → ℝ)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    0 < ∏ i : Fin (n N), ∏ j : Fin (n N), (1 - realCoordinateInv (x i) * s j) := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  exact realCoordinateInv_kernel_pos (x i) (hs j)

private theorem principal_s_weight_pos (N : ℕ) (s : Fin (n N) → ℝ)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    0 < ∏ j : Fin (n N), (s j ^ b N * (1 - s j) ^ q N) := by
  apply Finset.prod_pos
  intro j _
  exact mul_pos (pow_pos (hs j).1 _) (pow_pos (sub_pos.mpr (hs j).2) _)

private theorem principal_t_weight_nonneg (N : ℕ) (x : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ ∏ i : Fin (n N), (|realCoordinateInv (x i)| ^ (Cdegree N - 1) *
      (1 - realCoordinateInv (x i)) ^ h N) := by
  apply Finset.prod_nonneg
  intro i _
  exact mul_nonneg (pow_nonneg (abs_nonneg _) _)
    (pow_nonneg (one_sub_realCoordinateInv_pos (hx i)).le _)

theorem realPrincipalIntegrand_nonneg (N : ℕ) (x s : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    0 ≤ realPrincipalIntegrand N x s := by
  unfold realPrincipalIntegrand
  exact mul_nonneg
    (mul_nonneg
      (div_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))
        (principal_kernel_product_pos N x s hs).le)
      (principal_s_weight_pos N s hs).le)
    (principal_t_weight_nonneg N x hx)

theorem realPrincipalIntegrand_pos (N : ℕ) (x s : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hxi : Function.Injective x) (hsi : Function.Injective s) :
    0 < realPrincipalIntegrand N x s := by
  have hvt : (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i,
      (realCoordinateInv (x j) - realCoordinateInv (x i))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    intro htji
    have hji : x j = x i := by
      have hc := congrArg realCoordinate htji
      simpa only [realCoordinate_left_inverse (hx j),
        realCoordinate_left_inverse (hx i)] using hc
    exact (ne_of_gt (Finset.mem_Ioi.mp hj)) (hxi hji)
  have hvs : (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun hji => (ne_of_gt (Finset.mem_Ioi.mp hj)) (hsi hji))
  have htw : 0 < ∏ i : Fin (n N),
      (|realCoordinateInv (x i)| ^ (Cdegree N - 1) *
        (1 - realCoordinateInv (x i)) ^ h N) := by
    apply Finset.prod_pos
    intro i _
    have hti : realCoordinateInv (x i) ≠ 0 := by
      unfold realCoordinateInv
      exact div_ne_zero (mul_ne_zero (by norm_num) (hx0 i))
        (realCoordinateInv_denominator_pos (x i)).ne'
    exact mul_pos (pow_pos (abs_pos.mpr hti) _)
      (pow_pos (one_sub_realCoordinateInv_pos (hx i)) _)
  unfold realPrincipalIntegrand
  exact mul_pos
    (mul_pos
      (div_pos (mul_pos (abs_pos.mpr hvt) (pow_pos (abs_pos.mpr hvs) _))
        (principal_kernel_product_pos N x s hs))
      (principal_s_weight_pos N s hs)) htw

theorem abs_sheetRealIntegrand_eq (N : ℕ) (x s : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    |sheetRealIntegrand N x s| = |realSheetDeterminant N x| * realPrincipalIntegrand N x s := by
  have htw : |∏ i : Fin (n N),
      (realCoordinateInv (x i) ^ (Cdegree N - 1) *
        (1 - realCoordinateInv (x i)) ^ h N)| =
      ∏ i : Fin (n N), (|realCoordinateInv (x i)| ^ (Cdegree N - 1) *
        (1 - realCoordinateInv (x i)) ^ h N) := by
    rw [Finset.abs_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp only [abs_mul, abs_pow, abs_of_pos (one_sub_realCoordinateInv_pos (hx i))]
  unfold sheetRealIntegrand realPrincipalIntegrand
  simp only [abs_div, abs_mul, abs_pow, htw,
    abs_of_pos (principal_kernel_product_pos N x s hs),
    abs_of_pos (principal_s_weight_pos N s hs)]
  ring

theorem abs_sheetRealIntegrand_le_majorantOne {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    |sheetRealIntegrand N x s| ≤
      (3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2) *
        realEnergyMajorantOne N x s := by
  rw [abs_sheetRealIntegrand_eq N x s hx hs]
  calc
    _ ≤ ((3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2) /
        (2 : ℝ) ^ ((n N).choose 2) *
        (∏ i : Fin (n N), ((1 + x i ^ 2) ^ (((n N : ℝ) - 1) / 2) *
          |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))))) *
          realPrincipalIntegrand N x s :=
      mul_le_mul_of_nonneg_right (realSheetDeterminant_abs_le hN x hx hx0)
        (realPrincipalIntegrand_nonneg N x s hx hs)
    _ = _ := by
      unfold realEnergyMajorantOne
      ring

theorem realPrincipalIntegrand_coordinate {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    realPrincipalIntegrand N x s =
      (2 : ℝ) ^ (n N * (Cdegree N - 1) + (n N).choose 2) *
        |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (x j - x i)| *
        |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)| ^ 2 *
        (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (1 - x i * x j)) *
        (∏ j : Fin (n N), (s j ^ b N * (1 - s j) ^ q N)) *
        (∏ i : Fin (n N), (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) /
        ((∏ i : Fin (n N), ∏ j : Fin (n N), (1 - 2 * x i * s j + x i ^ 2)) *
          (∏ i : Fin (n N), (1 + x i ^ 2) ^ (H N - 2))) := by
  unfold realPrincipalIntegrand
  rw [abs_vandermonde_realCoordinateInv x hx, prod_realCoordinateInv_kernel,
    prod_energy_row_weight_coordinate]
  calc
    _ = ((2 : ℝ) ^ ((n N).choose 2) * (2 : ℝ) ^ (n N * (Cdegree N - 1)) *
          |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (x j - x i)| *
          |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)| ^ 2 *
          (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (1 - x i * x j)) *
          (∏ j : Fin (n N), (s j ^ b N * (1 - s j) ^ q N)) *
          (∏ i : Fin (n N), (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) /
          (∏ i : Fin (n N), ∏ j : Fin (n N), (1 - 2 * x i * s j + x i ^ 2))) *
        ((∏ i : Fin (n N), (1 + x i ^ 2) ^ n N) /
          ((∏ i : Fin (n N), (1 + x i ^ 2) ^ (n N - 1)) *
            (∏ i : Fin (n N), (1 + x i ^ 2) ^ (Cdegree N - 1 + h N)))) := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    _ = _ := by
      rw [prod_energy_quadratic_weight_cancel hN x, pow_add]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem energy_one_quadratic_weight {N : ℕ} (hN : 0 < N) (x : ℝ) :
    (1 + x ^ 2) ^ (((n N : ℝ) - 1) / 2) / (1 + x ^ 2) ^ (H N - 2) =
      (1 + x ^ 2) ^
        (2 - (Cdegree N : ℝ) - (h N : ℝ) + ((n N : ℝ) - 1) / 2) := by
  have hH : 2 ≤ H N := by unfold H; omega
  have hc : ((H N - 2 : ℕ) : ℝ) = (Cdegree N : ℝ) + (h N : ℝ) - 2 := by
    rw [Nat.cast_sub hH, H_eq_Cdegree_add_h, Nat.cast_add, Nat.cast_ofNat]
  rw [← Real.rpow_sub_natCast (realCoordinateInv_denominator_pos x).ne']
  congr 1
  rw [hc]
  ring

theorem realEnergyMajorantOne_coordinate {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) :
    realEnergyMajorantOne N x s =
      (2 : ℝ) ^ (n N * (Cdegree N - 1)) *
        |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (x j - x i)| *
        |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)| ^ 2 *
        (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (1 - x i * x j)) *
        (∏ j : Fin (n N), (s j ^ b N * (1 - s j) ^ q N)) *
        (∏ i : Fin (n N),
          (|x i| ^ A N * (1 - x i) ^ (2 * h N) *
            (1 + x i ^ 2) ^
              (2 - (Cdegree N : ℝ) - (h N : ℝ) + ((n N : ℝ) - 1) / 2))) /
        (∏ i : Fin (n N), ∏ j : Fin (n N), (1 - 2 * x i * s j + x i ^ 2)) := by
  have hw :
      ((∏ i : Fin (n N), (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) *
        (∏ i : Fin (n N), ((1 + x i ^ 2) ^ (((n N : ℝ) - 1) / 2) *
          |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))))) /
          (∏ i : Fin (n N), (1 + x i ^ 2) ^ (H N - 2)) =
        ∏ i : Fin (n N),
          (|x i| ^ A N * (1 - x i) ^ (2 * h N) *
            (1 + x i ^ 2) ^
              (2 - (Cdegree N : ℝ) - (h N : ℝ) + ((n N : ℝ) - 1) / 2)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    calc
      _ = (|x i| ^ (Cdegree N - 1) *
            |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) *
          (1 - x i) ^ (2 * h N) *
          ((1 + x i ^ 2) ^ (((n N : ℝ) - 1) / 2) /
            (1 + x i ^ 2) ^ (H N - 2)) := by ring
      _ = _ := by rw [energy_abs_node_weight_cancel hN (hx0 i),
        energy_one_quadratic_weight hN]
  unfold realEnergyMajorantOne
  rw [realPrincipalIntegrand_coordinate hN x s hx]
  calc
    _ = ((2 : ℝ) ^ (n N * (Cdegree N - 1)) *
          |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (x j - x i)| *
          |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)| ^ 2 *
          (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (1 - x i * x j)) *
          (∏ j : Fin (n N), (s j ^ b N * (1 - s j) ^ q N)) /
          (∏ i : Fin (n N), ∏ j : Fin (n N), (1 - 2 * x i * s j + x i ^ 2))) *
        ((2 : ℝ) ^ ((n N).choose 2) / (2 : ℝ) ^ ((n N).choose 2)) *
        (((∏ i : Fin (n N), (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) *
          (∏ i : Fin (n N), ((1 + x i ^ 2) ^ (((n N : ℝ) - 1) / 2) *
            |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))))) /
          (∏ i : Fin (n N), (1 + x i ^ 2) ^ (H N - 2))) := by
      rw [pow_add]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      rw [div_self (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), mul_one, hw]
      ring

open Set
open scoped BigOperators

theorem energy_abs_node_weight_two_cancel {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx0 : x ≠ 0) :
    (|x| ^ (Cdegree N - 1) * |x| ^ g N) / |x| ^ (n N - 1) = |x| ^ A N := by
  calc
    _ = |x| ^ (Cdegree N - 1) *
        |x| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) := by
      rw [zpow_sub₀ (abs_ne_zero.mpr hx0)]
      simp only [zpow_natCast]
      ring
    _ = |x| ^ A N := energy_abs_node_weight_cancel hN hx0

theorem prod_energy_abs_node_weight_two_cancel {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) (hx0 : ∀ i, x i ≠ 0) :
    ((∏ i : Fin (n N), (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) *
      (∏ i : Fin (n N), |x i| ^ g N)) /
        (∏ i : Fin (n N), |x i| ^ (n N - 1)) =
      ∏ i : Fin (n N), (|x i| ^ A N * (1 - x i) ^ (2 * h N)) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  calc
    _ = ((|x i| ^ (Cdegree N - 1) * |x i| ^ g N) / |x i| ^ (n N - 1)) *
        (1 - x i) ^ (2 * h N) := by ring
    _ = _ := by rw [energy_abs_node_weight_two_cancel hN (hx0 i)]

theorem realEnergyMajorantTwo_coordinate {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) :
    realEnergyMajorantTwo N x s =
      (2 : ℝ) ^ (n N * (Cdegree N - 1) + (n N).choose 2) *
        |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (x j - x i)| ^ 2 *
        |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)| ^ 2 *
        (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (1 - x i * x j)) *
        (∏ j : Fin (n N), (s j ^ b N * (1 - s j) ^ q N)) *
        (∏ i : Fin (n N), (|x i| ^ A N * (1 - x i) ^ (2 * h N))) /
        ((∏ i : Fin (n N), ∏ j : Fin (n N), (1 - 2 * x i * s j + x i ^ 2)) *
          (∏ i : Fin (n N), (1 + x i ^ 2) ^ (H N - 2))) := by
  unfold realEnergyMajorantTwo
  rw [realPrincipalIntegrand_coordinate hN x s hx, abs_vandermonde_inv x hx0]
  calc
    _ = ((2 : ℝ) ^ (n N * (Cdegree N - 1) + (n N).choose 2) *
          |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (x j - x i)| ^ 2 *
          |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)| ^ 2 *
          (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (1 - x i * x j)) *
          (∏ j : Fin (n N), (s j ^ b N * (1 - s j) ^ q N)) /
          ((∏ i : Fin (n N), ∏ j : Fin (n N), (1 - 2 * x i * s j + x i ^ 2)) *
            (∏ i : Fin (n N), (1 + x i ^ 2) ^ (H N - 2)))) *
        (((∏ i : Fin (n N), (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) *
          (∏ i : Fin (n N), |x i| ^ g N)) /
            (∏ i : Fin (n N), |x i| ^ (n N - 1))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      rw [prod_energy_abs_node_weight_two_cancel hN x hx0]
      ring

end InternalCatalan

end

end OAI
