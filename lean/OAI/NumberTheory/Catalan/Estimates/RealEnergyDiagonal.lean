import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace InternalCatalan

section

open Set Real

def realCoordinate (t : ℝ) : ℝ := t / (1 + sqrt (1 - t ^ 2))

def realCoordinateInv (x : ℝ) : ℝ := 2 * x / (1 + x ^ 2)

private theorem coordinate_radicand_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - x ^ 2 := by
  have hsq : x ^ 2 < 1 := by
    simpa only [sq_abs, one_pow] using
      (sq_lt_sq₀ (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1)).mpr (abs_lt.mpr hx)
  linarith

theorem realCoordinateInv_mem {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    realCoordinateInv x ∈ Ioo (-1 : ℝ) 1 := by
  have hd : 0 < 1 + x ^ 2 := by positivity
  constructor
  · unfold realCoordinateInv
    apply (lt_div_iff₀ hd).mpr
    nlinarith [sq_pos_of_ne_zero (by linarith [hx.1] : x + 1 ≠ 0)]
  · unfold realCoordinateInv
    apply (div_lt_iff₀ hd).mpr
    nlinarith [sq_pos_of_ne_zero (by linarith [hx.2] : x - 1 ≠ 0)]

theorem sqrt_one_sub_realCoordinateInv_sq {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    sqrt (1 - realCoordinateInv x ^ 2) = (1 - x ^ 2) / (1 + x ^ 2) := by
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  have hsq : 1 - realCoordinateInv x ^ 2 =
      ((1 - x ^ 2) / (1 + x ^ 2)) ^ 2 := by
    unfold realCoordinateInv
    field_simp
    ring
  rw [hsq, sqrt_sq (div_nonneg (coordinate_radicand_pos hx).le (by positivity))]

theorem realCoordinate_mem {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    realCoordinate t ∈ Ioo (-1 : ℝ) 1 := by
  have hs : 0 ≤ sqrt (1 - t ^ 2) := sqrt_nonneg _
  have hd : 0 < 1 + sqrt (1 - t ^ 2) := by positivity
  constructor
  · unfold realCoordinate
    apply (lt_div_iff₀ hd).mpr
    linarith [ht.1]
  · unfold realCoordinate
    apply (div_lt_iff₀ hd).mpr
    linarith [ht.2]

theorem realCoordinate_left_inverse {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    realCoordinate (realCoordinateInv x) = x := by
  unfold realCoordinate
  rw [sqrt_one_sub_realCoordinateInv_sq hx]
  unfold realCoordinateInv
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  have hs : 1 + (1 - x ^ 2) / (1 + x ^ 2) = 2 / (1 + x ^ 2) := by
    field_simp
    ring
  rw [hs]
  field_simp

theorem realCoordinate_right_inverse {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    realCoordinateInv (realCoordinate t) = t := by
  have hs : sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 :=
    sq_sqrt (coordinate_radicand_pos ht).le
  have hd : 1 + sqrt (1 - t ^ 2) ≠ 0 := by positivity
  have hden : 1 + (t / (1 + sqrt (1 - t ^ 2))) ^ 2 =
      2 / (1 + sqrt (1 - t ^ 2)) := by
    field_simp
    nlinarith only [hs]
  unfold realCoordinateInv realCoordinate
  rw [hden]
  field_simp

theorem realCoordinate_bijOn :
    BijOn realCoordinate (Ioo (-1 : ℝ) 1) (Ioo (-1 : ℝ) 1) := by
  refine ⟨fun t ht => realCoordinate_mem ht, ?_, ?_⟩
  · intro t ht u hu he
    have h := congrArg realCoordinateInv he
    simpa only [realCoordinate_right_inverse ht, realCoordinate_right_inverse hu] using h
  · intro x hx
    exact ⟨realCoordinateInv x, realCoordinateInv_mem hx, realCoordinate_left_inverse hx⟩

theorem hasDerivAt_realCoordinateInv (x : ℝ) :
    HasDerivAt realCoordinateInv (2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2) x := by
  have h := ((hasDerivAt_id x).const_mul 2).div
    ((hasDerivAt_pow 2 x).const_add 1) (by positivity : 1 + x ^ 2 ≠ 0)
  have heq : ((fun y : ℝ => 2 * id y) / (fun y : ℝ => 1 + y ^ 2)) =
      realCoordinateInv := by
    funext y
    rfl
  rw [heq] at h
  have hd : (2 * 1 * (1 + x ^ 2) - 2 * id x * (((2 : ℕ) : ℝ) * x ^ (2 - 1))) /
      (1 + x ^ 2) ^ 2 = 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2 := by
    norm_num
    ring
  rw [hd] at h
  exact h

theorem continuous_realCoordinateInv : Continuous realCoordinateInv :=
  (continuous_const.mul continuous_id).div
    (continuous_const.add (continuous_id.pow 2)) (fun x => by positivity)

theorem realCoordinate_weight_jacobian {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (|realCoordinateInv x| / sqrt (1 - realCoordinateInv x ^ 2)) *
        (2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2) =
      4 * |x| / (1 + x ^ 2) ^ 2 := by
  rw [sqrt_one_sub_realCoordinateInv_sq hx]
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  have hr : 1 - x ^ 2 ≠ 0 := (coordinate_radicand_pos hx).ne'
  unfold realCoordinateInv
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (by positivity : 0 < 1 + x ^ 2)]
  field_simp
  ring

end

section

open Set

section

theorem realCoordinateInv_denominator_pos (x : ℝ) : 0 < 1 + x ^ 2 := by
  positivity

theorem abs_realCoordinateInv (x : ℝ) :
    |realCoordinateInv x| = 2 * |x| / (1 + x ^ 2) := by
  unfold realCoordinateInv
  simp only [abs_div, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (realCoordinateInv_denominator_pos x)]

theorem realCoordinateInv_sub (x y : ℝ) :
    realCoordinateInv x - realCoordinateInv y =
      2 * (x - y) * (1 - x * y) / ((1 + x ^ 2) * (1 + y ^ 2)) := by
  have hx : 1 + x ^ 2 ≠ 0 := (realCoordinateInv_denominator_pos x).ne'
  have hy : 1 + y ^ 2 ≠ 0 := (realCoordinateInv_denominator_pos y).ne'
  unfold realCoordinateInv
  field_simp [hx, hy]
  ring

theorem energy_one_sub_mul_pos {x y : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - x * y := by
  apply sub_pos.mpr
  calc
    x * y ≤ |x * y| := le_abs_self _
    _ = |x| * |y| := abs_mul x y
    _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left (abs_lt.mpr hy).le (abs_nonneg x)
    _ = |x| := mul_one _
    _ < 1 := abs_lt.mpr hx

theorem abs_realCoordinateInv_sub {x y : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    |realCoordinateInv x - realCoordinateInv y| =
      2 * |x - y| * (1 - x * y) / ((1 + x ^ 2) * (1 + y ^ 2)) := by
  rw [realCoordinateInv_sub]
  simp only [abs_div, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (energy_one_sub_mul_pos hx hy),
    abs_of_pos (realCoordinateInv_denominator_pos x),
    abs_of_pos (realCoordinateInv_denominator_pos y)]

theorem one_sub_realCoordinateInv_mul (x s : ℝ) :
    1 - realCoordinateInv x * s = (1 - 2 * x * s + x ^ 2) / (1 + x ^ 2) := by
  have hx : 1 + x ^ 2 ≠ 0 := (realCoordinateInv_denominator_pos x).ne'
  unfold realCoordinateInv
  field_simp [hx]
  ring

theorem one_sub_realCoordinateInv (x : ℝ) :
    1 - realCoordinateInv x = (1 - x) ^ 2 / (1 + x ^ 2) := by
  have hx : 1 + x ^ 2 ≠ 0 := (realCoordinateInv_denominator_pos x).ne'
  unfold realCoordinateInv
  field_simp [hx]
  ring

theorem realCoordinateInv_kernel_numerator_pos (x : ℝ) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) : 0 < 1 - 2 * x * s + x ^ 2 := by
  have hp : 0 < (1 - s) * (1 + s) :=
    mul_pos (sub_pos.mpr hs.2) (by linarith [hs.1])
  nlinarith [sq_nonneg (x - s)]

theorem realCoordinateInv_kernel_pos (x : ℝ) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) : 0 < 1 - realCoordinateInv x * s := by
  rw [one_sub_realCoordinateInv_mul]
  exact div_pos (realCoordinateInv_kernel_numerator_pos x hs)
    (realCoordinateInv_denominator_pos x)

theorem one_sub_realCoordinateInv_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - realCoordinateInv x :=
  sub_pos.mpr (realCoordinateInv_mem hx).2

def realEnergyTau (e : ℝ) : ℝ := 1 - e
def realEnergyRho (e x : ℝ) : ℝ := 1 - e * (1 - x)
def realEnergySigma (e s : ℝ) : ℝ := 1 - e * Real.sqrt (1 - s)

theorem realEnergyTau_bounds {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8)) :
    0 < realEnergyTau e ∧ realEnergyTau e < 1 := by
  unfold realEnergyTau
  constructor <;> linarith [he.1, he.2]

theorem realEnergyRho_bounds {e x : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    1 - 2 * e < realEnergyRho e x ∧ realEnergyRho e x < 1 := by
  unfold realEnergyRho
  have h1 := mul_pos he.1 (sub_pos.mpr hx.2)
  have h2 := mul_pos he.1 (show 0 < x + 1 by linarith [hx.1])
  constructor <;> nlinarith

theorem realEnergyRho_mem {e x : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : x ∈ Ioo (-1 : ℝ) 1) : realEnergyRho e x ∈ Ioo (0 : ℝ) 1 := by
  have hb := realEnergyRho_bounds he hx
  exact ⟨by linarith [hb.1, he.2], hb.2⟩

theorem realEnergySigma_bounds {e s : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    1 - e < realEnergySigma e s ∧ realEnergySigma e s < 1 := by
  have hs0 : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.mpr (sub_pos.mpr hs.2)
  have hs1 : Real.sqrt (1 - s) < 1 := by
    have ht := Real.sqrt_lt_sqrt (sub_pos.mpr hs.2).le (show 1 - s < 1 by linarith [hs.1])
    simpa only [Real.sqrt_one] using ht
  unfold realEnergySigma
  have h1 := mul_pos he.1 hs0
  have h2 := mul_pos he.1 (sub_pos.mpr hs1)
  constructor <;> nlinarith

theorem realEnergySigma_mem {e s : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hs : s ∈ Ioo (0 : ℝ) 1) : realEnergySigma e s ∈ Ioo (0 : ℝ) 1 := by
  have hb := realEnergySigma_bounds he hs
  exact ⟨by linarith [hb.1, he.2], hb.2⟩

theorem realEnergyRho_mul_bounds {e x y : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    0 < realEnergyRho e x * realEnergyRho e y ∧
      realEnergyRho e x * realEnergyRho e y < 1 ∧
      1 - realEnergyRho e x * realEnergyRho e y ≤ 4 * e := by
  have hxm := realEnergyRho_mem he hx
  have hym := realEnergyRho_mem he hy
  have hxb := (realEnergyRho_bounds he hx).1
  have hyb := (realEnergyRho_bounds he hy).1
  refine ⟨mul_pos hxm.1 hym.1, ?_, ?_⟩
  · have hm := mul_lt_mul_of_pos_left hym.2 hxm.1
    nlinarith [hxm.2]
  · have he0 : 0 < 1 - 2 * e := by linarith [he.2]
    have hp := mul_le_mul hxb.le hyb.le he0.le hxm.1.le
    nlinarith [sq_nonneg e]

theorem realEnergySigma_mul_bounds {e s t : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 - e) ^ 2 ≤ realEnergySigma e s * realEnergySigma e t ∧
      realEnergySigma e s * realEnergySigma e t < 1 := by
  have hsm := realEnergySigma_mem he hs
  have htm := realEnergySigma_mem he ht
  have hsb := (realEnergySigma_bounds he hs).1
  have htb := (realEnergySigma_bounds he ht).1
  have he0 : 0 < 1 - e := by linarith [he.2]
  constructor
  · have hp := mul_le_mul hsb.le htb.le he0.le hsm.1.le
    nlinarith
  · have hp := mul_lt_mul_of_pos_left htm.2 hsm.1
    nlinarith [hsm.2]

end

open Set
open scoped BigOperators

theorem prod_pair_factors {m : ℕ} (w : Fin m → ℝ) :
    (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (w i * w j)) =
      ∏ i : Fin m, w i ^ (m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
    simp only [Fin.prod_Ioi_succ]
    rw [ih, Fin.prod_univ_succ]
    simp only [Nat.add_sub_cancel, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_fin]
    by_cases hm : m = 0
    · subst m
      simp
    · have hp (i : Fin m) : w i.succ * w i.succ ^ (m - 1) = w i.succ ^ m := by
        rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)]
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      simp_rw [hp]

theorem prod_pair_const (m : ℕ) (c : ℝ) :
    (∏ i : Fin m, ∏ _j ∈ Finset.Ioi i, c) = c ^ (m.choose 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
    simp only [Fin.prod_Ioi_succ]
    rw [ih]
    simp only [Finset.prod_const, Finset.card_fin]
    have hc : (m + 1).choose 2 = m + m.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ m 1
    rw [hc, pow_add]

private theorem abs_inv_sub_inv_eq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    |a⁻¹ - b⁻¹| = |a - b| / (|a| * |b|) := by
  have heq : a⁻¹ - b⁻¹ = -(a - b) / (a * b) := by
    field_simp [ha, hb]
    ring
  rw [heq, abs_div, abs_neg, abs_mul]

theorem abs_vandermonde_inv {m : ℕ} (x : Fin m → ℝ) (hx0 : ∀ i, x i ≠ 0) :
    |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, ((x j)⁻¹ - (x i)⁻¹)| =
      |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (x j - x i)| /
        (∏ i : Fin m, |x i| ^ (m - 1)) := by
  have hp (i j : Fin m) : |(x j)⁻¹ - (x i)⁻¹| =
      |x j - x i| / (|x i| * |x j|) := by
    rw [abs_inv_sub_inv_eq (hx0 j) (hx0 i), mul_comm |x j| |x i|]
  simp_rw [Finset.abs_prod, hp, Finset.prod_div_distrib]
  rw [prod_pair_factors]

theorem prod_realCoordinateInv_kernel {m : ℕ} (x s : Fin m → ℝ) :
    (∏ i : Fin m, ∏ j : Fin m, (1 - realCoordinateInv (x i) * s j)) =
      (∏ i : Fin m, ∏ j : Fin m, (1 - 2 * x i * s j + x i ^ 2)) /
        (∏ i : Fin m, (1 + x i ^ 2) ^ m) := by
  simp_rw [one_sub_realCoordinateInv_mul, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem abs_vandermonde_realCoordinateInv {m : ℕ} (x : Fin m → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    |∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
      (realCoordinateInv (x j) - realCoordinateInv (x i))| =
      (2 : ℝ) ^ (m.choose 2) *
        |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (x j - x i)| *
        (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (1 - x i * x j)) /
        (∏ i : Fin m, (1 + x i ^ 2) ^ (m - 1)) := by
  have hp (i j : Fin m) :
      |realCoordinateInv (x j) - realCoordinateInv (x i)| =
        2 * |x j - x i| * (1 - x i * x j) /
          ((1 + x i ^ 2) * (1 + x j ^ 2)) := by
    simpa only [mul_comm (x j) (x i), mul_comm (1 + x j ^ 2) (1 + x i ^ 2)] using
      abs_realCoordinateInv_sub (hx j) (hx i)
  simp_rw [Finset.abs_prod, hp, Finset.prod_div_distrib]
  rw [prod_pair_factors]
  simp only [Finset.prod_mul_distrib]
  rw [prod_pair_const]

end

open Set

theorem energy_cross_relative_size {x s : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    |x| * ((1 - x) + Real.sqrt (1 - s)) ≤
      3 * Real.sqrt (1 - 2 * x * s + x ^ 2) := by
  let b := Real.sqrt (1 - s)
  let q := Real.sqrt (1 - 2 * x * s + x ^ 2)
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hb2 : b ^ 2 = 1 - s := Real.sq_sqrt (sub_pos.mpr hs.2).le
  have hq2 : q ^ 2 = 1 - 2 * x * s + x ^ 2 :=
    Real.sq_sqrt (realCoordinateInv_kernel_numerator_pos x hs).le
  have hb1 : b ≤ 1 := by
    dsimp only [b]
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (show 1 - s ≤ 1 by linarith [hs.1])
  change |x| * ((1 - x) + b) ≤ 3 * q
  by_cases hx0 : 0 ≤ x
  · have ha0 : 0 ≤ 1 - x := (sub_pos.mpr hx.2).le
    have hdecomp : q ^ 2 = (1 - x) ^ 2 + 2 * x * b ^ 2 := by
      rw [hq2, hb2]
      ring
    have haq : 1 - x ≤ q := by
      apply (sq_le_sq₀ ha0 hq0).mp
      rw [hdecomp]
      nlinarith [mul_nonneg hx0 (sq_nonneg b)]
    have hxc : 0 ≤ 2 * x - x ^ 2 := by
      nlinarith [mul_nonneg hx0 ha0]
    have hxb : x * b ≤ q := by
      apply (sq_le_sq₀ (mul_nonneg hx0 hb0) hq0).mp
      rw [hdecomp]
      nlinarith [mul_nonneg hxc (sq_nonneg b), sq_nonneg (1 - x)]
    have hxa : x * (1 - x) ≤ q := by
      calc
        _ ≤ 1 * (1 - x) := mul_le_mul_of_nonneg_right hx.2.le ha0
        _ ≤ q := by simpa only [one_mul] using haq
    rw [abs_of_nonneg hx0]
    nlinarith
  · have hxneg : x ≤ 0 := le_of_not_ge hx0
    have hq1 : 1 ≤ q := by
      apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hq0).mp
      rw [hq2]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hxneg hs.1.le, sq_nonneg x]
    have hab : 0 ≤ (1 - x) + b := by linarith [hx.2]
    calc
      _ ≤ 1 * ((1 - x) + b) :=
        mul_le_mul_of_nonneg_right (abs_lt.mpr hx).le hab
      _ ≤ 3 := by linarith [hx.1]
      _ ≤ 3 * q := by linarith

theorem realEnergy_cross_node_error {e x s : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    |x - realEnergyRho e x * realEnergySigma e s * x| ≤
      3 * e * Real.sqrt (1 - 2 * x * s + x ^ 2) := by
  let d := realEnergyRho e x * realEnergySigma e s
  let b := Real.sqrt (1 - s)
  have hr := realEnergyRho_mem he hx
  have ht := realEnergySigma_mem he hs
  have hd1 : d ≤ 1 := by
    calc
      d ≤ realEnergyRho e x * 1 := mul_le_mul_of_nonneg_left ht.2.le hr.1.le
      _ ≤ 1 := by simpa only [mul_one] using hr.2.le
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have herr : 1 - d ≤ e * ((1 - x) + b) := by
    calc
      1 - d = e * ((1 - x) + b) - (e * (1 - x)) * (e * b) := by
        dsimp only [d, b, realEnergyRho, realEnergySigma]
        ring
      _ ≤ e * ((1 - x) + b) :=
        sub_le_self _ (mul_nonneg
          (mul_nonneg he.1.le (sub_pos.mpr hx.2).le) (mul_nonneg he.1.le hb0))
  have hsize := energy_cross_relative_size hx hs
  change |x| * ((1 - x) + b) ≤ 3 * Real.sqrt (1 - 2 * x * s + x ^ 2) at hsize
  change |x - d * x| ≤ 3 * e * Real.sqrt (1 - 2 * x * s + x ^ 2)
  calc
    _ = (1 - d) * |x| := by
      rw [show x - d * x = (1 - d) * x by ring, abs_mul,
        abs_of_nonneg (sub_nonneg.mpr hd1)]
    _ ≤ (e * ((1 - x) + b)) * |x| := mul_le_mul_of_nonneg_right herr (abs_nonneg x)
    _ = e * (|x| * ((1 - x) + b)) := by ring
    _ ≤ e * (3 * Real.sqrt (1 - 2 * x * s + x ^ 2)) :=
      mul_le_mul_of_nonneg_left hsize he.1.le
    _ = _ := by ring

theorem realEnergy_cross_quadratic_le {e x s : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    1 - 2 * (realEnergyRho e x * realEnergySigma e s * x) * s +
        (realEnergyRho e x * realEnergySigma e s * x) ^ 2 ≤
      (1 + 3 * e) ^ 2 * (1 - 2 * x * s + x ^ 2) := by
  let u := realEnergyRho e x * realEnergySigma e s * x
  let δ := x - u
  let q := Real.sqrt (1 - 2 * x * s + x ^ 2)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = 1 - 2 * x * s + x ^ 2 :=
    Real.sq_sqrt (realCoordinateInv_kernel_numerator_pos x hs).le
  have hδ : |δ| ≤ 3 * e * q := realEnergy_cross_node_error he hx hs
  have hr0 : 0 ≤ 3 * e * q :=
    mul_nonneg (mul_nonneg (by norm_num) he.1.le) hq0
  have hsx : |s - x| ≤ q := by
    apply (sq_le_sq₀ (abs_nonneg _) hq0).mp
    rw [sq_abs, hq2]
    have hp : 0 < (1 - s) * (1 + s) :=
      mul_pos (sub_pos.mpr hs.2) (by linarith [hs.1])
    nlinarith
  have hδ2 : δ ^ 2 ≤ (3 * e * q) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg δ) hr0).mpr hδ
  have hcross : δ * (s - x) ≤ (3 * e * q) * q := by
    calc
      _ ≤ |δ * (s - x)| := le_abs_self _
      _ = |δ| * |s - x| := abs_mul _ _
      _ ≤ (3 * e * q) * q := mul_le_mul hδ hsx (abs_nonneg _) hr0
  change 1 - 2 * u * s + u ^ 2 ≤ (1 + 3 * e) ^ 2 * (1 - 2 * x * s + x ^ 2)
  calc
    _ = (1 - 2 * x * s + x ^ 2) + 2 * δ * (s - x) + δ ^ 2 := by
      dsimp only [δ]
      ring
    _ ≤ (1 - 2 * x * s + x ^ 2) + 2 * ((3 * e * q) * q) + (3 * e * q) ^ 2 := by
      nlinarith only [hcross, hδ2]
    _ = _ := by
      rw [← hq2]
      ring

theorem realEnergy_cross_kernel_le {e x s : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    -Real.log (1 - 2 * x * s + x ^ 2) ≤
      -Real.log (1 - 2 * (realEnergyRho e x * realEnergySigma e s * x) * s +
        (realEnergyRho e x * realEnergySigma e s * x) ^ 2) + 6 * e := by
  have hQ := realCoordinateInv_kernel_numerator_pos x hs
  have hD := realCoordinateInv_kernel_numerator_pos
    (realEnergyRho e x * realEnergySigma e s * x) hs
  have hfac : 0 < 1 + 3 * e := by linarith [he.1]
  have hlog := Real.log_le_log hD (realEnergy_cross_quadratic_le he hx hs)
  rw [Real.log_mul (pow_ne_zero 2 hfac.ne') hQ.ne', Real.log_pow] at hlog
  simp only [Nat.cast_ofNat] at hlog
  have hcost := Real.log_le_sub_one_of_pos hfac
  linarith only [hlog, hcost]

theorem energy_log_opposite_sign {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.log (1 + q) - Real.log (1 + r * q) ≤ 1 - r := by
  have hx : 0 < 1 + q := by linarith
  have hy : 0 < 1 + r * q := by positivity
  have hl := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at hl
  have he : (1 + q) / (1 + r * q) - 1 = (1 - r) * q / (1 + r * q) := by
    field_simp [hy.ne']
    ring
  rw [he] at hl
  calc
    _ ≤ (1 - r) * q / (1 + r * q) := hl
    _ ≤ 1 - r := by
      apply (div_le_iff₀ hy).mpr
      have hq := mul_le_mul_of_nonneg_left hq1 (sub_nonneg.mpr hr1)
      have hd := mul_le_mul_of_nonneg_left
        (show 1 ≤ 1 + r * q by nlinarith [mul_nonneg hr0 hq0]) (sub_nonneg.mpr hr1)
      nlinarith

theorem energy_damped_power_pos {u r : ℝ} (hu : u < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : 0 < 1 - r * u := by
  by_cases hu0 : 0 ≤ u
  · have hm := mul_le_mul_of_nonneg_right hr1 hu0
    nlinarith
  · have hm := mul_nonpos_of_nonneg_of_nonpos hr0 (le_of_not_ge hu0)
    linarith

theorem realEnergy_power_kernel_le {e x y : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    Real.log (1 - x * y) ≤
      Real.log (1 - (realEnergyRho e x * realEnergyRho e y) * (x * y)) + 4 * e := by
  let r := realEnergyRho e x * realEnergyRho e y
  have hr := realEnergyRho_mul_bounds he hx hy
  have hr0 : 0 ≤ r := hr.1.le
  have hr1 : r ≤ 1 := hr.2.1.le
  have hrerr : 1 - r ≤ 4 * e := hr.2.2
  have hu : |x * y| < 1 := by
    rw [abs_mul]
    calc
      |x| * |y| ≤ |x| * 1 :=
        mul_le_mul_of_nonneg_left (abs_lt.mpr hy).le (abs_nonneg x)
      _ = |x| := mul_one _
      _ < 1 := abs_lt.mpr hx
  change Real.log (1 - x * y) ≤ Real.log (1 - r * (x * y)) + 4 * e
  by_cases hxy : 0 ≤ x * y
  · have hm := mul_le_mul_of_nonneg_right hr1 hxy
    have hl := Real.log_le_log (energy_one_sub_mul_pos hx hy)
      (show 1 - x * y ≤ 1 - r * (x * y) by nlinarith)
    linarith [he.1]
  · have hq0 : 0 ≤ -(x * y) := by linarith
    have hq1 : -(x * y) ≤ 1 := by linarith [(abs_lt.mp hu).1]
    have hl := energy_log_opposite_sign hq0 hq1 hr0 hr1
    have heq : 1 + r * -(x * y) = 1 - r * (x * y) := by ring
    rw [heq] at hl
    change Real.log (1 - x * y) - Real.log (1 - r * (x * y)) ≤ 1 - r at hl
    linarith

open Set

theorem realEnergy_power_diagonal_nonneg_side {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : 0 ≤ x) :
    1 - x ≤ 1 - realEnergyRho e x ^ 2 * x ^ 2 := by
  have hr := realEnergyRho_mem he hx
  have hr2 : realEnergyRho e x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hr.1.le (sub_nonneg.mpr hr.2.le)]
  have hp := mul_le_mul_of_nonneg_right hr2 (sq_nonneg x)
  have hxx := mul_nonneg hx0 (sub_nonneg.mpr hx.2.le)
  nlinarith

theorem realEnergy_power_diagonal_nonpos_side {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≤ 0) :
    e ≤ 1 - realEnergyRho e x ^ 2 * x ^ 2 := by
  have hr := realEnergyRho_mem he hx
  have he0 : 0 ≤ 1 - e := by linarith [he.2]
  have hrle : realEnergyRho e x ≤ 1 - e := by
    unfold realEnergyRho
    nlinarith [mul_nonpos_of_nonneg_of_nonpos he.1.le hx0]
  have hr2 : realEnergyRho e x ^ 2 ≤ (1 - e) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrle) (add_nonneg he0 hr.1.le)]
  have hxx : x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - x by linarith [hx.2])
      (show 0 ≤ 1 + x by linarith [hx.1])]
  have hp := mul_le_mul_of_nonneg_left hxx (sq_nonneg (realEnergyRho e x))
  have hee := mul_nonneg he.1.le he0
  nlinarith

theorem realEnergy_log_power_diagonal_ge {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Real.log (1 - x) + Real.log e - Real.log 2 ≤
      Real.log (1 - realEnergyRho e x ^ 2 * x ^ 2) := by
  by_cases hx0 : 0 ≤ x
  · have hl := Real.log_le_log (sub_pos.mpr hx.2)
      (realEnergy_power_diagonal_nonneg_side he hx hx0)
    have he2 := Real.log_le_log he.1 (show e ≤ 2 by linarith [he.2])
    linarith
  · have hl := Real.log_le_log he.1
      (realEnergy_power_diagonal_nonpos_side he hx (le_of_not_ge hx0))
    have hx2 := Real.log_le_log (sub_pos.mpr hx.2)
      (show 1 - x ≤ 2 by linarith [hx.1])
    linarith

theorem realEnergy_sigma_diagonal_ge {e s : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hs : s ∈ Ioo (0 : ℝ) 1) :
    e * Real.sqrt (1 - s) ≤ 1 - realEnergySigma e s ^ 2 := by
  have hs0 : 0 ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (1 - s) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [hs.1])
  have ht0 : 0 ≤ e * Real.sqrt (1 - s) := mul_nonneg he.1.le hs0
  have ht1 : e * Real.sqrt (1 - s) ≤ 1 := by
    have hp := mul_le_mul_of_nonneg_left hs1 he.1.le
    nlinarith [he.2]
  have hp := mul_nonneg ht0 (sub_nonneg.mpr ht1)
  unfold realEnergySigma
  nlinarith

theorem realEnergy_log_sigma_diagonal_ge {e s : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hs : s ∈ Ioo (0 : ℝ) 1) :
    Real.log e + Real.log (1 - s) / 2 ≤ Real.log (1 - realEnergySigma e s ^ 2) := by
  have hs0 : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.mpr (sub_pos.mpr hs.2)
  have hl := Real.log_le_log (mul_pos he.1 hs0) (realEnergy_sigma_diagonal_ge he hs)
  rw [Real.log_mul he.1.ne' hs0.ne', Real.log_sqrt (sub_pos.mpr hs.2).le] at hl
  exact hl

end InternalCatalan

end

end OAI
