import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section
open PowerSeries
namespace NCHitting

variable {F : Type*} [Field F] [CharZero F]

def integral (a : PowerSeries F) : PowerSeries F :=
  PowerSeries.mk fun r => match r with
    | 0 => 0
    | r + 1 => PowerSeries.coeff r a / (r + 1 : F)

omit [CharZero F] in
@[simp] theorem coeff_integral_zero (a : PowerSeries F) :
    PowerSeries.coeff 0 (integral a) = 0 := by simp [integral]

omit [CharZero F] in
@[simp] theorem coeff_integral_succ (a : PowerSeries F) (r : ℕ) :
    PowerSeries.coeff (r+1) (integral a) = PowerSeries.coeff r a / (r+1 : F) := by
  simp [integral]

omit [CharZero F] in
@[simp] theorem constantCoeff_integral (a : PowerSeries F) :
    PowerSeries.constantCoeff (integral a) = 0 := by
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using coeff_integral_zero a

@[simp] theorem derivative_integral (a : PowerSeries F) :
    PowerSeries.derivative (R := F) (integral a) = a := by
  ext r
  rw [PowerSeries.coeff_derivative, coeff_integral_succ]
  exact div_mul_cancel₀ _ (by simpa using (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r) : ((r + 1 : ℕ) : F) ≠ 0))

theorem integral_unique (a b : PowerSeries F)
    (hd : PowerSeries.derivative (R := F) b = a) (hc : PowerSeries.constantCoeff b = 0) :
    b = integral a := by
  apply PowerSeries.derivative.ext
  · simpa using hd
  · simpa using hc

omit [CharZero F] in
@[simp] theorem integral_zero : integral (0 : PowerSeries F) = 0 := by
  ext r
  cases r <;> simp [integral]

omit [CharZero F] in
@[simp] theorem integral_add (a b : PowerSeries F) :
    integral (a+b) = integral a + integral b := by
  ext r
  cases r with
  | zero => simp
  | succ r => simp [add_div]

omit [CharZero F] in
@[simp] theorem integral_smul (c : F) (a : PowerSeries F) :
    integral (c • a) = c • integral a := by
  ext r
  cases r with
  | zero => simp
  | succ r => simp [smul_eq_mul, mul_div_assoc]

def kernel (i : ℕ) : PowerSeries F :=
  PowerSeries.mk fun r => (-1 : F)^r / (i : F)^(r+1)

omit [CharZero F] in
@[simp] theorem coeff_kernel (i r : ℕ) :
    PowerSeries.coeff r (kernel (F := F) i) = (-1 : F)^r / (i : F)^(r+1) := by
  simp [kernel]

def J (i : ℕ) (a : PowerSeries F) : PowerSeries F := integral (a * kernel i)

@[simp] theorem derivative_J (i : ℕ) (a : PowerSeries F) :
    PowerSeries.derivative (R := F) (J i a) = a * kernel i := by simp [J]

omit [CharZero F] in
@[simp] theorem constantCoeff_J (i : ℕ) (a : PowerSeries F) :
    PowerSeries.constantCoeff (J i a) = 0 := by simp [J]

omit [CharZero F] in
@[simp] theorem J_zero (i : ℕ) : J i (0 : PowerSeries F) = 0 := by simp [J]

omit [CharZero F] in
@[simp] theorem J_add (i : ℕ) (a b : PowerSeries F) :
    J i (a+b) = J i a + J i b := by simp [J, add_mul]

omit [CharZero F] in
@[simp] theorem J_smul (i : ℕ) (c : F) (a : PowerSeries F) :
    J i (c • a) = c • J i a := by simp [J]

def JLinear (i : ℕ) : PowerSeries F →ₗ[F] PowerSeries F where
  toFun := J i
  map_add' := J_add i
  map_smul' := J_smul i

omit [CharZero F] in
@[simp] theorem J_sum {ι : Type*} (i : ℕ) (s : Finset ι) (a : ι → PowerSeries F) :
    J i (∑ j ∈ s, a j) = ∑ j ∈ s, J i (a j) :=
  map_sum (JLinear i) a s

omit [CharZero F] in
theorem coeff_J (i r : ℕ) (a : PowerSeries F) :
    PowerSeries.coeff r (J i a) =
      ∑ q ∈ Finset.range r,
        ((-1 : F)^(r-q-1) / ((r : F) * (i : F)^(r-q))) * PowerSeries.coeff q a := by
  cases r with
  | zero => simp [J]
  | succ r =>
    rw [J, coeff_integral_succ, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    have hqr : q ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have hsub' : r+1-q = r-q+1 := by omega
    simp only [coeff_kernel, hsub', Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

omit [CharZero F] in
theorem coeff_J_eq_zero (i r : ℕ) (a : PowerSeries F)
    (h : ∀ q < r, PowerSeries.coeff q a = 0) :
    PowerSeries.coeff r (J i a) = 0 := by
  rw [coeff_J]
  apply Finset.sum_eq_zero
  intro q hq
  rw [h q (Finset.mem_range.mp hq), mul_zero]

theorem kernel_mul_linear (i : ℕ) (hi : i ≠ 0) :
    kernel (F := F) i * (PowerSeries.X + PowerSeries.C (i : F)) = 1 := by
  have hiF : (i : F) ≠ 0 := Nat.cast_ne_zero.mpr hi
  ext r
  cases r with
  | zero => simp [mul_add, kernel, hiF]
  | succ r =>
    rw [mul_add, map_add, PowerSeries.coeff_mul_C]
    have hx : PowerSeries.coeff (r+1) (kernel (F := F) i * PowerSeries.X) =
        PowerSeries.coeff r (kernel (F := F) i) := by
      simp
    rw [hx]
    simp only [coeff_kernel, PowerSeries.coeff_one, Nat.succ_ne_zero, ite_false,
      pow_succ]
    field_simp
    ring

def wordSeries {n : ℕ} : List (Fin n) → PowerSeries F
  | [] => 1
  | i :: w => J (i.val + 1) (wordSeries w)

omit [CharZero F] in
@[simp] theorem wordSeries_nil {n : ℕ} : wordSeries (F := F) (n := n) [] = 1 := rfl
omit [CharZero F] in
@[simp] theorem wordSeries_cons {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    wordSeries (F := F) (i :: w) = J (i.val + 1) (wordSeries w) := rfl

@[simp] theorem derivative_wordSeries_cons {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    PowerSeries.derivative (R := F) (wordSeries (i :: w)) = wordSeries w * kernel (i.val + 1) := by simp

omit [CharZero F] in
@[simp] theorem constantCoeff_wordSeries_cons {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    PowerSeries.constantCoeff (wordSeries (F := F) (i :: w)) = 0 := by simp

omit [CharZero F] in
theorem coeff_wordSeries_below {n : ℕ} (w : List (Fin n)) (r : ℕ) (hr : r < w.length) :
    PowerSeries.coeff r (wordSeries (F := F) w) = 0 := by
  induction w generalizing r with
  | nil => simp at hr
  | cons i w ih =>
    rw [wordSeries_cons]
    apply coeff_J_eq_zero
    intro q hq
    apply ih q
    simp only [List.length_cons] at hr
    omega

omit [CharZero F] in
theorem length_le_order_wordSeries {n : ℕ} (w : List (Fin n)) :
    (w.length : ℕ∞) ≤ (wordSeries (F := F) w).order :=
  PowerSeries.nat_le_order _ _ (coeff_wordSeries_below w)

section Map
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero F] [CharZero K] in
theorem map_integral (f : F →+* K) (a : PowerSeries F) :
    PowerSeries.map f (integral a) = integral (PowerSeries.map f a) := by
  ext r
  cases r with
  | zero => simp
  | succ r => simp [map_div₀]

omit [CharZero F] [CharZero K] in
theorem map_kernel (f : F →+* K) (i : ℕ) :
    PowerSeries.map f (kernel (F := F) i) = kernel (F := K) i := by
  ext r
  simp [map_div₀]

omit [CharZero F] [CharZero K] in
theorem map_J (f : F →+* K) (i : ℕ) (a : PowerSeries F) :
    PowerSeries.map f (J i a) = J i (PowerSeries.map f a) := by
  simp [J, map_integral, map_kernel]

omit [CharZero F] [CharZero K] in
theorem map_wordSeries (f : F →+* K) {n : ℕ} (w : List (Fin n)) :
    PowerSeries.map f (wordSeries (F := F) w) = wordSeries (F := K) w := by
  induction w with
  | nil => simp
  | cons i w ih => simp [map_J, ih]

end Map

end NCHitting

end

end OAI
