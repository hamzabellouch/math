import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace InternalCatalan

section

open scoped BigOperators

def centralCoeff (l : ℕ) : ℚ :=
  ((2 * l).choose l : ℚ) / 4 ^ l

def centralCoeffKernel (d : ℤ) : ℚ :=
  if 0 ≤ d ∧ d % 2 = 0 then centralCoeff (d.toNat / 2) else 0

@[simp] theorem centralCoeff_zero : centralCoeff 0 = 1 := by
  norm_num [centralCoeff]

@[simp] theorem centralCoeffKernel_zero : centralCoeffKernel 0 = 1 := by
  norm_num [centralCoeffKernel]

theorem centralCoeffKernel_of_neg {d : ℤ} (hd : d < 0) :
    centralCoeffKernel d = 0 := by
  simp [centralCoeffKernel, not_le.mpr hd]

theorem centralCoeffKernel_of_odd {d : ℤ} (hd : d % 2 ≠ 0) :
    centralCoeffKernel d = 0 := by
  simp [centralCoeffKernel, hd]

theorem centralCoeffKernel_two_mul (l : ℕ) :
    centralCoeffKernel (2 * (l : ℤ)) = centralCoeff l := by
  have hn : 0 ≤ 2 * (l : ℤ) := by positivity
  have he : (2 * (l : ℤ)) % 2 = 0 := by omega
  have ht : (2 * (l : ℤ)).toNat = 2 * l := by omega
  simp [centralCoeffKernel, hn, he, ht]

def momentScalar (i : ℕ) : ℚ :=
  if i % 2 = 0 then 2 / (((i + 1 : ℕ) : ℚ) * centralCoeff (i / 2)) else 0

@[simp] theorem momentScalar_zero : momentScalar 0 = 2 := by
  norm_num [momentScalar]

theorem momentScalar_even (l : ℕ) :
    momentScalar (2 * l) = 2 / (((2 * l + 1 : ℕ) : ℚ) * centralCoeff l) := by
  simp [momentScalar]

theorem momentScalar_odd (l : ℕ) : momentScalar (2 * l + 1) = 0 := by
  simp [momentScalar]

def boundaryMinus : ℕ → ℚ
  | 0 => 0
  | 1 => 2
  | d + 2 =>
      (((d + 1 : ℕ) : ℚ) * boundaryMinus d + momentScalar d + momentScalar (d + 1)) /
        ((d + 2 : ℕ) : ℚ)

def boundaryPlus : ℕ → ℚ
  | 0 => 0
  | 1 => 0
  | d + 2 =>
      ((d : ℚ) * boundaryPlus d + 2 / ((d + 1 : ℕ) : ℚ)) /
        ((d + 1 : ℕ) : ℚ)

@[simp] theorem boundaryMinus_zero : boundaryMinus 0 = 0 := rfl
@[simp] theorem boundaryMinus_one : boundaryMinus 1 = 2 := rfl
@[simp] theorem boundaryPlus_zero : boundaryPlus 0 = 0 := rfl
@[simp] theorem boundaryPlus_one : boundaryPlus 1 = 0 := rfl

theorem boundaryMinus_step (d : ℕ) :
    ((d + 2 : ℕ) : ℚ) * boundaryMinus (d + 2) =
      ((d + 1 : ℕ) : ℚ) * boundaryMinus d + momentScalar d + momentScalar (d + 1) := by
  have hd : ((d + 2 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [boundaryMinus]
  field_simp

theorem boundaryPlus_step (d : ℕ) :
    ((d + 1 : ℕ) : ℚ) * boundaryPlus (d + 2) =
      (d : ℚ) * boundaryPlus d + 2 / ((d + 1 : ℕ) : ℚ) := by
  have hd : ((d + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [boundaryPlus]
  field_simp

theorem boundaryMinus_unique (a : ℕ → ℚ)
    (hzero : a 0 = 0) (hone : a 1 = 2)
    (hstep : ∀ d, a (d + 2) =
      (((d + 1 : ℕ) : ℚ) * a d + momentScalar d + momentScalar (d + 1)) /
        ((d + 2 : ℕ) : ℚ)) (d : ℕ) : a d = boundaryMinus d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    cases d with
    | zero => exact hzero
    | succ d =>
      cases d with
      | zero => exact hone
      | succ d =>
        rw [hstep, boundaryMinus, ih d (by omega)]

theorem boundaryPlus_unique (a : ℕ → ℚ)
    (hzero : a 0 = 0) (hone : a 1 = 0)
    (hstep : ∀ d, a (d + 2) =
      ((d : ℚ) * a d + 2 / ((d + 1 : ℕ) : ℚ)) / ((d + 1 : ℕ) : ℚ))
    (d : ℕ) : a d = boundaryPlus d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    cases d with
    | zero => exact hzero
    | succ d =>
      cases d with
      | zero => exact hone
      | succ d =>
        rw [hstep, boundaryPlus, ih d (by omega)]

def momentRat (i j : ℕ) : ℚ :=
  if j ≤ i then
    boundaryMinus (i - j) -
      ∑ k ∈ Finset.range j, momentScalar (i - j + k) / ((k + 1 : ℕ) : ℚ)
  else
    boundaryPlus (j - i) -
      ∑ k ∈ Finset.range i, momentScalar k / ((j - i + k + 1 : ℕ) : ℚ)

theorem momentRat_of_le {i j : ℕ} (hji : j ≤ i) :
    momentRat i j = boundaryMinus (i - j) -
      ∑ k ∈ Finset.range j, momentScalar (i - j + k) / ((k + 1 : ℕ) : ℚ) := by
  simp [momentRat, hji]

theorem momentRat_of_lt {i j : ℕ} (hij : i < j) :
    momentRat i j = boundaryPlus (j - i) -
      ∑ k ∈ Finset.range i, momentScalar k / ((j - i + k + 1 : ℕ) : ℚ) := by
  simp [momentRat, not_le.mpr hij]

@[simp] theorem momentRat_zero_right (i : ℕ) : momentRat i 0 = boundaryMinus i := by
  simp [momentRat]

@[simp] theorem momentRat_zero_left (j : ℕ) : momentRat 0 j = boundaryPlus j := by
  cases j with
  | zero => simp [momentRat]
  | succ j => simp [momentRat]

theorem momentRat_diagonal (i : ℕ) :
    momentRat i i = -∑ k ∈ Finset.range i, momentScalar k / ((k + 1 : ℕ) : ℚ) := by
  simp [momentRat]

theorem momentRat_step (i j : ℕ) :
    momentRat i j - momentRat (i + 1) (j + 1) =
      momentScalar i / ((j + 1 : ℕ) : ℚ) := by
  by_cases hji : j ≤ i
  · have hs : j + 1 ≤ i + 1 := by omega
    have hi : i - j + j = i := Nat.sub_add_cancel hji
    rw [momentRat_of_le hji, momentRat_of_le hs]
    simp only [Nat.add_sub_add_right, Finset.sum_range_succ, hi]
    ring
  · have hij : i < j := Nat.lt_of_not_ge hji
    have hs : i + 1 < j + 1 := by omega
    have hj : j - i + i = j := Nat.sub_add_cancel (Nat.le_of_lt hij)
    rw [momentRat_of_lt hij, momentRat_of_lt hs]
    simp only [Nat.add_sub_add_right, Finset.sum_range_succ, hj]
    ring

def momentRatNegOne (j : ℕ) : ℚ := boundaryPlus (j + 1)

@[simp] theorem momentRatNegOne_eq (j : ℕ) :
    momentRatNegOne j = boundaryPlus (j + 1) := rfl

def harmonicRat (d n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / (((k + 1 : ℕ) : ℚ) ^ d)

@[simp] theorem harmonicRat_zero (d : ℕ) : harmonicRat d 0 = 0 := by
  simp [harmonicRat]

theorem harmonicRat_succ (d n : ℕ) :
    harmonicRat d (n + 1) = harmonicRat d n + 1 / (((n + 1 : ℕ) : ℚ) ^ d) := by
  simp [harmonicRat, Finset.sum_range_succ]

def zetaRat (i j : ℕ) : ℚ :=
  if i = j then -harmonicRat 2 i
  else (harmonicRat 1 i - harmonicRat 1 j) / ((i : ℚ) - (j : ℚ))

@[simp] theorem zetaRat_diagonal (i : ℕ) : zetaRat i i = -harmonicRat 2 i := by
  simp [zetaRat]

theorem zetaRat_of_ne {i j : ℕ} (hij : i ≠ j) :
    zetaRat i j = (harmonicRat 1 i - harmonicRat 1 j) / ((i : ℚ) - (j : ℚ)) := by
  simp [zetaRat, hij]

theorem zetaRat_symm (i j : ℕ) : zetaRat i j = zetaRat j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · rw [zetaRat_of_ne hij, zetaRat_of_ne (Ne.symm hij)]
    have hcast : (i : ℚ) ≠ (j : ℚ) := fun h => hij (Nat.cast_injective h)
    apply (div_eq_div_iff (sub_ne_zero.mpr hcast) (sub_ne_zero.mpr (Ne.symm hcast))).2
    ring

theorem zetaRat_step (i j : ℕ) :
    zetaRat i j - zetaRat (i + 1) (j + 1) =
      1 / (((i + 1 : ℕ) : ℚ) * ((j + 1 : ℕ) : ℚ)) := by
  have hi : ((i + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hj : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  by_cases hij : i = j
  · subst j
    rw [zetaRat_diagonal, zetaRat_diagonal, harmonicRat_succ]
    simp only [pow_two]
    ring
  · have hs : i + 1 ≠ j + 1 := by omega
    have hd : (i : ℚ) - (j : ℚ) ≠ 0 := by
      intro h
      have hc : (i : ℚ) = (j : ℚ) := sub_eq_zero.mp h
      exact hij (Nat.cast_injective hc)
    rw [zetaRat_of_ne hij, zetaRat_of_ne hs, harmonicRat_succ, harmonicRat_succ]
    simp only [pow_one, Nat.cast_add, Nat.cast_one]
    have hi' : (i : ℚ) + 1 ≠ 0 := by positivity
    have hj' : (j : ℚ) + 1 ≠ 0 := by positivity
    have hden : ((i : ℚ) + 1) - ((j : ℚ) + 1) = (i : ℚ) - (j : ℚ) := by ring
    rw [hden]
    field_simp [hi', hj', hd]
    ring

end

theorem centralCoeff_pos (l : ℕ) : 0 < centralCoeff l := by
  unfold centralCoeff
  apply div_pos
  · exact_mod_cast Nat.centralBinom_pos l
  · positivity

theorem centralCoeff_ne_zero (l : ℕ) : centralCoeff l ≠ 0 :=
  ne_of_gt (centralCoeff_pos l)

theorem centralCoeff_step (l : ℕ) :
    ((2 * l + 2 : ℕ) : ℚ) * centralCoeff (l + 1) =
      ((2 * l + 1 : ℕ) : ℚ) * centralCoeff l := by
  have hc : ((l + 1 : ℕ) : ℚ) * (((2 * (l + 1)).choose (l + 1) : ℕ) : ℚ) =
      2 * ((2 * l + 1 : ℕ) : ℚ) * (((2 * l).choose l : ℕ) : ℚ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ l
  have hp : (4 : ℚ) ^ l ≠ 0 := pow_ne_zero l (by norm_num)
  unfold centralCoeff
  rw [pow_succ]
  push_cast at hc ⊢
  field_simp
  nlinarith only [hc]

def boundaryFactor (z : ℕ) : ℚ :=
  if z % 2 = 0 then centralCoeff (z / 2)
  else 1 / ((z : ℚ) * centralCoeff ((z - 1) / 2))

theorem boundaryFactor_even (l : ℕ) : boundaryFactor (2 * l) = centralCoeff l := by
  simp [boundaryFactor]

theorem boundaryFactor_odd (l : ℕ) :
    boundaryFactor (2 * l + 1) = 1 / (((2 * l + 1 : ℕ) : ℚ) * centralCoeff l) := by
  simp [boundaryFactor]

@[simp] theorem boundaryFactor_zero : boundaryFactor 0 = 1 := by
  norm_num [boundaryFactor]

@[simp] theorem boundaryFactor_one : boundaryFactor 1 = 1 := by
  norm_num [boundaryFactor]

theorem boundaryFactor_pos (z : ℕ) : 0 < boundaryFactor z := by
  unfold boundaryFactor
  split_ifs with hz
  · exact centralCoeff_pos _
  · have hpos : 0 < z := by omega
    apply div_pos (by norm_num)
    exact mul_pos (by exact_mod_cast hpos) (centralCoeff_pos _)

theorem boundaryFactor_ne_zero (z : ℕ) : boundaryFactor z ≠ 0 :=
  ne_of_gt (boundaryFactor_pos z)

theorem boundaryFactor_step (z : ℕ) :
    ((z + 2 : ℕ) : ℚ) * boundaryFactor (z + 2) =
      ((z + 1 : ℕ) : ℚ) * boundaryFactor z := by
  by_cases hz : z % 2 = 0
  · have heq : z = 2 * (z / 2) := by omega
    generalize z / 2 = l at heq
    subst z
    rw [show 2 * l + 2 = 2 * (l + 1) by omega, boundaryFactor_even,
      boundaryFactor_even]
    convert centralCoeff_step l using 1
  · have heq : z = 2 * (z / 2) + 1 := by omega
    generalize z / 2 = l at heq
    subst z
    rw [show 2 * l + 1 + 2 = 2 * (l + 1) + 1 by omega,
      boundaryFactor_odd, boundaryFactor_odd]
    have hl : ((2 * l + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hl' : ((2 * (l + 1) + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hc := centralCoeff_step l
    have hc0 := centralCoeff_ne_zero l
    have hc1 := centralCoeff_ne_zero (l + 1)
    push_cast at hc ⊢
    field_simp
    nlinarith only [hc]

theorem boundaryFactor_ratio (z : ℕ) :
    boundaryFactor (z + 2) / boundaryFactor z =
      ((z + 1 : ℕ) : ℚ) / ((z + 2 : ℕ) : ℚ) := by
  have hfactor := boundaryFactor_ne_zero z
  have hden : ((z + 2 : ℕ) : ℚ) ≠ 0 := by positivity
  apply (div_eq_div_iff hfactor hden).2
  simpa [mul_comm] using boundaryFactor_step z

end InternalCatalan

end OAI
