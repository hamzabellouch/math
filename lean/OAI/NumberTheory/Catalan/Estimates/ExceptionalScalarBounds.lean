import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import OAI.NumberTheory.Catalan.Determinants.TwoAdicSmoothedMinor

namespace OAI


namespace InternalCatalan

open scoped BigOperators

private theorem two_adic_sum_lower {α : Type*} (s : Finset α) (f : α → ℚ)
    (B : ℤ) (hB : B ≤ 0) (hf : ∀ x ∈ s, B ≤ padicValRat 2 (f x)) :
    B ≤ padicValRat 2 (∑ x ∈ s, f x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    by_cases hz : f a + ∑ x ∈ s, f x = 0
    · simpa [hz] using hB
    · apply le_trans _ (padicValRat.min_le_padicValRat_add hz)
      apply le_min
      · exact hf a (Finset.mem_insert_self a s)
      · exact ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))

theorem harmonicRat_two_adic_lower (d n H : ℕ) (hn : n ≤ H) :
    -((d : ℤ) * (Nat.log 2 H : ℤ)) ≤ padicValRat 2 (harmonicRat d n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold harmonicRat
  apply two_adic_sum_lower
  · have : 0 ≤ (d : ℤ) * (Nat.log 2 H : ℤ) := by positivity
    omega
  · intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hval : padicValNat 2 (k + 1) ≤ Nat.log 2 H :=
      (padicValNat_le_nat_log (p := 2) (k + 1)).trans
        (Nat.log_mono_right (by omega : k + 1 ≤ H))
    have hval' : (padicValNat 2 (k + 1) : ℤ) ≤ (Nat.log 2 H : ℤ) := by
      exact_mod_cast hval
    simp only [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat]
    exact neg_le_neg (mul_le_mul_of_nonneg_left hval' (by positivity))

private theorem zetaRat_two_adic_lower_of_le (H i j : ℕ)
    (hi : i < H) (hji : j ≤ i) :
    -2 * (Nat.log 2 H : ℤ) ≤ padicValRat 2 (zetaRat i j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hj : j < H := lt_of_le_of_lt hji hi
  by_cases hij : i = j
  · subst j
    rw [zetaRat_diagonal, padicValRat.neg]
    simpa using harmonicRat_two_adic_lower 2 i H (Nat.le_of_lt hi)
  · have hden : ((i - j : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (show i - j ≠ 0 by omega)
    have heq : (i : ℚ) - (j : ℚ) = ((i - j : ℕ) : ℚ) :=
      (Nat.cast_sub hji).symm
    by_cases hnum : harmonicRat 1 i - harmonicRat 1 j = 0
    · rw [zetaRat_of_ne hij, hnum, zero_div, padicValRat.zero]
      have : 0 ≤ (Nat.log 2 H : ℤ) := by positivity
      omega
    · have hival : -(Nat.log 2 H : ℤ) ≤ padicValRat 2 (harmonicRat 1 i) := by
        simpa using harmonicRat_two_adic_lower 1 i H (Nat.le_of_lt hi)
      have hjval : -(Nat.log 2 H : ℤ) ≤ padicValRat 2 (harmonicRat 1 j) := by
        simpa using harmonicRat_two_adic_lower 1 j H (Nat.le_of_lt hj)
      have hsum := padicValRat.min_le_padicValRat_add (p := 2)
        (q := harmonicRat 1 i) (r := -harmonicRat 1 j)
        (by simpa only [sub_eq_add_neg] using hnum)
      rw [← sub_eq_add_neg, padicValRat.neg] at hsum
      have hnval : -(Nat.log 2 H : ℤ) ≤
          padicValRat 2 (harmonicRat 1 i - harmonicRat 1 j) :=
        (le_min hival hjval).trans hsum
      have hdval : padicValNat 2 (i - j) ≤ Nat.log 2 H :=
        (padicValNat_le_nat_log (p := 2) (i - j)).trans
          (Nat.log_mono_right (by omega : i - j ≤ H))
      rw [zetaRat_of_ne hij, heq, padicValRat.div hnum hden, padicValRat.of_nat]
      omega

theorem zetaRat_two_adic_lower (H i j : ℕ) (hi : i < H) (hj : j < H) :
    -2 * (Nat.log 2 H : ℤ) ≤ padicValRat 2 (zetaRat i j) := by
  rcases le_total j i with hji | hij
  · exact zetaRat_two_adic_lower_of_le H i j hi hji
  · rw [zetaRat_symm]
    exact zetaRat_two_adic_lower_of_le H j i hj hij

theorem zetaRat_two_adic_floor_lower (H i j : ℕ) (hi : i < H) (hj : j < H) :
    -2 * ⌊Real.logb 2 (H : ℝ)⌋ ≤ padicValRat 2 (zetaRat i j) := by
  have hfloor : ⌊Real.logb 2 (H : ℝ)⌋ = (Nat.log 2 H : ℤ) := by
    simpa only [Nat.cast_ofNat, Int.log_natCast] using
      (Real.floor_logb_natCast (b := 2) (r := (H : ℝ)) (Nat.cast_nonneg H))
  rw [hfloor]
  exact zetaRat_two_adic_lower H i j hi hj

end InternalCatalan



noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan

def exceptionScalar (q : ℚ) (N u j : ℕ) : ℚ_[2] :=
  (4 * (q : ℚ_[2]) - smoothingMoment 0 0) *
    ∑ v ∈ Finset.range (h N + 1),
      (((1 - X : ℤ[X]) ^ h N).coeff v : ℚ_[2]) *
        (centralCoeffKernel (((Cdegree N - 1 - u + v : ℕ) : ℤ) - j) : ℚ_[2])

def boundaryScalar (N u j : ℕ) : ℚ_[2] :=
  ∑ v ∈ Finset.range (h N + 1),
    (((1 - X : ℤ[X]) ^ h N).coeff v : ℚ_[2]) *
      ((-smoothingMoment 0 1) * (if Cdegree N - 1 - u + v = j then 1 else 0) -
        (3 / 2 : ℚ_[2]) * (zetaRat (Cdegree N - 1 - u + v) j : ℚ_[2]))

theorem exceptionalScalar_index_lt_H {N u v : ℕ}
    (hu : u < Cdegree N) (hv : v < h N + 1) :
    Cdegree N - 1 - u + v < H N := by
  unfold Cdegree h H at *
  omega

private theorem contract_rowFactor_reversed (N : ℕ) (F : ℤ[X]) (w : ℕ → ℚ_[2]) :
    (∑ i ∈ Finset.range (H N),
      ((((1 - X : ℤ[X]) ^ h N * reversedRow (Cdegree N) F).coeff i) : ℚ_[2]) *
        w i) =
      ∑ u ∈ Finset.range (Cdegree N), (F.coeff u : ℚ_[2]) *
        ∑ v ∈ Finset.range (h N + 1),
          (((1 - X : ℤ[X]) ^ h N).coeff v : ℚ_[2]) *
            w (Cdegree N - 1 - u + v) := by
  classical
  have hfactor : (1 - X : ℤ[X]) ^ h N =
      ∑ v ∈ Finset.range (h N + 1),
        Polynomial.C (((1 - X : ℤ[X]) ^ h N).coeff v) * X ^ v :=
    Polynomial.as_sum_range_C_mul_X_pow' _
      (lt_of_le_of_lt (rowFactor_natDegree_le N) (Nat.lt_succ_self _))
  have hpoly : (1 - X : ℤ[X]) ^ h N * reversedRow (Cdegree N) F =
      ∑ u ∈ Finset.range (Cdegree N), ∑ v ∈ Finset.range (h N + 1),
        Polynomial.C (F.coeff u * ((1 - X : ℤ[X]) ^ h N).coeff v) *
          X ^ (Cdegree N - 1 - u + v) := by
    unfold reversedRow
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    calc
      _ = (∑ v ∈ Finset.range (h N + 1),
          Polynomial.C (((1 - X : ℤ[X]) ^ h N).coeff v) * X ^ v) *
            (Polynomial.C (F.coeff u) * X ^ (Cdegree N - 1 - u)) :=
        congrArg (fun Q : ℤ[X] => Q *
          (Polynomial.C (F.coeff u) * X ^ (Cdegree N - 1 - u))) hfactor
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v hv
        rw [map_mul, pow_add]
        ring
  rw [hpoly]
  simp only [finsetSum_coeff, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hi := exceptionalScalar_index_lt_H
    (Finset.mem_range.mp hu) (Finset.mem_range.mp hv)
  simp [Finset.mem_range, hi, mul_assoc]

theorem exceptionColumn_eq_sum_exceptionScalar (q : ℚ) (N r j : ℕ) :
    exceptionColumn q N r j =
      ∑ u ∈ Finset.range (Cdegree N),
        ((Chebyshev.T ℤ (rowDistance N r : ℤ)).coeff u : ℚ_[2]) *
          exceptionScalar q N u j := by
  unfold exceptionColumn rowP
  rw [contract_rowFactor_reversed, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  unfold exceptionScalar
  ring

theorem boundaryColumn_eq_sum_boundaryScalar (N r j : ℕ) :
    boundaryColumn N r j =
      ∑ u ∈ Finset.range (Cdegree N),
        ((Int.sign (rowOffset N r) *
          (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).coeff u : ℤ) : ℚ_[2]) *
            boundaryScalar N u j := by
  unfold boundaryColumn rowD
  simp only [mul_assoc, coeff_C_mul, Int.cast_mul]
  rw [← Finset.mul_sum, contract_rowFactor_reversed, Finset.mul_sum]
  simp only [boundaryScalar]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem padic_two_norm_rat_le_zpow_of_valuation {x : ℚ} {b : ℤ}
    (hb : b ≤ padicValRat 2 x) : ‖(x : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-b) := by
  by_cases hx : x = 0
  · simp only [hx, Rat.cast_zero, norm_zero]
    positivity
  have hx₂ : (x : ℚ_[2]) ≠ 0 := by exact_mod_cast hx
  rw [Padic.norm_eq_zpow_neg_valuation hx₂, Padic.valuation_ratCast]
  exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (neg_le_neg hb)

theorem centralCoeff_norm_le (l : ℕ) :
    ‖(centralCoeff l : ℚ_[2])‖ ≤ (2 : ℝ) ^ (2 * (l : ℤ)) := by
  simpa only [neg_mul, neg_neg] using
    padic_two_norm_rat_le_zpow_of_valuation (centralCoeff_two_adic_lower l)

theorem centralCoeffKernel_norm_le (d : ℤ) :
    ‖(centralCoeffKernel d : ℚ_[2])‖ ≤ (2 : ℝ) ^ d := by
  by_cases hd : 0 ≤ d ∧ d % 2 = 0
  · have heq : 2 * ((d.toNat / 2 : ℕ) : ℤ) = d := by omega
    simpa only [centralCoeffKernel, ite_eq_left hd, heq] using
      centralCoeff_norm_le (d.toNat / 2)
  · simp only [centralCoeffKernel, ite_eq_right hd, Rat.cast_zero, norm_zero]
    positivity

theorem zetaRat_norm_le (H i j : ℕ) (hi : i < H) (hj : j < H) :
    ‖(zetaRat i j : ℚ_[2])‖ ≤ (2 : ℝ) ^ (2 * Nat.log 2 H) := by
  have hb := padic_two_norm_rat_le_zpow_of_valuation
    (zetaRat_two_adic_lower H i j hi hj)
  have heq : -(-2 * (Nat.log 2 H : ℤ)) = ((2 * Nat.log 2 H : ℕ) : ℤ) := by
    push_cast
    ring
  rw [heq, zpow_natCast] at hb
  exact hb

theorem exceptionScalar_norm_le (q : ℚ) {N u : ℕ} (j : ℕ)
    (hu : u < Cdegree N) :
    ‖exceptionScalar q N u j‖ ≤
      ‖4 * (q : ℚ_[2]) - smoothingMoment 0 0‖ *
        (2 : ℝ) ^ ((H N : ℤ) - 1 - u - j) := by
  unfold exceptionScalar
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro v hv
  have hv' := Finset.mem_range.mp hv
  have hCH := H_eq_Cdegree_add_h N
  have hindex : (((Cdegree N - 1 - u + v : ℕ) : ℤ) - j) ≤
      (H N : ℤ) - 1 - u - j := by omega
  have hk := (centralCoeffKernel_norm_le
    (((Cdegree N - 1 - u + v : ℕ) : ℤ) - j)).trans
      (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hindex)
  rw [norm_mul]
  calc
    _ ≤ 1 * (2 : ℝ) ^ ((H N : ℤ) - 1 - u - j) :=
      mul_le_mul (Padic.norm_int_le_one _) hk (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem boundaryScalar_norm_le {N u j : ℕ}
    (hu : u < Cdegree N) (hj : j < H N) :
    ‖boundaryScalar N u j‖ ≤
      max ‖-smoothingMoment 0 1‖ (2 * (2 : ℝ) ^ (2 * Nat.log 2 (H N))) := by
  have hthree : ‖(3 : ℚ_[2])‖ ≤ (1 : ℝ) := by
    simpa using Padic.norm_int_le_one (3 : ℤ)
  have htwo : ‖(2 : ℚ_[2])‖ = (1 / 2 : ℝ) := by
    simpa using Padic.norm_p (p := 2)
  have hratio : ‖(3 / 2 : ℚ_[2])‖ ≤ (2 : ℝ) := by
    rw [norm_div, htwo]
    calc
      _ ≤ 1 / (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_right hthree (by norm_num)
      _ = _ := by norm_num
  unfold boundaryScalar
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (le_trans (norm_nonneg _) (le_max_left _ _))
  intro v hv
  have hi := exceptionalScalar_index_lt_H hu (Finset.mem_range.mp hv)
  have hz := zetaRat_norm_le (H N) (Cdegree N - 1 - u + v) j hi hj
  have hdelta : ‖(-smoothingMoment 0 1) *
      (if Cdegree N - 1 - u + v = j then (1 : ℚ_[2]) else 0)‖ ≤
      ‖-smoothingMoment 0 1‖ := by
    split_ifs <;> simp
  have hzeta : ‖(3 / 2 : ℚ_[2]) *
      (zetaRat (Cdegree N - 1 - u + v) j : ℚ_[2])‖ ≤
      2 * (2 : ℝ) ^ (2 * Nat.log 2 (H N)) := by
    rw [norm_mul]
    exact mul_le_mul hratio hz (norm_nonneg _) (by norm_num)
  have hinner : ‖(-smoothingMoment 0 1) *
      (if Cdegree N - 1 - u + v = j then (1 : ℚ_[2]) else 0) -
      (3 / 2 : ℚ_[2]) * (zetaRat (Cdegree N - 1 - u + v) j : ℚ_[2])‖ ≤
      max ‖-smoothingMoment 0 1‖ (2 * (2 : ℝ) ^ (2 * Nat.log 2 (H N))) := by
    have hsum := Padic.nonarchimedean
      ((-smoothingMoment 0 1) *
        (if Cdegree N - 1 - u + v = j then (1 : ℚ_[2]) else 0))
      (-((3 / 2 : ℚ_[2]) * (zetaRat (Cdegree N - 1 - u + v) j : ℚ_[2])))
    rw [← sub_eq_add_neg, norm_neg] at hsum
    exact hsum.trans (max_le_max hdelta hzeta)
  rw [norm_mul]
  calc
    _ ≤ 1 * max ‖-smoothingMoment 0 1‖
        (2 * (2 : ℝ) ^ (2 * Nat.log 2 (H N))) :=
      mul_le_mul (Padic.norm_int_le_one _) hinner (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

end InternalCatalan

end

end OAI
