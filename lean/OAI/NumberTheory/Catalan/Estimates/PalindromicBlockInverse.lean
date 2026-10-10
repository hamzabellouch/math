import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeEvenStartingZero
import OAI.NumberTheory.Catalan.Estimates.PalindromicReversalMultiplicities

namespace OAI


noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan

def fixedB0 : Matrix (Fin 48) (Fin 48) ℚ :=
  fun r k => fixedBaseEntryRat r.castSucc k

def fixedB1 : Matrix (Fin 48) (Fin 48) ℚ :=
  fun r k => fixedBaseEntryRat r.succ k

def fixedMatrix (sigma : ℚ) : Matrix (Fin 48) (Fin 48) ℚ :=
  fixedB0 + sigma • fixedB1

theorem fixedMatrix_apply (sigma : ℚ) (r k : Fin 48) :
    fixedMatrix sigma r k =
      fixedBaseEntryRat r.castSucc k + sigma * fixedBaseEntryRat r.succ k := rfl

@[simp] theorem fixedMatrix_zero : fixedMatrix 0 = fixedB0 := by simp [fixedMatrix]
@[simp] theorem fixedMatrix_one : fixedMatrix 1 = fixedB0 + fixedB1 := by
  simp [fixedMatrix]
@[simp] theorem fixedMatrix_neg_one : fixedMatrix (-1) = fixedB0 - fixedB1 := by
  simp [fixedMatrix, sub_eq_add_neg]

theorem fixed_rowD_four : rowD 1 4 = 0 := by
  apply rowD_eq_zero_of_distance_zero
  norm_num [rowDistance, rowOffset, g]

theorem fixed_rowP_four : rowP 1 4 = (1 - X) ^ 2 * X ^ 62 := by
  have hr : reversedRow 63 (1 : ℤ[X]) = X ^ 62 := by
    ext i
    rw [reversedRow_coeff]
    simp only [Polynomial.coeff_one, Polynomial.coeff_X_pow]
    split_ifs <;> omega
  norm_num [rowP, rowDistance, rowOffset, g, h, Cdegree, hr]

theorem fixed_rawEntry_four (j : ℕ) :
    rawEntryRat 0 1 4 j = momentRat 62 j - 2 * momentRat 63 j + momentRat 64 j := by
  have hp : rowP 1 4 = X ^ 62 - 2 * X ^ 63 + X ^ 64 := by
    rw [fixed_rowP_four]
    ring
  rw [rawEntryRat_zero, hp, fixed_rowD_four]
  norm_num [H, Finset.sum_range_succ]
  ring

end InternalCatalan

end



noncomputable section
open scoped BigOperators
namespace InternalCatalan

def fixedFilteredMomentRat (i k : ℕ) : ℚ :=
  ∑ v ∈ Finset.range 5, filterCoeffRat 1 v * momentRat i (7 + k + v)

def fixedFilteredZetaRat (i k : ℕ) : ℚ :=
  ∑ v ∈ Finset.range 5, filterCoeffRat 1 v * zetaRat i (7 + k + v)

theorem fixedBaseEntry_dot_filtered (r : Fin 49) (k : Fin 48) :
    fixedBaseEntryRat r k =
      (∑ i ∈ Finset.range 65, ((rowP 1 r.val).coeff i : ℚ) *
        fixedFilteredMomentRat i k.val) -
      (3 / 2 : ℚ) * ∑ i ∈ Finset.range 65,
        ((rowD 1 r.val).coeff i : ℚ) * fixedFilteredZetaRat i k.val := by
  change (∑ v ∈ Finset.range 5,
    filterCoeffRat 1 v * rawEntryRat 0 1 r.val (7 + k.val + v)) = _
  simp_rw [rawEntryRat_zero]
  change (∑ v ∈ Finset.range 5, filterCoeffRat 1 v *
    ((∑ i ∈ Finset.range 65, ((rowP 1 r.val).coeff i : ℚ) *
      momentRat i (7 + k.val + v)) -
    (3 / 2 : ℚ) * ∑ i ∈ Finset.range 65, ((rowD 1 r.val).coeff i : ℚ) *
      zetaRat i (7 + k.val + v))) = _
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  unfold fixedFilteredMomentRat fixedFilteredZetaRat
  congr 1
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro v hv
    ring
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro v hv
    ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

theorem palindromicReversalMatrix_cube_mul (p : ℕ) :
    (palindromicReversalMatrix p * palindromicReversalMatrix p) *
      palindromicReversalMatrix p = palindromicReversalMatrix p := by
  ext k i
  by_cases hi : i.val = 0
  · rw [mul_palindromicReversalMatrix_column_zero _ k i hi,
      palindromicReversalMatrix_column_zero i hi k]
  · have hip : 0 < i.val := by omega
    rw [mul_palindromicReversalMatrix_column_pos _ k i hip,
      palindromicReversalMatrix_mul_self,
      ite_eq_right (show (palindromicReverseIndex i hip).val ≠ 0 by
        have h := palindromicReverseIndex_pos i hip
        omega)]
    exact (palindromicReversalMatrix_column_pos i hip k).symm

theorem palindromicReversalMatrix_cube (p : ℕ) :
    palindromicReversalMatrix p ^ 3 = palindromicReversalMatrix p := by
  simpa only [pow_succ, pow_zero, one_mul] using palindromicReversalMatrix_cube_mul p

def palindromicReversalProjZero (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p) (Fin p) (ZMod p) :=
  1 - palindromicReversalMatrix p * palindromicReversalMatrix p

def palindromicReversalProjPlus (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p) (Fin p) (ZMod p) :=
  (1 / 2 : ZMod p) •
    (palindromicReversalMatrix p * palindromicReversalMatrix p +
      palindromicReversalMatrix p)

def palindromicReversalProjMinus (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p) (Fin p) (ZMod p) :=
  (1 / 2 : ZMod p) •
    (palindromicReversalMatrix p * palindromicReversalMatrix p -
      palindromicReversalMatrix p)

theorem palindromicReversalProjections_sum {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    palindromicReversalProjZero p + palindromicReversalProjPlus p +
      palindromicReversalProjMinus p = 1 := by
  ext k i
  simp only [palindromicReversalProjZero, palindromicReversalProjPlus,
    palindromicReversalProjMinus, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  field_simp [palindromic_two_ne_zero hp2]
  ring

theorem palindromicReversalMatrix_mul_projZero {p : ℕ} [Fact p.Prime] :
    palindromicReversalMatrix p * palindromicReversalProjZero p = 0 := by
  rw [palindromicReversalProjZero, mul_sub, mul_one, ← mul_assoc,
    palindromicReversalMatrix_cube_mul, sub_self]

theorem palindromicReversalMatrix_mul_projPlus {p : ℕ} [Fact p.Prime] :
    palindromicReversalMatrix p * palindromicReversalProjPlus p =
      palindromicReversalProjPlus p := by
  simp only [palindromicReversalProjPlus, Matrix.mul_smul, mul_add]
  rw [← mul_assoc, palindromicReversalMatrix_cube_mul]
  congr 1
  exact add_comm _ _

theorem palindromicReversalMatrix_mul_projMinus {p : ℕ} [Fact p.Prime] :
    palindromicReversalMatrix p * palindromicReversalProjMinus p =
      -palindromicReversalProjMinus p := by
  simp only [palindromicReversalProjMinus, Matrix.mul_smul, mul_sub]
  rw [← mul_assoc, palindromicReversalMatrix_cube_mul, ← smul_neg, neg_sub]

theorem palindromicReversalProjZero_mul_matrix {p : ℕ} [Fact p.Prime] :
    palindromicReversalProjZero p * palindromicReversalMatrix p = 0 := by
  rw [palindromicReversalProjZero, sub_mul, one_mul,
    palindromicReversalMatrix_cube_mul, sub_self]

theorem palindromicReversalProjPlus_mul_matrix {p : ℕ} [Fact p.Prime] :
    palindromicReversalProjPlus p * palindromicReversalMatrix p =
      palindromicReversalProjPlus p := by
  simp only [palindromicReversalProjPlus, Matrix.smul_mul, add_mul]
  rw [palindromicReversalMatrix_cube_mul]
  congr 1
  exact add_comm _ _

theorem palindromicReversalProjMinus_mul_matrix {p : ℕ} [Fact p.Prime] :
    palindromicReversalProjMinus p * palindromicReversalMatrix p =
      -palindromicReversalProjMinus p := by
  simp only [palindromicReversalProjMinus, Matrix.smul_mul, sub_mul]
  rw [palindromicReversalMatrix_cube_mul, ← smul_neg, neg_sub]







open scoped BigOperators

def palindromicRatResidue (p : ℕ) [Fact p.Prime] (x : ℚ) : ZMod p :=
  (x.num : ZMod p) / (x.den : ZMod p)

def fixedB0Residue (p : ℕ) [Fact p.Prime] : Matrix (Fin 48) (Fin 48) (ZMod p) :=
  fun r k => palindromicRatResidue p (fixedB0 r k)

def fixedB1Residue (p : ℕ) [Fact p.Prime] : Matrix (Fin 48) (Fin 48) (ZMod p) :=
  fun r k => palindromicRatResidue p (fixedB1 r k)

theorem fixedB0Residue_apply (p : ℕ) [Fact p.Prime] (r k : Fin 48) :
    fixedB0Residue p r k = palindromicRatResidue p (fixedBaseEntryRat r.castSucc k) :=
  rfl

theorem fixedB1Residue_apply (p : ℕ) [Fact p.Prime] (r k : Fin 48) :
    fixedB1Residue p r k = palindromicRatResidue p (fixedBaseEntryRat r.succ k) :=
  rfl

@[simp] theorem palindromicRatResidue_intCast (p : ℕ) [Fact p.Prime] (z : ℤ) :
    palindromicRatResidue p (z : ℚ) = (z : ZMod p) := by
  simp [palindromicRatResidue]

theorem palindromicRatResidue_mul {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : (a.den : ZMod p) ≠ 0) (hb : (b.den : ZMod p) ≠ 0) :
    palindromicRatResidue p (a * b) =
      palindromicRatResidue p a * palindromicRatResidue p b :=
  (rational_residue_mul ha hb).2

theorem palindromicRatResidue_add {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : (a.den : ZMod p) ≠ 0) (hb : (b.den : ZMod p) ≠ 0) :
    palindromicRatResidue p (a + b) =
      palindromicRatResidue p a + palindromicRatResidue p b :=
  (rational_residue_add ha hb).2

theorem palindromicRatResidue_sub {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : (a.den : ZMod p) ≠ 0) (hb : (b.den : ZMod p) ≠ 0) :
    palindromicRatResidue p (a - b) =
      palindromicRatResidue p a - palindromicRatResidue p b :=
  (rational_residue_sub ha hb).2

theorem palindromicRatResidue_sum {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, ((f i).den : ZMod p) ≠ 0) :
    palindromicRatResidue p (∑ i ∈ s, f i) =
      ∑ i ∈ s, palindromicRatResidue p (f i) :=
  (rational_residue_sum s f hf).2

private theorem fixed_nat_inverse_pow_den {p n : ℕ} [Fact p.Prime]
    (hn0 : 0 < n) (hn : n < p) (d : ℕ) :
    ((1 / (n : ℚ) ^ d).den : ZMod p) ≠ 0 := by
  have hv : padicValRat p ((n : ℚ) ^ d) = 0 := by
    rw [padicValRat.pow, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hn0 hn)]
    simp
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn0)
  simpa only [one_div] using (rational_residue_inv (pow_ne_zero d hnq) hv).1

theorem harmonicRat_small_den_ne_zero {p n : ℕ} [Fact p.Prime]
    (hn : n < p) (d : ℕ) : ((harmonicRat d n).den : ZMod p) ≠ 0 := by
  apply (rational_residue_sum (Finset.range n)
    (fun k => 1 / (((k + 1 : ℕ) : ℚ) ^ d)) ?_).1
  intro k hk
  exact fixed_nat_inverse_pow_den (by omega) (by
    have := Finset.mem_range.mp hk
    omega) d

theorem zetaRat_small_den_ne_zero {p i j : ℕ} [Fact p.Prime]
    (hi : i < p) (hj : j < p) : ((zetaRat i j).den : ZMod p) ≠ 0 := by
  have hle : ∀ a b : ℕ, a < p → b < p → b ≤ a →
      ((zetaRat a b).den : ZMod p) ≠ 0 := by
    intro a b ha hb hba
    by_cases hab : a = b
    · subst b
      simpa only [zetaRat_diagonal, Rat.neg_den] using
        harmonicRat_small_den_ne_zero ha 2
    · rw [zetaRat_of_ne hab, ← Nat.cast_sub hba, div_eq_mul_inv]
      have hinv : (((((a - b : ℕ) : ℚ)⁻¹).den : ℕ) : ZMod p) ≠ 0 := by
        simpa only [pow_one, one_div] using
          (fixed_nat_inverse_pow_den (p := p) (n := a - b) (by omega) (by omega) 1)
      exact (rational_residue_mul
        (rational_residue_sub (harmonicRat_small_den_ne_zero ha 1)
          (harmonicRat_small_den_ne_zero hb 1)).1 hinv).1
  rcases le_total j i with hji | hij
  · exact hle i j hi hj hji
  · rw [zetaRat_symm]
    exact hle j i hj hi hij

private theorem fixed_three_halves_den {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) : (((3 / 2 : ℚ).den : ℕ) : ZMod p) ≠ 0 := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega : 0 < 2) (by omega : 2 < p)) hdiv
  simpa only [show (3 / 2 : ℚ).den = 2 by norm_num, Nat.cast_ofNat] using htwo

theorem fixed_rawEntryRat_den_ne_zero {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r j : ℕ) (hj : j < p) :
    ((rawEntryRat 0 1 r j).den : ZMod p) ≠ 0 := by
  have hM : ∀ i ∈ Finset.range (H 1),
      (((((rowP 1 r).coeff i : ℚ) * momentRat i j)).den : ZMod p) ≠ 0 := by
    intro i hi
    apply (rational_residue_mul (by simp) ?_).1
    exact momentRat_odd_prime_small_den_ne_zero (by omega)
      (by have := Finset.mem_range.mp hi; simp only [H] at this; omega) hj
  have hZ : ∀ i ∈ Finset.range (H 1),
      (((((rowD 1 r).coeff i : ℚ) * zetaRat i j)).den : ZMod p) ≠ 0 := by
    intro i hi
    apply (rational_residue_mul (by simp) ?_).1
    exact zetaRat_small_den_ne_zero
      (by have := Finset.mem_range.mp hi; simp only [H] at this; omega) hj
  rw [rawEntryRat_zero]
  exact (rational_residue_sub
    (rational_residue_sum _ _ hM).1
    (rational_residue_mul (fixed_three_halves_den hp)
      (rational_residue_sum _ _ hZ).1).1).1

theorem filterCoeffRat_den_ne_zero {p : ℕ} [Fact p.Prime] (N v : ℕ) :
    ((filterCoeffRat N v).den : ZMod p) ≠ 0 := by
  have hcast : (((-1 : ℤ) ^ v * ((q N).choose v : ℤ) : ℤ) : ℚ) =
      filterCoeffRat N v := by simp [filterCoeffRat]
  rw [← hcast, Rat.den_intCast, Nat.cast_one]
  exact one_ne_zero

theorem palindromicRatResidue_int_sum {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (a : ι → ℤ) (f : ι → ℚ)
    (hf : ∀ i ∈ s, ((f i).den : ZMod p) ≠ 0) :
    ((∑ i ∈ s, (a i : ℚ) * f i).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (∑ i ∈ s, (a i : ℚ) * f i) =
        ∑ i ∈ s, (a i : ZMod p) * palindromicRatResidue p (f i) := by
  have hterm : ∀ i ∈ s, (((a i : ℚ) * f i).den : ZMod p) ≠ 0 :=
    fun i hi => (rational_residue_mul (by simp) (hf i hi)).1
  refine ⟨(rational_residue_sum s _ hterm).1, ?_⟩
  rw [palindromicRatResidue_sum s _ hterm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [palindromicRatResidue_mul (by simp) (hf i hi), palindromicRatResidue_intCast]

theorem fixed_rawEntryRat_residue {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r j : ℕ) (hj : j < p) :
    palindromicRatResidue p (rawEntryRat 0 1 r j) =
      (∑ i ∈ Finset.range (H 1), ((rowP 1 r).coeff i : ZMod p) *
        palindromicRatResidue p (momentRat i j)) -
      (3 / 2 : ZMod p) *
        ∑ i ∈ Finset.range (H 1), ((rowD 1 r).coeff i : ZMod p) *
          palindromicRatResidue p (zetaRat i j) := by
  have hM := palindromicRatResidue_int_sum (p := p) (Finset.range (H 1))
    (fun i => (rowP 1 r).coeff i) (fun i => momentRat i j) (by
      intro i hi
      exact momentRat_odd_prime_small_den_ne_zero (by omega)
        (by have := Finset.mem_range.mp hi; simp only [H] at this; omega) hj)
  have hZ := palindromicRatResidue_int_sum (p := p) (Finset.range (H 1))
    (fun i => (rowD 1 r).coeff i) (fun i => zetaRat i j) (by
      intro i hi
      exact zetaRat_small_den_ne_zero
        (by have := Finset.mem_range.mp hi; simp only [H] at this; omega) hj)
  rw [rawEntryRat_zero,
    palindromicRatResidue_sub hM.1
      (rational_residue_mul (fixed_three_halves_den hp) hZ.1).1,
    palindromicRatResidue_mul (fixed_three_halves_den hp) hZ.1, hM.2, hZ.2]
  have hthree : palindromicRatResidue p (3 / 2 : ℚ) = (3 / 2 : ZMod p) := by
    norm_num [palindromicRatResidue]
  rw [hthree]

theorem filterCoeffRat_residue (p N v : ℕ) [Fact p.Prime] :
    palindromicRatResidue p (filterCoeffRat N v) =
      (-1 : ZMod p) ^ v * ((q N).choose v : ZMod p) := by
  simpa [filterCoeffRat] using
    palindromicRatResidue_intCast p ((-1 : ℤ) ^ v * ((q N).choose v : ℤ))

theorem fixedBaseEntryRat_den_ne_zero {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r : Fin 49) (k : Fin 48) :
    ((fixedBaseEntryRat r k).den : ZMod p) ≠ 0 := by
  unfold fixedBaseEntryRat filteredEntryRat
  apply (rational_residue_sum _ _ ?_).1
  intro v hv
  apply (rational_residue_mul (filterCoeffRat_den_ne_zero 1 v) ?_).1
  apply fixed_rawEntryRat_den_ne_zero hp
  have hk := k.isLt
  have hv' := Finset.mem_range.mp hv
  simp only [q, b] at hv' ⊢
  omega

theorem fixedB0_den_ne_zero {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r k : Fin 48) : ((fixedB0 r k).den : ZMod p) ≠ 0 :=
  fixedBaseEntryRat_den_ne_zero hp r.castSucc k

theorem fixedB1_den_ne_zero {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r k : Fin 48) : ((fixedB1 r k).den : ZMod p) ≠ 0 :=
  fixedBaseEntryRat_den_ne_zero hp r.succ k

theorem fixedBaseEntryRat_residue {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r : Fin 49) (k : Fin 48) :
    palindromicRatResidue p (fixedBaseEntryRat r k) =
      ∑ v ∈ Finset.range (q 1 + 1),
        ((-1 : ZMod p) ^ v * ((q 1).choose v : ZMod p)) *
          palindromicRatResidue p (rawEntryRat 0 1 r.val (b 1 + k.val + v)) := by
  have hraw : ∀ v ∈ Finset.range (q 1 + 1),
      ((rawEntryRat 0 1 r.val (b 1 + k.val + v)).den : ZMod p) ≠ 0 := by
    intro v hv
    apply fixed_rawEntryRat_den_ne_zero hp
    have hk := k.isLt
    have hv' := Finset.mem_range.mp hv
    simp only [q, b] at hv' ⊢
    omega
  unfold fixedBaseEntryRat filteredEntryRat
  rw [palindromicRatResidue_sum _ _ (fun v hv =>
    (rational_residue_mul (filterCoeffRat_den_ne_zero 1 v) (hraw v hv)).1)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [palindromicRatResidue_mul (filterCoeffRat_den_ne_zero 1 v) (hraw v hv),
    filterCoeffRat_residue]

theorem fixedMatrix_one_residue {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r k : Fin 48) :
    palindromicRatResidue p (fixedMatrix 1 r k) =
      fixedB0Residue p r k + fixedB1Residue p r k := by
  rw [fixedMatrix_one]
  exact palindromicRatResidue_add (fixedB0_den_ne_zero hp r k)
    (fixedB1_den_ne_zero hp r k)

theorem fixedMatrix_neg_one_residue {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r k : Fin 48) :
    palindromicRatResidue p (fixedMatrix (-1) r k) =
      fixedB0Residue p r k - fixedB1Residue p r k := by
  rw [fixedMatrix_neg_one]
  exact palindromicRatResidue_sub (fixedB0_den_ne_zero hp r k)
    (fixedB1_den_ne_zero hp r k)

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Matrix
open scoped Kronecker

def palindromicScaledResidueMatrix (z : ℚ) (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p × Fin 48) (Fin p × Fin 48) (ZMod p) :=
  fun r k => palindromicRatResidue p
    ((p : ℚ) ^ 2 * filteredEntryRat z p
      (p * r.2.val + r.1.val) (k.1.val + p * k.2.val))

def palindromicResidueBlockMatrix (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p × Fin 48) (Fin p × Fin 48) (ZMod p) :=
  fun r k => palindromicTransitionMatrix p k.1 r.1 * fixedB0Residue p r.2 k.2 +
    palindromicReversedTransitionMatrix p k.1 r.1 * fixedB1Residue p r.2 k.2

theorem palindromicResidueBlockMatrix_kronecker (p : ℕ) [Fact p.Prime] :
    palindromicResidueBlockMatrix p =
      (palindromicTransitionMatrix p)ᵀ ⊗ₖ fixedB0Residue p +
        (palindromicReversedTransitionMatrix p)ᵀ ⊗ₖ fixedB1Residue p := by
  ext r k
  rfl

def palindromicResidueColumnChange (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p × Fin 48) (Fin p × Fin 48) (ZMod p) :=
  ((palindromicTransitionMatrix p)ᵀ)⁻¹ ⊗ₖ
    (1 : Matrix (Fin 48) (Fin 48) (ZMod p))

def palindromicReducedBlockMatrix (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p × Fin 48) (Fin p × Fin 48) (ZMod p) :=
  (1 : Matrix (Fin p) (Fin p) (ZMod p)) ⊗ₖ fixedB0Residue p +
    (palindromicReversalMatrix p)ᵀ ⊗ₖ fixedB1Residue p

theorem palindromicReversedTransitionMatrix_transpose (p : ℕ) :
    (palindromicReversedTransitionMatrix p)ᵀ =
      (palindromicReversalMatrix p)ᵀ * (palindromicTransitionMatrix p)ᵀ := by
  rw [palindromicReversedTransitionMatrix, Matrix.transpose_mul]

theorem palindromicResidueBlockMatrix_factor (p : ℕ) [Fact p.Prime] :
    palindromicResidueBlockMatrix p = palindromicReducedBlockMatrix p *
      ((palindromicTransitionMatrix p)ᵀ ⊗ₖ
        (1 : Matrix (Fin 48) (Fin 48) (ZMod p))) := by
  rw [palindromicResidueBlockMatrix_kronecker, palindromicReducedBlockMatrix,
    Matrix.add_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
    ← palindromicReversedTransitionMatrix_transpose]

theorem palindromicResidueBlockMatrix_mul_columnChange {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    palindromicResidueBlockMatrix p * palindromicResidueColumnChange p =
      palindromicReducedBlockMatrix p := by
  have hu : IsUnit ((palindromicTransitionMatrix p)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (det_palindromicTransitionMatrix_ne_zero hp2)
  rw [palindromicResidueBlockMatrix_factor, palindromicResidueColumnChange,
    Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mul, Matrix.one_kronecker_one, Matrix.mul_one]

theorem det_palindromicResidueColumnChange {p : ℕ} [Fact p.Prime] :
    (palindromicResidueColumnChange p).det =
      ((palindromicTransitionMatrix p).det⁻¹) ^ 48 := by
  rw [palindromicResidueColumnChange, Matrix.det_kronecker,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Matrix.det_transpose,
    Matrix.det_one, one_pow, mul_one]
  rfl

theorem det_palindromicResidueColumnChange_ne_zero {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : (palindromicResidueColumnChange p).det ≠ 0 := by
  rw [det_palindromicResidueColumnChange]
  exact pow_ne_zero _ (inv_ne_zero (det_palindromicTransitionMatrix_ne_zero hp2))

theorem det_palindromicResidueBlockMatrix {p : ℕ} [Fact p.Prime] :
    (palindromicResidueBlockMatrix p).det =
      (palindromicTransitionMatrix p).det ^ 48 *
        (palindromicReducedBlockMatrix p).det := by
  rw [palindromicResidueBlockMatrix_factor, Matrix.det_mul, Matrix.det_kronecker,
    Matrix.det_transpose, Matrix.det_one, one_pow, mul_one]
  simpa using mul_comm (palindromicReducedBlockMatrix p).det
    ((palindromicTransitionMatrix p).det ^ 48)

theorem det_palindromicResidueBlockMatrix_ne_zero_iff {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (palindromicResidueBlockMatrix p).det ≠ 0 ↔
      (palindromicReducedBlockMatrix p).det ≠ 0 := by
  rw [det_palindromicResidueBlockMatrix]
  exact mul_ne_zero_iff.trans
    (and_iff_right (pow_ne_zero 48 (det_palindromicTransitionMatrix_ne_zero hp2)))

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Matrix
open scoped Kronecker

def palindromicReducedBlockRightInverse (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p × Fin 48) (Fin p × Fin 48) (ZMod p) :=
  (palindromicReversalProjZero p)ᵀ ⊗ₖ (fixedB0Residue p)⁻¹ +
    (palindromicReversalProjPlus p)ᵀ ⊗ₖ (fixedB0Residue p + fixedB1Residue p)⁻¹ +
      (palindromicReversalProjMinus p)ᵀ ⊗ₖ (fixedB0Residue p - fixedB1Residue p)⁻¹

theorem palindromicReducedBlock_mul_projZero {p : ℕ} [Fact p.Prime]
    (h0 : (fixedB0Residue p).det ≠ 0) :
    palindromicReducedBlockMatrix p *
        ((palindromicReversalProjZero p)ᵀ ⊗ₖ (fixedB0Residue p)⁻¹) =
      (palindromicReversalProjZero p)ᵀ ⊗ₖ
        (1 : Matrix (Fin 48) (Fin 48) (ZMod p)) := by
  have hp0 : (palindromicReversalMatrix p)ᵀ * (palindromicReversalProjZero p)ᵀ = 0 := by
    rw [← Matrix.transpose_mul, palindromicReversalProjZero_mul_matrix, Matrix.transpose_zero]
  rw [palindromicReducedBlockMatrix, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, hp0, Matrix.zero_kronecker, add_zero,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h0)]

theorem palindromicReducedBlock_mul_projPlus {p : ℕ} [Fact p.Prime]
    (hplus : (fixedB0Residue p + fixedB1Residue p).det ≠ 0) :
    palindromicReducedBlockMatrix p *
        ((palindromicReversalProjPlus p)ᵀ ⊗ₖ
          (fixedB0Residue p + fixedB1Residue p)⁻¹) =
      (palindromicReversalProjPlus p)ᵀ ⊗ₖ
        (1 : Matrix (Fin 48) (Fin 48) (ZMod p)) := by
  have hpp : (palindromicReversalMatrix p)ᵀ * (palindromicReversalProjPlus p)ᵀ =
      (palindromicReversalProjPlus p)ᵀ := by
    rw [← Matrix.transpose_mul, palindromicReversalProjPlus_mul_matrix]
  rw [palindromicReducedBlockMatrix, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, hpp, ← Matrix.kronecker_add, ← Matrix.add_mul,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hplus)]

theorem palindromicReducedBlock_mul_projMinus {p : ℕ} [Fact p.Prime]
    (hminus : (fixedB0Residue p - fixedB1Residue p).det ≠ 0) :
    palindromicReducedBlockMatrix p *
        ((palindromicReversalProjMinus p)ᵀ ⊗ₖ
          (fixedB0Residue p - fixedB1Residue p)⁻¹) =
      (palindromicReversalProjMinus p)ᵀ ⊗ₖ
        (1 : Matrix (Fin 48) (Fin 48) (ZMod p)) := by
  have hpm : (palindromicReversalMatrix p)ᵀ * (palindromicReversalProjMinus p)ᵀ =
      -(palindromicReversalProjMinus p)ᵀ := by
    rw [← Matrix.transpose_mul, palindromicReversalProjMinus_mul_matrix, Matrix.transpose_neg]
  rw [palindromicReducedBlockMatrix, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, hpm]
  have hcombine (C : Matrix (Fin 48) (Fin 48) (ZMod p)) :
      (palindromicReversalProjMinus p)ᵀ ⊗ₖ (fixedB0Residue p * C) +
        (-(palindromicReversalProjMinus p)ᵀ) ⊗ₖ (fixedB1Residue p * C) =
      (palindromicReversalProjMinus p)ᵀ ⊗ₖ ((fixedB0Residue p - fixedB1Residue p) * C) := by
    rw [Matrix.sub_mul]
    ext ⟨i, r⟩ ⟨j, k⟩
    simp only [Matrix.add_apply, Matrix.kronecker_apply, Matrix.neg_apply, Matrix.sub_apply]
    ring
  rw [hcombine, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hminus)]

theorem palindromicReducedBlock_mul_rightInverse {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (h0 : (fixedB0Residue p).det ≠ 0)
    (hplus : (fixedB0Residue p + fixedB1Residue p).det ≠ 0)
    (hminus : (fixedB0Residue p - fixedB1Residue p).det ≠ 0) :
    palindromicReducedBlockMatrix p * palindromicReducedBlockRightInverse p = 1 := by
  rw [palindromicReducedBlockRightInverse, Matrix.mul_add, Matrix.mul_add,
    palindromicReducedBlock_mul_projZero h0, palindromicReducedBlock_mul_projPlus hplus,
    palindromicReducedBlock_mul_projMinus hminus,
    ← Matrix.add_kronecker, ← Matrix.add_kronecker,
    ← Matrix.transpose_add, ← Matrix.transpose_add,
    palindromicReversalProjections_sum hp2, Matrix.transpose_one,
    Matrix.one_kronecker_one]

theorem det_palindromicReducedBlockMatrix_ne_zero_of_fixed {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (h0 : (fixedB0Residue p).det ≠ 0)
    (hplus : (fixedB0Residue p + fixedB1Residue p).det ≠ 0)
    (hminus : (fixedB0Residue p - fixedB1Residue p).det ≠ 0) :
    (palindromicReducedBlockMatrix p).det ≠ 0 := by
  have hd := congrArg Matrix.det (palindromicReducedBlock_mul_rightInverse hp2 h0 hplus hminus)
  rw [Matrix.det_mul, Matrix.det_one] at hd
  exact left_ne_zero_of_mul_eq_one hd

theorem det_palindromicResidueBlockMatrix_ne_zero_of_fixed {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (h0 : (fixedB0Residue p).det ≠ 0)
    (hplus : (fixedB0Residue p + fixedB1Residue p).det ≠ 0)
    (hminus : (fixedB0Residue p - fixedB1Residue p).det ≠ 0) :
    (palindromicResidueBlockMatrix p).det ≠ 0 :=
  (det_palindromicResidueBlockMatrix_ne_zero_iff hp2).mpr
    (det_palindromicReducedBlockMatrix_ne_zero_of_fixed hp2 h0 hplus hminus)

end InternalCatalan

end

end OAI
