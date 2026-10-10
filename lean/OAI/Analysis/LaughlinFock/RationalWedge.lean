import Mathlib
import OAI.Analysis.LaughlinFock.RationalFour

namespace OAI

/-! Rational Wedge. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
def rationalWordVacuum {Q : ℕ} : List (Orbital Q) → Occupation Q → ℚ
  | [], A => if A=∅ then 1 else 0
  | x::xs, A => if x∈A then
      rationalWordVacuum xs (A.erase x) * (-1)^((A.filter (· < x)).card) else 0

theorem annihilatorList_vacuum_rational {Q : ℕ} (xs : List (Orbital Q))
    (A : Occupation Q) :
    annihilatorList Q xs ∅ A = (rationalWordVacuum xs A : ℂ) := by
  induction xs generalizing A with
  | nil => by_cases h : A=∅ <;> simp [rationalWordVacuum, h, eq_comm]
  | cons x xs ih =>
    rw [annihilatorList_cons, mul_annihilator_apply]
    simp only [rationalWordVacuum]
    split_ifs <;> simp [ih, fermionSign]

theorem rationalWordVacuum_support {Q : ℕ} (xs : List (Orbital Q))
    (A : Occupation Q) (hn : rationalWordVacuum xs A ≠ 0) :
    xs.Nodup ∧ xs.toFinset=A := by
  induction xs generalizing A with
  | nil => simpa [rationalWordVacuum, eq_comm] using hn
  | cons x xs ih =>
    simp only [rationalWordVacuum] at hn
    split_ifs at hn with hx
    · obtain ⟨hxs,hA⟩ := ih (A.erase x) (fun h => hn (by rw [h, zero_mul]))
      refine ⟨List.nodup_cons.mpr ⟨?_,hxs⟩, ?_⟩
      · intro h
        have : x ∈ A.erase x := by rw [← hA]; simpa using h
        exact Finset.notMem_erase x A this
      · rw [List.toFinset_cons, hA, Finset.insert_erase hx]
    · simp at hn

def occupationFactorial {Q : ℕ} (A : Occupation Q) : ℚ :=
  ∏ a ∈ A, (a.val.factorial : ℚ)

def factorialMode (Q : ℕ) (a : Orbital Q) : ℂ :=
  (Real.sqrt (a.val.factorial : ℝ) : ℂ)

theorem factorialMode_ne_zero (Q : ℕ) (a : Orbital Q) : factorialMode Q a ≠ 0 := by
  unfold factorialMode
  exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0:ℝ)<a.val.factorial)).ne'

def rationalHighestTerm (D : ℕ) (r : CopyLabel D) (p j k x y : ℕ) : ℚ :=
  if x+y=p+1 then
    rationalCopyPolynomial D D r.val.val p j k * ((x:ℚ)-(y:ℚ)) *
      p.factorial * j.factorial * k.factorial
  else 0

theorem copy_pair_factorial (D : ℕ) (r : CopyLabel D) (p j k x y : ℕ)
    (hpk : p+j+k=D) :
    planarCopyCoefficient D D r.val.val p j k * limitPairCoefficient p x y *
      Real.sqrt (x.factorial:ℝ) * Real.sqrt (y.factorial:ℝ) *
      Real.sqrt (j.factorial:ℝ) * Real.sqrt (k.factorial:ℝ) =
    (Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) * Real.sqrt 2 / 2^D) *
      (rationalHighestTerm D r p j k x y : ℝ) := by
  unfold rationalHighestTerm limitPairCoefficient
  split_ifs with hxy
  · rw [planarCopyCoefficient_rational r p j k le_rfl hpk]
    have hsq : Real.sqrt (rationalCopyWeight D D p j k : ℝ) *
        Real.sqrt ((p.factorial:ℝ)/(2^p*x.factorial*y.factorial)) *
        Real.sqrt (x.factorial:ℝ) * Real.sqrt (y.factorial:ℝ) *
        Real.sqrt (j.factorial:ℝ) * Real.sqrt (k.factorial:ℝ) =
          Real.sqrt 2 * (p.factorial:ℝ)*j.factorial*k.factorial / 2^D := by
      have hn : 0 ≤ (rationalCopyWeight D D p j k : ℝ) := by
        exact_mod_cast (rationalCopyWeight_pos _ _ _ _ _).le
      apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
      simp only [mul_pow, div_pow]
      rw [Real.sq_sqrt hn, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
        Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
        Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
      have hpow : (2:ℝ)^(j+k+D)*2^p = (2^D)^2 := by
        rw [← pow_add, ← pow_mul]
        congr 1
        omega
      dsimp only [rationalCopyWeight]
      push_cast
      simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
      field_simp
      nlinarith only [hpow]
    push_cast
    linear_combination (rationalCopyPolynomial D D r.val.val p j k : ℝ)*
      ((x:ℝ)-(y:ℝ))*Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ)*hsq
  · simp

 

def rationalHighestEntry (D : ℕ) (r : CopyLabel D) (A : Occupation 24) : ℚ :=
  ∑ b : FourHighestShell 24 D, ∑ xy : IncreasingPair 24,
    rationalHighestTerm D r b.val.1.val b.val.2.val.1.val b.val.2.val.2.val
      xy.val.1.val xy.val.2.val *
    rationalWordVacuum [xy.val.1, xy.val.2, b.val.2.val.1, b.val.2.val.2] A

theorem factorial_conjugate_highest (D : ℕ) (r : CopyLabel D) :
    diagonalConjugate 24 (factorialMode 24) (planarHighestFourAnnihilator D r) =
      (Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) * Real.sqrt 2 / 2^D : ℂ) •
      (∑ b : FourHighestShell 24 D, ∑ xy : IncreasingPair 24,
        (rationalHighestTerm D r b.val.1.val b.val.2.val.1.val b.val.2.val.2.val
          xy.val.1.val xy.val.2.val : ℂ) •
        annihilatorList 24 [xy.val.1, xy.val.2, b.val.2.val.1, b.val.2.val.2]) := by
  classical
  unfold planarHighestFourAnnihilator
  rw [diagonalConjugate_sum]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [diagonalConjugate_smul,
    diagonalConjugate_mul _ _ (factorialMode_ne_zero 24),
    diagonalConjugate_mul _ _ (factorialMode_ne_zero 24),
    diagonalConjugate_annihilator _ _ (factorialMode_ne_zero 24),
    diagonalConjugate_annihilator _ _ (factorialMode_ne_zero 24),
    limitPairAnnihilator, diagonalConjugate_pair _ _ (factorialMode_ne_zero 24),
    coefficientPair_basis_expansion, Matrix.mul_sum]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro xy _
  have hbasis : basisAnnihilator 24 (increasingPairSector 24 xy).val =
      annihilator 24 xy.val.2 * annihilator 24 xy.val.1 :=
    basisAnnihilator_pair _ _ xy.property
  rw [hbasis]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hc := congrArg (fun x:ℝ => (x:ℂ))
    (copy_pair_factorial D r b.val.1.val b.val.2.val.1.val b.val.2.val.2.val
      xy.val.1.val xy.val.2.val b.property)
  push_cast at hc
  dsimp only [factorialMode, planarLocalCopyMatrix]
  rw [show (annihilator 24 b.val.2.val.2 * annihilator 24 b.val.2.val.1) *
      (annihilator 24 xy.val.2 * annihilator 24 xy.val.1) =
      annihilatorList 24 [xy.val.1, xy.val.2, b.val.2.val.1, b.val.2.val.2] by
    simp only [annihilatorList_cons, annihilatorList_nil, Matrix.one_mul, Matrix.mul_assoc]]
  congr 1
  convert hc using 1
  ring

end LaughlinFock
end

noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem occupationFactorial_pos {Q : ℕ} (A : Occupation Q) :
    0 < occupationFactorial A := by
  unfold occupationFactorial
  exact Finset.prod_pos (fun a _ => by positivity)

theorem factorialMode_prod {Q : ℕ} (A : Occupation Q) :
    (∏ a ∈ A, factorialMode Q a) = (Real.sqrt (occupationFactorial A : ℝ) : ℂ) := by
  unfold factorialMode occupationFactorial
  rw [Rat.cast_prod, Real.sqrt_prod _ (by intro a _; positivity)]
  simp

theorem planarFourWedgeMatrix_rational (D : ℕ) (r : CopyLabel D)
    (A : SectorOccupation 24 4) :
    planarFourWedgeMatrix D A r =
      ((Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) * Real.sqrt 2 / 2^D *
        (rationalHighestEntry D r A.val : ℝ) / Real.sqrt (occupationFactorial A.val : ℝ) : ℝ) : ℂ) := by
  classical
  have he := congrArg (fun M : FockMatrix 24 => M ∅ A.val) (factorial_conjugate_highest D r)
  simp only [diagonalConjugate, occupationDiagonalInv, occupationDiagonal,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Finset.prod_empty, inv_one, one_mul,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    annihilatorList_vacuum_rational] at he
  rw [factorialMode_prod] at he
  have hsum : (∑ b : FourHighestShell 24 D, ∑ xy : IncreasingPair 24,
      (rationalHighestTerm D r b.val.1.val b.val.2.val.1.val b.val.2.val.2.val
        xy.val.1.val xy.val.2.val : ℂ) *
      (rationalWordVacuum [xy.val.1,xy.val.2,b.val.2.val.1,b.val.2.val.2] A.val : ℂ)) =
        (rationalHighestEntry D r A.val : ℂ) := by
    unfold rationalHighestEntry
    push_cast
    rfl
  rw [hsum] at he
  have hn : (Real.sqrt (occupationFactorial A.val : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast occupationFactorial_pos A.val)).ne'
  have hv : planarHighestFourAnnihilator D r ∅ A.val =
      ((Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) * Real.sqrt 2 / 2^D : ℝ) : ℂ) *
       (rationalHighestEntry D r A.val : ℂ) / (Real.sqrt (occupationFactorial A.val : ℝ) : ℂ) := by
    apply (eq_div_iff hn).mpr
    simpa using he
  unfold planarFourWedgeMatrix annihilatorVector
  rw [hv]
  simp only [map_div₀, map_mul, Complex.star_def, Complex.conj_ofReal]
  push_cast
  simp

 
def rationalFourGram (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℚ := fun r s =>
  ∑ A : SectorOccupation 24 4,
    2 * rationalHighestEntry D r A.val * rationalHighestEntry D s A.val /
      (2^(2*D) * occupationFactorial A.val)

theorem planarFourGram_rational (D : ℕ) (r s : CopyLabel D) :
    planarFourGram D r s =
      ((Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) *
        (rationalFourGram D r s : ℝ) *
        Real.sqrt (rationalCopyDiagonal D s.val.val : ℝ) : ℝ) : ℂ) := by
  classical
  unfold planarFourGram
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, planarFourWedgeMatrix_rational,
    Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 1
  unfold rationalFourGram
  rw [Rat.cast_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A _
  have hn : 0 < (occupationFactorial A.val : ℝ) := by
    exact_mod_cast occupationFactorial_pos A.val
  have hn' : Real.sqrt (occupationFactorial A.val : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hsq := Real.sq_sqrt hn.le
  have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  push_cast
  rw [show 2*D=D*2 by omega, pow_mul]
  field_simp
  rw [hsq, hs2]
  ring

end LaughlinFock
end

end OAI
