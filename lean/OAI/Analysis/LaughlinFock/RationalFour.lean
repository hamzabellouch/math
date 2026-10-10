import Mathlib
import OAI.Analysis.LaughlinFock.RationalThree

namespace OAI

/-! Rational Four. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def rationalCopyDiagonal (D r : ℕ) : ℚ :=
  2^r / ((r.factorial : ℚ) * (D-r).factorial)

def rationalCopyPolynomial (D T r p j k : ℕ) : ℚ :=
  if r ≤ j+k then
    rationalCoupling 1 r (j+k-r) j * rationalCoupling 1 (D-r) (T-D) p
  else 0

def rationalCopyWeight (D T p j k : ℕ) : ℚ :=
  2 * (j.factorial : ℚ) * k.factorial * p.factorial /
    (2^(j+k+T) * ((T-D).factorial : ℚ))

theorem rationalCopyDiagonal_pos (D r : ℕ) : 0 < rationalCopyDiagonal D r := by
  unfold rationalCopyDiagonal
  positivity

theorem rationalCopyWeight_pos (D T p j k : ℕ) : 0 < rationalCopyWeight D T p j k := by
  unfold rationalCopyWeight
  positivity

theorem couplingWeight_copy {D T r p j k : ℕ} (hr : r ≤ D)
    (hD : D ≤ T) (hw : p+j+k=T) (hrjk : r ≤ j+k) :
    2 * rationalCouplingWeight 1 r (j+k-r) j *
      rationalCouplingWeight 1 (D-r) (T-D) p =
        rationalCopyDiagonal D r * rationalCopyWeight D T p j k := by
  have h1 : r+(j+k-r)=j+k := Nat.add_sub_of_le hrjk
  have h2 : D-r+(T-D)=T-r := by omega
  have h3 : T-r-p=j+k-r := by omega
  have hpow : (2:ℚ)^T = 2^r*2^(T-r) := by rw [← pow_add, Nat.add_sub_of_le (hr.trans hD)]
  unfold rationalCouplingWeight rationalCopyDiagonal rationalCopyWeight
  rw [h1, h2, h3, show j+k-j=k by omega]
  norm_num only [one_pow, one_add_one_eq_two, one_mul]
  simp only [pow_add]
  rw [hpow]
  field_simp

 
theorem planarCopyCoefficient_rational {D T : ℕ} (r : CopyLabel D)
    (p j k : ℕ) (hD : D ≤ T) (hw : p+j+k=T) :
    planarCopyCoefficient D T r.val.val p j k =
      (rationalCopyPolynomial D T r.val.val p j k : ℝ) *
      (Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) *
        Real.sqrt (rationalCopyWeight D T p j k : ℝ)) := by
  have hr : r.val.val ≤ D := Nat.le_of_lt_succ r.val.isLt
  have hCoupling (z n a : ℕ) :
      polynomialCouplingCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) z n a =
        (rationalCoupling 1 z n a : ℝ)*Real.sqrt (rationalCouplingWeight 1 z n a : ℝ) := by
    simpa only [Rat.cast_one, show (1:ℝ)+1=2 by norm_num] using
      polynomialCouplingCoefficient_rational 1 (by norm_num) z n a
  unfold planarCopyCoefficient rationalCopyPolynomial
  by_cases hjk : r.val.val ≤ j+k
  · rw [ite_eq_left ⟨r.property, hr, hD, hjk, hw⟩, ite_eq_left hjk, hCoupling, hCoupling,
      Rat.cast_mul]
    have hs : Real.sqrt 2 * Real.sqrt (rationalCouplingWeight 1 r.val.val (j+k-r.val.val) j : ℝ) *
        Real.sqrt (rationalCouplingWeight 1 (D-r.val.val) (T-D) p : ℝ) =
        Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) *
        Real.sqrt (rationalCopyWeight D T p j k : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ)≤2),
        ← Real.sqrt_mul (mul_nonneg (by norm_num) (by
          exact_mod_cast (rationalCouplingWeight_pos (by norm_num : (0:ℚ)<1) r.val.val (j+k-r.val.val) j).le))]
      have hc := congrArg (fun q:ℚ => (q:ℝ)) (couplingWeight_copy hr hD hw hjk)
      push_cast at hc
      rw [hc, Real.sqrt_mul (by exact_mod_cast (rationalCopyDiagonal_pos D r.val.val).le)]
    linear_combination ((rationalCoupling 1 r.val.val (j+k-r.val.val) j : ℝ)*
      (rationalCoupling 1 (D-r.val.val) (T-D) p : ℝ))*hs
  · rw [ite_eq_right (by tauto), ite_eq_right hjk]
    simp

 
def rationalFourFactor {t : ℕ} (D : ℕ) (b c : RowEntry t) : ℚ :=
  2 * 2^(rowP b) * 2^(rowP c) * (t.factorial : ℚ) *
    (rowI b).factorial * (rowI c).factorial /
    (2^t * (2^(rowFourLevel b c))^2 * ((rowFourLevel b c-D).factorial : ℚ))

theorem rationalFourFactor_pos {t : ℕ} (D : ℕ) (b c : RowEntry t) :
    0 < rationalFourFactor D b c := by
  unfold rationalFourFactor
  positivity

theorem row_copy_weight_product {t D : ℕ} (b c : RowEntry t) :
    rationalAlphaWeight t b * rationalAlphaWeight t c *
      rationalCopyWeight D (rowFourLevel b c) (rowP b) (rowJ b) (rowI c) *
      rationalCopyWeight D (rowFourLevel b c) (rowP c) (rowJ c) (rowI b) =
        (rationalFourFactor D b c)^2 := by
  have h1 : (2:ℚ)^(rowJ b+rowI c) = 2^(rowFourLevel b c)/2^(rowP b) := by
    rw [eq_div_iff (by positivity)]
    rw [← pow_add]
    congr 1
    dsimp [rowFourLevel]
    omega
  have h2 : (2:ℚ)^(rowJ c+rowI b) = 2^(rowFourLevel b c)/2^(rowP c) := by
    rw [eq_div_iff (by positivity)]
    rw [← pow_add]
    congr 1
    have := rowFourLevel_symm b c
    dsimp [rowFourLevel] at *
    omega
  unfold rationalAlphaWeight rationalCopyWeight rationalFourFactor
  rw [pow_add (2:ℚ) (rowJ b+rowI c), pow_add (2:ℚ) (rowJ c+rowI b), h1, h2]
  field_simp

 
def rationalFourTrace (D t : ℕ) (a : RowEntry t → ℚ) :
    Matrix (CopyLabel D) (CopyLabel D) ℚ := fun r s =>
  -(∑ b : RowEntry t, ∑ c : RowEntry t, if D ≤ rowFourLevel b c then
    a b*a c*rationalFourFactor D b c *
      rationalCopyPolynomial D (rowFourLevel b c) r.val.val (rowP b) (rowJ b) (rowI c) *
      rationalCopyPolynomial D (rowFourLevel b c) s.val.val (rowP c) (rowJ c) (rowI b)
    else 0)

theorem planarRowFourTrace_rational (D : ℕ) (t : Fin 8)
    (ell : ℚ) (a : RowEntry t.val → ℚ) (r s : CopyLabel D) :
    planarRowFourTrace D t.val (rationalComparisonRow t ell a).alpha r s =
      Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) *
      (rationalFourTrace D t.val a r s : ℝ) *
      Real.sqrt (rationalCopyDiagonal D s.val.val : ℝ) := by
  classical
  unfold planarRowFourTrace rationalFourTrace
  push_cast
  simp only [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  by_cases hD : D ≤ rowFourLevel b c
  · rw [ite_eq_left hD,
      planarCopyCoefficient_rational r _ _ _ hD rfl,
      planarCopyCoefficient_rational s _ _ _ hD (rowFourLevel_symm c b)]
    have hA : 0 ≤ (rationalAlphaWeight t.val b : ℝ) := by
      exact_mod_cast (rationalAlphaWeight_pos t.val b).le
    have hB : 0 ≤ (rationalAlphaWeight t.val c : ℝ) := by
      exact_mod_cast (rationalAlphaWeight_pos t.val c).le
    have hC : 0 ≤ (rationalCopyWeight D (rowFourLevel b c) (rowP b) (rowJ b) (rowI c) : ℝ) := by
      exact_mod_cast (rationalCopyWeight_pos _ _ _ _ _).le
    have hR : Real.sqrt (rationalAlphaWeight t.val b : ℝ) *
        Real.sqrt (rationalAlphaWeight t.val c : ℝ) *
        Real.sqrt (rationalCopyWeight D (rowFourLevel b c) (rowP b) (rowJ b) (rowI c) : ℝ) *
        Real.sqrt (rationalCopyWeight D (rowFourLevel b c) (rowP c) (rowJ c) (rowI b) : ℝ) =
          (rationalFourFactor D b c : ℝ) := by
      rw [← Real.sqrt_mul hA, ← Real.sqrt_mul (mul_nonneg hA hB),
        ← Real.sqrt_mul (mul_nonneg (mul_nonneg hA hB) hC)]
      have hc := congrArg (fun q:ℚ => (q:ℝ)) (row_copy_weight_product (D:=D) b c)
      push_cast at hc
      rw [hc, Real.sqrt_sq (by exact_mod_cast (rationalFourFactor_pos D b c).le)]
    dsimp only [rationalComparisonRow]
    push_cast
    linear_combination ((a b:ℝ)*(a c:ℝ)*
      (rationalCopyPolynomial D (rowFourLevel b c) r.val.val (rowP b) (rowJ b) (rowI c) : ℝ)*
      (rationalCopyPolynomial D (rowFourLevel b c) s.val.val (rowP c) (rowJ c) (rowI b) : ℝ)*
      Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ)*
      Real.sqrt (rationalCopyDiagonal D s.val.val : ℝ))*hR
  · simp [planarCopyCoefficient, hD]

end LaughlinFock
end

end OAI
