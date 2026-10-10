import Mathlib
import OAI.Analysis.LaughlinFock.RationalCoupling
import OAI.Analysis.LaughlinFock.RelativeTransfer

namespace OAI

/-! Rational Three. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
def rationalAlphaWeight (t : ℕ) (b : RowEntry t) : ℚ :=
  2^(rowP b) * (t.factorial : ℚ) * (rowI b).factorial /
    (2^t * ((rowP b).factorial : ℚ) * (rowJ b).factorial)

theorem rationalAlphaWeight_pos (t : ℕ) (b : RowEntry t) :
    0 < rationalAlphaWeight t b := by
  unfold rationalAlphaWeight
  positivity

theorem rationalCouplingWeight_pos {c : ℚ} (hc : 0 < c) (z k p : ℕ) :
    0 < rationalCouplingWeight c z k p := by
  unfold rationalCouplingWeight
  positivity

 

def rationalComparisonRow (t : Fin 8) (ell : ℚ) (a : RowEntry t.val → ℚ) : ComparisonRow where
  t := t
  ell := ell
  alpha b := (a b : ℝ) * Real.sqrt (rationalAlphaWeight t.val b : ℝ)

theorem planarThreeCoefficient_rational (z T p : ℕ) (hz : z ≤ T) :
    planarThreeCoefficient z T p = (rationalCoupling 2 z (T-z) p : ℝ) *
      Real.sqrt (rationalCouplingWeight 2 z (T-z) p : ℝ) := by
  rw [planarThreeCoefficient, ite_eq_left hz]
  simpa only [Rat.cast_ofNat, show (1:ℝ)+2=3 by norm_num] using
    polynomialCouplingCoefficient_rational 2 (by norm_num) z (T-z) p

theorem rationalAlphaWeight_cancellation {t T z : ℕ} (b : RowEntry t)
    (hz : z ≤ T) (hb : rowP b+rowJ b=T) :
    rationalAlphaWeight t b * rationalCouplingWeight 2 z (T-z) (rowP b) =
      rationalCouplingWeight 2 z (T-z) t := by
  have hi : T-t = rowI b := by simp [rowI, hb]
  have hj : T-rowP b = rowJ b := by omega
  unfold rationalAlphaWeight rationalCouplingWeight
  rw [Nat.add_sub_of_le hz, hi, hj]
  field_simp

theorem alpha_mul_planarThree {t T z : ℕ} (a : RowEntry t → ℚ)
    (b : RowEntry t) (hz : z ≤ T) (hb : rowP b+rowJ b=T) :
    ((a b : ℝ) * Real.sqrt (rationalAlphaWeight t b : ℝ)) *
      planarThreeCoefficient z T (rowP b) =
      ((a b * rationalCoupling 2 z (T-z) (rowP b) : ℚ) : ℝ) *
        Real.sqrt (rationalCouplingWeight 2 z (T-z) t : ℝ) := by
  rw [planarThreeCoefficient_rational z T (rowP b) hz, Rat.cast_mul]
  rw [mul_mul_mul_comm, ← Real.sqrt_mul (by exact_mod_cast (rationalAlphaWeight_pos t b).le)]
  have he : (rationalAlphaWeight t b : ℝ) * (rationalCouplingWeight 2 z (T-z) (rowP b) : ℝ) =
      (rationalCouplingWeight 2 z (T-z) t : ℝ) := by
    exact_mod_cast rationalAlphaWeight_cancellation b hz hb
  rw [he]

 
def rationalThreeTrace (z t : ℕ) (ell : ℚ) (a : RowEntry t → ℚ) : ℚ :=
  ∑ T ∈ Finset.range 16, if z ≤ T ∧ t ≤ T then
    let X := ∑ b : RowEntry t, if rowP b+rowJ b=T then
      a b*rationalCoupling 2 z (T-z) (rowP b) else 0
    rationalCouplingWeight 2 z (T-z) t * X *
      (X+2*ell*rationalCoupling 2 z (T-z) t)
  else 0

theorem planarRowThreeTrace_rational (z : ℕ) (t : Fin 8)
    (ell : ℚ) (a : RowEntry t.val → ℚ) :
    planarRowThreeTrace z t.val (rationalComparisonRow t ell a).ell
      (rationalComparisonRow t ell a).alpha = (rationalThreeTrace z t.val ell a : ℝ) := by
  classical
  unfold planarRowThreeTrace rationalThreeTrace
  push_cast
  apply Finset.sum_congr rfl
  intro T _
  split_ifs with ht
  · let X : ℚ := ∑ b : RowEntry t.val, if rowP b+rowJ b=T then
        a b*rationalCoupling 2 z (T-z) (rowP b) else 0
    have hX : (∑ b : RowEntry t.val, if rowP b+rowJ b=T then
        (rationalComparisonRow t ell a).alpha b*planarThreeCoefficient z T (rowP b) else 0) =
        (X : ℝ) * Real.sqrt (rationalCouplingWeight 2 z (T-z) t.val : ℝ) := by
      dsimp [X]
      rw [Rat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs with hb
      · exact alpha_mul_planarThree a b ht.1 hb
      · simp
    rw [hX, planarThreeCoefficient_rational z T t.val ht.1]
    change 2*(ell:ℝ)*((rationalCoupling 2 z (T-z) t.val : ℝ)*
        Real.sqrt (rationalCouplingWeight 2 z (T-z) t.val : ℝ))*
        ((X:ℝ)*Real.sqrt (rationalCouplingWeight 2 z (T-z) t.val : ℝ))+
        ((X:ℝ)*Real.sqrt (rationalCouplingWeight 2 z (T-z) t.val : ℝ))^2 = _
    have hn : 0 ≤ (rationalCouplingWeight 2 z (T-z) t.val : ℝ) := by
      exact_mod_cast (rationalCouplingWeight_pos (by norm_num : (0:ℚ)<2) z (T-z) t.val).le
    have hs := Real.sq_sqrt hn
    calc
      _ = (Real.sqrt (rationalCouplingWeight 2 z (T-z) t.val : ℝ))^2 *
        (X:ℝ)*((X:ℝ)+2*(ell:ℝ)*(rationalCoupling 2 z (T-z) t.val : ℝ)) := by ring
      _ = _ := by rw [hs]; simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat]; rfl
  · simp

end LaughlinFock
end

end OAI
