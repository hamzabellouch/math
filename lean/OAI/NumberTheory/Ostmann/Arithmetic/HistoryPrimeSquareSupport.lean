import Mathlib.Data.ZMod.Units
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryActualNumerators
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrimeRows
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeSquareLifts

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPrimeSquareSupport
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPatternRows HistoryRepeatedRenaming ClearedCoefficientFlags MvPolynomial

theorem power_dvd_cleared_iff (p n : ℕ) [Fact p.Prime]
    (D N A B X Y : ℤ) (hD : (D : ZMod p) ≠ 0)
    (hclear : D*N=A*X+B*Y) :
    (p:ℤ)^n ∣ N ↔ (p:ℤ)^n ∣ A*X+B*Y := by
  have hc : IsCoprime (p:ℤ) D :=
    (ZMod.coe_int_isUnit_iff_isCoprime D p).mp (isUnit_iff_ne_zero.mpr hD)
  rw [← hclear]
  exact (hc.pow_left.dvd_mul_left_iff).symm

theorem square_dvd_lift_iff (p : ℕ) [Fact p.Prime]
    (D N A B X Y carry u v : ℤ) (hD : (D : ZMod p) ≠ 0)
    (hclear : D*N=A*(X+(p:ℤ)*u)+B*(Y+(p:ℤ)*v))
    (hbase : A*X+B*Y=(p:ℤ)*carry) :
    (p:ℤ)^2 ∣ N ↔ (A:ZMod p)*(u:ZMod p)+(B:ZMod p)*(v:ZMod p)=-(carry:ZMod p) := by
  rw [power_dvd_cleared_iff p 2 D N A B _ _ hD hclear,pow_two]
  exact PrimeSquareLifts.square_divides_lift_iff_residue p A B X Y carry u v hbase

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem denominator_ne_zero (h : History l) (hs : h.Supported V outside)
    (i : InternalKey h) (p : ℕ) [Fact p.Prime]
    (hx : HistoryPrimeRows.AncestorUnits h i
      (fun j : PatternKey h => (patternSample h j.val:ZMod p)))
    (hV : ∀ j ≤ l, V j < p) :
    (eval (fun j : PatternKey h => patternSample h j.val)
      (commonDenominator (row h hs i).1 (row h hs i).2):ZMod p) ≠ 0 := by
  obtain ⟨ha,hb,_⟩ := HistoryPrimeRows.row_regular_nonzero_field h hs i _ hx
    (HistoryPrimeRows.frequency_units h hs p hV)
  have hd := (coefficients_cleared (row h hs i).1 (row h hs i).2 _ ha hb).1
  rwa [Expr.eval₂_cast_int] at hd

theorem actual_power_dvd_iff (h : History l) (hs : h.Supported V outside)
    (i : InternalKey h) (p n : ℕ) [Fact p.Prime]
    (hx : HistoryPrimeRows.AncestorUnits h i
      (fun j : PatternKey h => (patternSample h j.val:ZMod p)))
    (hV : ∀ j ≤ l, V j < p) :
    (p:ℤ)^n ∣ HistoryActualNumerators.actual h i ↔
      (p:ℤ)^n ∣
        eval (fun j : PatternKey h => patternSample h j.val) (leftFlag h hs i)*
          (h.root.giantPlus:ℤ)+
        eval (fun j : PatternKey h => patternSample h j.val) (rightFlag h hs i)*
          (h.root.giantMinus:ℤ) :=
  power_dvd_cleared_iff p n _ _ _ _ _ _ (denominator_ne_zero h hs i p hx hV)
    (HistoryActualNumerators.integer_linear_cleared h hs i)

end Ostmann.Arithmetic.HistoryPrimeSquareSupport

end

end OAI
