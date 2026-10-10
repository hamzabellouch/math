import Mathlib
import OAI.Analysis.LaughlinFock.CertificateRows
import OAI.Analysis.LaughlinFock.IntegerCoupling

namespace OAI

/-! Three Certificate. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators

def integerThreeTrace (z t : ℕ) (ell : ℚ) (a : RowEntry t → ℚ) : ℚ :=
  ∑ T ∈ Finset.range 16, if z ≤ T ∧ t ≤ T then
    let X := ∑ b : RowEntry t, if rowP b+rowJ b=T then
      a b*(integerCoupling 2 z (T-z) (rowP b) : ℚ) else 0
    rationalCouplingWeight 2 z (T-z) t * X *
      (X+2*ell*(integerCoupling 2 z (T-z) t : ℚ))
  else 0

theorem rationalThreeTrace_integer (z t : ℕ) (ell : ℚ) (a : RowEntry t → ℚ) :
    rationalThreeTrace z t ell a = integerThreeTrace z t ell a := by
  simp only [rationalThreeTrace, integerThreeTrace, ← rationalCoupling_integer, Int.cast_ofNat]

def integerRowsThreeTrace (z : ℕ) : ℚ :=
  ∑ t : Fin 8, integerThreeTrace z t.val (certificateEll t) (certificateAlpha t)

theorem planarRowsThreeTrace_integer (z : ℕ) :
    planarRowsThreeTrace certificateRows z = (integerRowsThreeTrace z : ℝ) := by
  unfold planarRowsThreeTrace integerRowsThreeTrace
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact (planarRowThreeTrace_rational z t (certificateEll t) (certificateAlpha t)).trans
    (congrArg (fun q:ℚ => (q:ℝ)) (rationalThreeTrace_integer z t.val _ _))

theorem certificate_three_2 : integerRowsThreeTrace 2 <
    (3/2 : ℚ)*(3*(2:ℚ)-1)*(-1/2)^(2:ℕ) := by
  decide +kernel

theorem certificate_three_4 : integerRowsThreeTrace 4 <
    (3/2 : ℚ)*(3*(4:ℚ)-1)*(-1/2)^(4:ℕ) := by
  decide +kernel

theorem certificate_three_5 : integerRowsThreeTrace 5 <
    (3/2 : ℚ)*(3*(5:ℚ)-1)*(-1/2)^(5:ℕ) := by
  decide +kernel

theorem certificate_three_6 : integerRowsThreeTrace 6 <
    (3/2 : ℚ)*(3*(6:ℚ)-1)*(-1/2)^(6:ℕ) := by
  decide +kernel

theorem certificate_three_7 : integerRowsThreeTrace 7 <
    (3/2 : ℚ)*(3*(7:ℚ)-1)*(-1/2)^(7:ℕ) := by
  decide +kernel

theorem certificate_three_8 : integerRowsThreeTrace 8 <
    (3/2 : ℚ)*(3*(8:ℚ)-1)*(-1/2)^(8:ℕ) := by
  decide +kernel

theorem certificate_three_9 : integerRowsThreeTrace 9 <
    (3/2 : ℚ)*(3*(9:ℚ)-1)*(-1/2)^(9:ℕ) := by
  decide +kernel

theorem certificate_three_10 : integerRowsThreeTrace 10 <
    (3/2 : ℚ)*(3*(10:ℚ)-1)*(-1/2)^(10:ℕ) := by
  decide +kernel

theorem certificate_three_11 : integerRowsThreeTrace 11 <
    (3/2 : ℚ)*(3*(11:ℚ)-1)*(-1/2)^(11:ℕ) := by
  decide +kernel

theorem certificate_three_12 : integerRowsThreeTrace 12 <
    (3/2 : ℚ)*(3*(12:ℚ)-1)*(-1/2)^(12:ℕ) := by
  decide +kernel

theorem certificate_three_13 : integerRowsThreeTrace 13 <
    (3/2 : ℚ)*(3*(13:ℚ)-1)*(-1/2)^(13:ℕ) := by
  decide +kernel

theorem certificate_three_14 : integerRowsThreeTrace 14 <
    (3/2 : ℚ)*(3*(14:ℚ)-1)*(-1/2)^(14:ℕ) := by
  decide +kernel

theorem certificate_three_15 : integerRowsThreeTrace 15 <
    (3/2 : ℚ)*(3*(15:ℚ)-1)*(-1/2)^(15:ℕ) := by
  decide +kernel

theorem certificate_three (z : ComparedThreeBlock) :
    planarRowsThreeTrace certificateRows z.val.val <
      (3/2 : ℝ)*(3*(z.val.val:ℝ)-1)*(-1/2)^z.val.val := by
  rw [planarRowsThreeTrace_integer]
  have h (n : ℕ) (hn : n=2 ∨ 4≤n) (hn' : n<16) : integerRowsThreeTrace n <
      (3/2 : ℚ)*(3*(n:ℚ)-1)*(-1/2)^n := by
    interval_cases n
    · omega
    · omega
    · exact certificate_three_2
    · omega
    · exact certificate_three_4
    · exact certificate_three_5
    · exact certificate_three_6
    · exact certificate_three_7
    · exact certificate_three_8
    · exact certificate_three_9
    · exact certificate_three_10
    · exact certificate_three_11
    · exact certificate_three_12
    · exact certificate_three_13
    · exact certificate_three_14
    · exact certificate_three_15
  have hl := (Rat.cast_lt (K:=ℝ)).mpr (h z.val.val z.property z.val.isLt)
  simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast,
    Rat.cast_sub, Rat.cast_pow, Rat.cast_neg, Rat.cast_one] using hl

end LaughlinFock
end

end OAI
