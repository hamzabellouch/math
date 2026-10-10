import Mathlib
import OAI.Combinatorics.Chromatic.Walls.SignedMultiplicity
import OAI.Combinatorics.Chromatic.GradedAlgebra.CompleteUnit

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open EnergyLaurent WallUnits PowerSeries
open scoped LaurentSeries
noncomputable section

def strictUnitEquiv (a n : ℕ) (h : a=0) : Strict n ≃ UnitIndex a n :=
  Equiv.subtypeEquivRight (fun f=>by simp only [ite_eq_left h])

def weakUnitEquivSame (a n : ℕ) (h : a≠0) : Weak n ≃ UnitIndex a n :=
  Equiv.subtypeEquivRight (fun f=>by simp only [ite_eq_right h])

lemma unitAdmissible (a n : ℕ) (k : ℤ) : Admissible (unitEnergy a n k) := by
  by_cases h : a=0
  · exact admissible_equiv (strictAdmissible n k) (strictUnitEquiv a n h) (fun _=>rfl)
  · exact admissible_equiv (weakAdmissible n k) (weakUnitEquivSame a n h) (fun _=>rfl)

def indexedUnitSeries (a n : ℕ) (k : ℤ) : LaurentSeries ℚ :=
  series (unitEnergy a n k) (unitAdmissible a n k)

def indexedUnit (a : ℕ) (k : ℤ) : PowerSeries (RatFunc ℚ) :=
  if a=0 then elementary RationalRay.q (RationalRay.v^k)
  else complete RationalRay.q (RationalRay.v^k)

theorem indexedUnit_literal_expansion (a n : ℕ) (k : ℤ) :
    LaurentRay.atInfinity (coeff n (indexedUnit a k))=indexedUnitSeries a n k := by
  unfold indexedUnit
  by_cases h : a=0
  · rw [ite_eq_left h,elementary_literal_expansion]
    exact series_equiv (strictAdmissible n k) (unitAdmissible a n k)
      (strictUnitEquiv a n h) (fun _=>rfl)
  · rw [ite_eq_right h,complete_literal_expansion]
    exact series_equiv (weakAdmissible n k) (unitAdmissible a n k)
      (weakUnitEquivSame a n h) (fun _=>rfl)

end
end ElementaryPositivity.UnitSelections
end
end

end OAI
