import OAI.MeasureTheory.DyadicAvoidance.OrderedRouting

namespace OAI

open MeasureTheory Set
open scoped BigOperators

namespace Problem310.OrderedRouting

variable {M : ℕ} (ν : Measure Bool) [IsProbabilityMeasure ν]

/-- All nondefault selectors fail precisely on one product cylinder. -/
theorem measure_chooseChild_default :
    Measure.pi (fun _ : Fin M => ν) {S | chooseChild S = Fin.last M} =
      (ν {false}) ^ M := by
  have heq : {S : Fin M → Bool | chooseChild S = Fin.last M} =
      Set.pi Set.univ (fun _ : Fin M => ({false} : Set Bool)) := by
    ext S
    simp [chooseChild_eq_default_iff, Set.mem_pi]
  rw [heq, Measure.pi_pi]
  simp

/-- The first-success choice has the geometric child law. -/
theorem measure_chooseChild_nondefault (i : Fin M) :
    Measure.pi (fun _ : Fin M => ν) {S | chooseChild S = i.castSucc} =
      ν {true} * (ν {false}) ^ i.val := by
  classical
  let f : Fin M → Set Bool := fun j => if j = i then {true} else {false}
  have heq : {S : Fin M → Bool | chooseChild S = i.castSucc} =
      Set.pi (↑(Finset.Iic i) : Set (Fin M)) f := by
    ext S
    change (chooseChild S = i.castSucc) ↔ ∀ j ∈ Finset.Iic i, S j ∈ f j
    rw [chooseChild_eq_nondefault_iff]
    constructor
    · rintro ⟨hi, hprev⟩ j hj
      have hji : j ≤ i := Finset.mem_Iic.mp hj
      by_cases h : j = i
      · subst j
        simpa [f] using hi
      · simpa [f, h] using hprev j (lt_of_le_of_ne hji h)
    · intro h
      constructor
      · simpa [f] using h i (Finset.mem_Iic.mpr le_rfl)
      · intro j hj
        simpa [f, ne_of_lt hj] using h j (Finset.mem_Iic.mpr (le_of_lt hj))
  rw [heq, Measure.pi_pi_finset, ← Finset.Iio_insert]
  rw [Finset.prod_insert (by simp)]
  have hprod : (∏ j ∈ Finset.Iio i, ν (f j)) = (ν {false}) ^ i.val := by
    calc
      (∏ j ∈ Finset.Iio i, ν (f j)) = ∏ _j ∈ Finset.Iio i, ν {false} := by
        apply Finset.prod_congr rfl
        intro j hj
        simp [f, ne_of_lt (Finset.mem_Iio.mp hj)]
      _ = (ν {false}) ^ i.val := by simp
  simpa [f] using congrArg (fun z => ν {true} * z) hprod

end Problem310.OrderedRouting

end OAI
