import OAI.Probability.ContinuumTransition.MomentBootstrap

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem occupation_card_binary {ι : Type} [Fintype ι] (D C : Set Space)
    (s : Finset ι) (x : ι → Space) (hx : x ∈ binaryRegion (D ∩ C) (D \ C) s) :
    occupation C x = (s.card : ℝ) := by
  unfold occupation
  rw [← Fintype.card_coe s]
  congr 1
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  have hh := hx i
  by_cases hi : i ∈ s
  · simp only [ite_eq_left hi] at hh
    exact iff_of_true hh.2 hi
  · simp only [ite_eq_right hi] at hh
    exact iff_of_false hh.2 hi

end ContinuumTemperature
end

end OAI
