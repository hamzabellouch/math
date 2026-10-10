import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseSelect
import OAI.Combinatorics.KMedian.Geometry.RationalCompletedCost

namespace OAI


                                         
section
namespace MetricKMedian.Completion.Rational
open Finset
variable {F H : Type} [DecidableEq H] {j : ℕ}

theorem score_image (d : Fin j → H → ℚ) (f : F → H) (O : Finset F) :
    score d (O.image f)=score (fun c a => d c (f a)) O := by
  unfold score
  apply sum_congr rfl
  intro c _
  by_cases hO : O.Nonempty
  · rw [dite_eq_left (hO.image f),dite_eq_left hO]
    simp only [image_image]
    rfl
  · have hI : ¬(O.image f).Nonempty := by simpa only [image_nonempty] using hO
    rw [dite_eq_right hO,dite_eq_right hI]

end MetricKMedian.Completion.Rational
namespace MetricKMedian.SparseSelect
variable {α : Type}

theorem best_of_witness (P : α → Bool) (cost : α → ℚ) (L : List α)
    (a : α) (ha : a∈L) (hP : P a=true) :
    ∃ b, best P cost L=some b ∧ b∈L ∧ P b=true ∧ cost b ≤ cost a := by
  cases hb : best P cost L with
  | none =>
    have hh := (best_spec P cost L).1.mp hb a ha
    rw [hP] at hh
    contradiction
  | some b =>
    obtain ⟨hbmem,hbP,hbcost⟩ := (best_spec P cost L).2 b hb
    exact ⟨b,rfl,hbmem,hbP,hbcost a ha hP⟩

end MetricKMedian.SparseSelect
end

end OAI
