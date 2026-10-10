import OAI.NumberTheory.TwoPoint.Halasz.HalaszCollisionPartition
import OAI.NumberTheory.TwoPoint.Halasz.HalaszZeroRepresentation

namespace OAI

/-! Counting allowed differences by the zero-representation inequality. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_difference_set_count {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (W : Finset (Fin k → ℤ)) :
    (univ.filter (fun xy : ι×ι => f xy.1-f xy.2∈W)).card≤
      W.card*halaszRepresentationCount f 0 := by
  have hsub : univ.filter (fun xy : ι×ι => f xy.1-f xy.2∈W) ⊆
      W.biUnion (fun w => univ.filter (fun xy : ι×ι => f xy.1-f xy.2=w)) := by
    intro xy hxy
    exact mem_biUnion.mpr ⟨f xy.1-f xy.2,(mem_filter.mp hxy).2,
      mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
  calc
    _ ≤ _ := card_le_card hsub
    _ ≤ ∑ w∈W,(univ.filter (fun xy : ι×ι => f xy.1-f xy.2=w)).card := card_biUnion_le
    _ = ∑ w∈W,halaszRepresentationCount f w := rfl
    _ ≤ ∑ _w∈W,halaszRepresentationCount f 0 :=
      sum_le_sum (fun w _ => halasz_zero_representation_dominates f w)
    _ = _ := by simp

lemma halasz_vinogradov_difference_count (s k M : ℕ) (W : Finset (Fin k → ℤ)) :
    (univ.filter (fun xy : (Fin s → Fin M)×(Fin s → Fin M) =>
      halaszVinogradovFrequency k xy.1-halaszVinogradovFrequency k xy.2∈W)).card≤
        W.card*halaszVinogradovCount s k M := by
  have h := halasz_difference_set_count (halaszVinogradovFrequency (s := s) (N := M) k) W
  rw [← halasz_fiber_energy_representation,halasz_frequency_energy] at h
  exact h

end TwoPointCorrelations

end OAI
