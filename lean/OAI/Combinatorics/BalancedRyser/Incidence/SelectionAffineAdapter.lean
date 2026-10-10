import OAI.Combinatorics.BalancedRyser.Candidates.CandidateBasics
import OAI.Combinatorics.BalancedRyser.Incidence.AffinePlaneInstance
import OAI.Combinatorics.BalancedRyser.Selection.Selection
import OAI.Combinatorics.BalancedRyser.Selection.SelectionOccupancy

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

namespace SelectionOccupancy

variable {F} (C : Configuration F)

theorem initial_trackedSets {c₀ : ℝ}
    (hsize : ∀ l, c₀ * Fintype.card F ≤ ((initial C l).card : ℝ)) :
    Selection.TrackedSets (coordinatePlane F) (initial C) c₀ := by
  intro l
  exact ⟨by simpa only [coordinatePlane_linePoints] using initial_subset_line C l, hsize l⟩

theorem candidate_good_trackedSets {c Cbound : ℝ}
    (hgood : CandidateGraphGood C.merged c Cbound) :
    Selection.TrackedSets (coordinatePlane F) (initial C) (1 / 5) :=
  initial_trackedSets C (candidate_good_initial C hgood).2

theorem selection_finalTracked_eq {V : Type*} (line : V → Line F)
    (a : Slot F → V) (hline : ∀ s, line (a s) = (C.choice s).line) (l : Line F) :
    Selection.finalTracked (coordinatePlane F) line (initial C) a l = final C l := by
  ext p
  simp only [Selection.finalTracked, final, Finset.mem_filter]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    intro S hS hne
    rcases Finset.mem_image.mp hS with ⟨s, _, rfl⟩
    simpa only [hline s, coordinatePlane] using (h s (by simpa only [hline s] using hne))
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    intro s hne
    have hmem : (C.choice s).line ∈ C.splitLines :=
      Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩
    simpa only [hline s, coordinatePlane] using (h (C.choice s).line hmem
      (by simpa only [hline s] using hne))

theorem occupancy_of_selection_finalTracked {V : Type*} (line : V → Line F)
    (a : Slot F → V) (hline : ∀ s, line (a s) = (C.choice s).line)
    {c Cbound ρ : ℝ} (hV : C.Valid)
    (hgood : CandidateGraphGood C.merged c Cbound)
    (hfinal : ∀ l, ρ * Fintype.card F ≤
      ((Selection.finalTracked (coordinatePlane F) line (initial C) a l).card : ℝ)) :
    C.Occupancy ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊ := by
  apply occupancy_of_candidate_good_final C hV hgood
  intro l
  simpa only [selection_finalTracked_eq C line a hline l] using hfinal l

end SelectionOccupancy
end
end Balanced

end OAI
