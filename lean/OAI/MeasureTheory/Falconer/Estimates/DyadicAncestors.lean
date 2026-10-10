import OAI.MeasureTheory.Falconer.Estimates.DyadicCenters
import OAI.MeasureTheory.Falconer.Estimates.ParallelCount

namespace OAI

/-!
# Ancestor groups for the retained graph witnesses

There are at most `2^(d*g)` ancestor groups at relative depth `g`.
All centers within one group lie in the same original dyadic cube, giving
the diameter used in the parallel-test witness argument.
-/

namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem dyadic_ancestor_count {d n g : ℕ} (A : Finset (List (Fin d → Bool)))
    (hA : ∀ p ∈ A, p.length = n) (hg : g ≤ n) :
    (A.image (List.take g)).card ≤ 2^(d*g) := by
  rw [← card_cubePaths]
  apply Finset.card_le_card
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  simp only [mem_cubePaths, List.length_take, hA q hq, min_eq_left hg]

theorem DyadicCube.center_mem_ancestor {d : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) (p : List (Fin d → Bool)) (g : ℕ) :
    (Q.descendant p).center ∈ (Q.descendant (p.take g)).carrier := by
  have he : Q.descendant p = (Q.descendant (p.take g)).descendant (p.drop g) := by
    rw [← Q.descendant_append, List.take_append_drop]
  rw [he]
  exact (Q.descendant (p.take g)).descendant_subset (p.drop g)
    (((Q.descendant (p.take g)).descendant (p.drop g)).center_mem
      ((Q.descendant (p.take g)).descendant_side_pos (Q.descendant_side_pos hQ _) _))

theorem DyadicCube.same_ancestor_center_dist {d n g : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) (p q : List (Fin d → Bool))
    (hp : p.length = n) (hg : g ≤ n) (heq : p.take g = q.take g) :
    dist (Q.descendant p).center (Q.descendant q).center ≤
      Real.sqrt d * (Q.side / (2 : ℝ)^g) := by
  have hcp := Q.center_mem_ancestor hQ p g
  have hcq := Q.center_mem_ancestor hQ q g
  rw [← heq] at hcq
  have hh := (Q.descendant (p.take g)).dist_le (Q.descendant_side_pos hQ _).le hcp hcq
  simpa only [Q.descendant_side, List.length_take, hp, min_eq_left hg] using hh

/-- One eligible point--angle witness per cell supplies the literal
parallel test; the candidate count then costs only the number of actual
dyadic ancestors, independently of their occupied masses. -/
theorem DyadicCube.parallel_count {d n g C : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) (A : Finset (List (Fin d → Bool)))
    (hA : ∀ p ∈ A, p.length = n) (hg : g ≤ n)
    (w₀ base : Space d) (hw₀ : ‖w₀‖ = 1) {τ δ W : ℝ} (hδ : 0 ≤ δ)
    (hwidth : 2*τ + 2*δ*(Real.sqrt d * (Q.side/(2 : ℝ)^g)) ≤ W)
    (hwitness : ∀ a ∈ A, ∃ w : Space d, ‖w‖ = 1 ∧ ‖w-w₀‖ ≤ δ ∧
      (A.filter (fun z => z.take g = a.take g ∧
        ‖(Q.descendant z).center - (Q.descendant a).center‖ ≤
          Real.sqrt d * (Q.side/(2 : ℝ)^g) ∧
        ‖perpendicularPart w ((Q.descendant z).center - (Q.descendant a).center)‖ ≤ W)).card ≤ C) :
    (A.filter (fun z => ‖perpendicularPart w₀
      ((Q.descendant z).center - base)‖ ≤ τ)).card ≤ C*2^(d*g) := by
  apply parallel_count_from_witnesses A (fun p => (Q.descendant p).center)
    (List.take g) w₀ base hw₀ hδ (dyadic_ancestor_count A hA hg) hwidth
  · intro x hx y _ hxy
    simpa only [dist_eq_norm] using Q.same_ancestor_center_dist hQ x y (hA x hx) hg hxy
  · exact hwitness

end Falconer

end OAI
