import OAI.Combinatorics.Ramsey.CycleClique.Construction.RepresentativeCuts

namespace OAI

/-! All noninitial representatives lie outside the clique; their number
is exactly the number of assigned paths. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type*} {Q : Finset V}

theorem representativesFrom_outside {prev : V} {xs : List V}
    (hsteps : (prev :: xs).IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    ∀ x ∈ representativesFrom Q prev xs, x ∉ Q := by
  induction xs generalizing prev with
  | nil => simp [representativesFrom]
  | cons y ys ih =>
    have hs := List.isChain_cons_cons.mp hsteps
    intro x hx
    simp only [representativesFrom, List.mem_append] at hx
    by_cases hp : prev ∈ Q
    · simp only [hp, ↓reduceIte, List.mem_singleton] at hx
      rcases hx with rfl | hx
      · exact fun hy => hs.1 ⟨hp, hy⟩
      · exact ih hs.2 x hx
    · simp only [hp, ↓reduceIte, List.not_mem_nil, false_or] at hx
      exact ih hs.2 x hx

noncomputable def chainOutsideCount (Q : Finset V) (l : List V) : ℕ :=
  (l.filter (fun v => decide (v ∉ Q))).length

theorem chainRepresentatives_outside_count {l : List V}
    (hends : (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    chainOutsideCount Q (chainRepresentatives Q l) = chainCliqueCount Q l - 1 := by
  cases l with
  | nil => rfl
  | cons x xs =>
    have hx : x ∈ Q := hends.1 x (by simp)
    have hfilter : (representativesFrom Q x xs).filter (fun v => decide (v ∉ Q)) =
        representativesFrom Q x xs := by
      apply List.filter_eq_self.mpr
      intro v hv
      simpa using representativesFrom_outside hsteps v hv
    have hlength := representativesFrom_length x xs hends.2
    simp only [chainOutsideCount, chainRepresentatives, List.filter_cons, hx,
      not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, hfilter]
    omega

namespace RawPathSystem

variable {G : SimpleGraph V}

theorem representatives_outside_count (S : RawPathSystem G Q) :
    chainOutsideCount Q S.representatives = S.assignedCount := by
  unfold chainOutsideCount representatives assignedCount rawAssignedCount
  rw [List.filter_flatten, List.length_flatten, List.map_map]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  exact chainRepresentatives_outside_count (S.endpoints l hl) (S.no_clique_steps l hl)

theorem completed_representatives_outside_count (S : ExpandedPathSystem G Q) :
    chainOutsideCount Q S.toRaw.completeClique.representatives = S.assignedCount := by
  rw [representatives_outside_count, completeClique_assignedCount,
    ExpandedPathSystem.toRaw_assignedCount]

end RawPathSystem

end CycleClique.Construction

end OAI
