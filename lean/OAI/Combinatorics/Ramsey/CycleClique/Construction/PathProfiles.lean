import OAI.Combinatorics.Ramsey.CycleClique.Construction.AssignedAmounts
import OAI.Combinatorics.Ramsey.CycleClique.Construction.Patterns

namespace OAI

/-! Amount profiles of actual path systems, including singleton components
for unused clique vertices. No canonical ordering is assumed here. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type*} {Q : Finset V}

theorem exists_chain_profiles (C : List (List V))
    (hends : ∀ l ∈ C, (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : ∀ l ∈ C, l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    ∃ P, List.Forall₂ (AssignedAmounts Q) C P := by
  induction C with
  | nil => exact ⟨[], .nil⟩
  | cons l C ih =>
    obtain ⟨w, hw⟩ := exists_assignedAmounts (hends l (by simp)) (hsteps l (by simp))
    obtain ⟨P, hP⟩ := ih (fun l hl => hends l (by simp [hl]))
      (fun l hl => hsteps l (by simp [hl]))
    exact ⟨w :: P, .cons hw hP⟩

namespace ChainProfiles

theorem amount {C : List (List V)} {P : List (List ℕ)}
    (hp : List.Forall₂ (AssignedAmounts Q) C P) :
    patternAmount P = chainOutsideCount Q C.flatten := by
  induction hp with
  | nil => rfl
  | @cons l w C P h hw ih =>
    have hs := h.sum_eq
    simp only [patternAmount, List.map_cons, List.sum_cons, List.flatten_cons,
      chainOutsideCount, List.filter_append, List.length_append] at hs ih ⊢
    omega

theorem assignedCount {C : List (List V)} {P : List (List ℕ)}
    (hp : List.Forall₂ (AssignedAmounts Q) C P) :
    (P.map List.length).sum = rawAssignedCount Q C := by
  induction hp with
  | nil => rfl
  | @cons l w C P h hw ih =>
    simp only [List.map_cons, List.sum_cons, rawAssignedCount] at ih ⊢
    rw [h.length_eq, ih]

theorem vertices {C : List (List V)} {P : List (List ℕ)}
    (hp : List.Forall₂ (AssignedAmounts Q) C P)
    (hne : ∀ l ∈ C, l ≠ [])
    (hhead : ∀ l ∈ C, ∀ v ∈ l.head?, v ∈ Q) :
    patternVertices P = chainCliqueCount Q C.flatten := by
  induction hp with
  | nil => rfl
  | @cons l w C P h hw ih =>
    have hl := h.length_eq
    have hpos := chainCliqueCount_pos (hne l (by simp)) (hhead l (by simp))
    have ht := ih (fun l hl => hne l (by simp [hl]))
      (fun l hl => hhead l (by simp [hl]))
    simp only [patternVertices, List.map_cons, List.sum_cons, List.flatten_cons,
      chainCliqueCount_append] at ht ⊢
    omega

theorem positive {C : List (List V)} {P : List (List ℕ)}
    (hp : List.Forall₂ (AssignedAmounts Q) C P) :
    ∀ w ∈ P, ∀ a ∈ w, 0 < a := by
  induction hp with
  | nil => simp
  | @cons l w C P h hw ih =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact h.positive
    · exact ih u hu

end ChainProfiles

namespace ExpandedPathSystem

variable {G : SimpleGraph V}

theorem exists_complete_profile (S : ExpandedPathSystem G Q) :
    ∃ P : List (List ℕ),
      List.Forall₂ (AssignedAmounts Q) S.toRaw.completeClique.chains P ∧
      patternVertices P = Q.card ∧ patternAmount P = S.amount ∧
      (P.map List.length).sum = S.assignedCount ∧
      ∀ w ∈ P, ∀ a ∈ w, 0 < a := by
  obtain ⟨P, hp⟩ := exists_chain_profiles S.toRaw.completeClique.chains
    S.toRaw.completeClique.endpoints S.toRaw.completeClique.no_clique_steps
  have hnonempty : ∀ l ∈ S.toRaw.completeClique.chains, l ≠ [] := by
    intro l hl
    change l ∈ S.chains ++ (Q \ S.toRaw.vertices).toList.map (fun v => [v]) at hl
    rcases List.mem_append.mp hl with hl | hl
    · have ht := S.nontrivial l hl
      intro he
      simp only [he, List.length_nil] at ht
      omega
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
      simp
  refine ⟨P, hp, ?_, ?_, ?_, ChainProfiles.positive hp⟩
  · rw [ChainProfiles.vertices hp hnonempty
      (fun l hl => (S.toRaw.completeClique.endpoints l hl).1),
      ← S.toRaw.completeClique.representatives_length,
      S.toRaw.completeClique_representatives_length]
  · rw [ChainProfiles.amount hp, ← S.toRaw.completeClique.amount_eq_outside_count,
      RawPathSystem.completeClique_amount, toRaw_amount]
  · rw [ChainProfiles.assignedCount hp, ← RawPathSystem.assignedCount,
      RawPathSystem.completeClique_assignedCount, toRaw_assignedCount]

end ExpandedPathSystem

end CycleClique.Construction

end OAI
