import OAI.Combinatorics.Ramsey.CycleClique.Construction.AssignedProfileOperations

namespace OAI

/-! At a representative cut, at most one old assigned path is absorbed.
Its outside vertices are precisely the leading outside segment of the tail. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type*} {Q : Finset V}

structure AssignedCutProfile (Q : Finset V) (A : List V) (x : V) (B : List V) where
  before : List ℕ
  after : List ℕ
  removed : List ℕ
  lead : List V
  endpoint : V
  rest : List V
  tail_eq : x :: B = lead ++ endpoint :: rest
  outside : ∀ z ∈ lead, z ∉ Q
  endpoint_mem : endpoint ∈ Q
  before_profile : AssignedAmounts Q A before
  after_profile : AssignedAmounts Q (endpoint :: rest) after
  removed_sum : removed.sum = lead.length
  removed_eq : removed = if A = [] then [] else [lead.length]
  lead_nonempty : A ≠ [] → lead ≠ []
  removed_length : removed.length = if A = [] then 0 else 1
  full_profile : AssignedAmounts Q (A ++ x :: B) (before ++ removed ++ after)

theorem exists_assigned_cut_profile {A B : List V} {x : V}
    (hends : (∀ v ∈ (A ++ x :: B).head?, v ∈ Q) ∧
      (∀ v ∈ (A ++ x :: B).getLast?, v ∈ Q))
    (hsteps : (A ++ x :: B).IsChain (fun u v => ¬ (u ∈ Q ∧ v ∈ Q)))
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) :
    Nonempty (AssignedCutProfile Q A x B) := by
  classical
  by_cases hAne : A = []
  · subst A
    obtain ⟨w, hw⟩ := exists_assignedAmounts hends hsteps
    have hx : x ∈ Q := hends.1 x (by simp)
    exact ⟨{
      before := [], after := w, removed := [], lead := [], endpoint := x, rest := B
      tail_eq := rfl
      outside := by simp
      endpoint_mem := hx
      before_profile := .nil
      after_profile := hw
      removed_sum := rfl
      removed_eq := by simp
      lead_nonempty := by simp
      removed_length := by simp
      full_profile := by simpa using hw }⟩
  · have hx : x ∉ Q := by
      intro hx
      have hh := (List.isChain_append.mp hsteps).2.2
      exact hh (A.getLast hAne) (List.getLast?_eq_some_getLast hAne) x (by simp)
        ⟨hA _ (List.getLast?_eq_some_getLast hAne), hx⟩
    have hAends : (∀ v ∈ A.head?, v ∈ Q) ∧ (∀ v ∈ A.getLast?, v ∈ Q) := by
      refine ⟨?_, hA⟩
      intro v hv
      exact hends.1 v (List.mem_head?_append_of_mem_head? hv)
    obtain ⟨wa, hwa⟩ := exists_assignedAmounts hAends (List.isChain_append.mp hsteps).1
    have htailEnd : ∀ v ∈ (x :: B).getLast?, v ∈ Q := by
      intro v hv
      apply hends.2 v
      have he := List.getLast?_eq_some_getLast (show x :: B ≠ [] by simp)
      simpa only [List.getLast?_append, he, Option.or] using hv
    have hlastQ : (x :: B).getLast (by simp) ∈ Q :=
      htailEnd _ (List.getLast?_eq_some_getLast (by simp))
    obtain ⟨J, y, C, heq, hJ, hy⟩ := exists_first_clique
      ⟨(x :: B).getLast (by simp), List.getLast_mem (by simp), hlastQ⟩
    have hJne : J ≠ [] := by
      intro hj
      subst J
      have hxy : x = y := (List.cons.inj heq).1
      exact hx (by simpa only [hxy] using hy)
    have htailEnds : (∀ v ∈ (y :: C).head?, v ∈ Q) ∧
        (∀ v ∈ (y :: C).getLast?, v ∈ Q) := by
      refine ⟨by simpa using hy, ?_⟩
      intro v hv
      apply htailEnd v
      rw [heq, List.getLast?_append,
        List.getLast?_eq_some_getLast (show y :: C ≠ [] by simp)]
      simpa only [List.getLast?_eq_some_getLast (show y :: C ≠ [] by simp), Option.or] using hv
    have htailSteps : (y :: C).IsChain (fun u v => ¬ (u ∈ Q ∧ v ∈ Q)) := by
      have hh := (List.isChain_append.mp hsteps).2.1
      rw [heq] at hh
      exact (List.isChain_append.mp hh).2.1
    obtain ⟨wb, hwb⟩ := exists_assignedAmounts htailEnds htailSteps
    exact ⟨{
      before := wa, after := wb, removed := [J.length], lead := J, endpoint := y, rest := C
      tail_eq := heq
      outside := hJ
      endpoint_mem := hy
      before_profile := hwa
      after_profile := hwb
      removed_sum := by simp
      removed_eq := by simp [hAne]
      lead_nonempty := fun _ => hJne
      removed_length := by simp [hAne]
      full_profile := by
        rw [heq]
        simpa [List.append_assoc] using hwa.append_segment hAne hJ hJne hwb }⟩

end CycleClique.Construction

end OAI
