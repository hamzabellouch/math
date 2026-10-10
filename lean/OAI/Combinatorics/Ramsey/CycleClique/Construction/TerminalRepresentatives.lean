import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalPathClassification
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RepresentativeExclusion

namespace OAI

/-! Terminal classification for every representative pair in every
independent orientation of the completed path system. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}

abbrev TerminalAlternative (S : ExpandedPathSystem G Q) (k d : ℕ) (x y : V) : Prop :=
  (d = 2 ∧ Q.card ≤ S.incident + 2 ∧ Q \ S.vertices ⊆ {x, y}) ∨
  (d = 3 ∧ (Q.card = 9 ∨ Q.card = 11) ∧
    2 * S.assignedCount = Q.card - 3 ∧ S.incident = Q.card - 3 ∧
    (∀ l ∈ S.chains, chainCliqueCount Q l = 2) ∧ x ∉ S.vertices ∧ y ∉ S.vertices) ∨
  (d = 5 ∧ Q.card = 9 ∧ k = 19 ∧ S.assignedCount = 2 ∧ S.incident = 4 ∧
    (∀ l ∈ S.chains, chainCliqueCount Q l = 2) ∧ x ∉ S.vertices ∧ y ∉ S.vertices)

theorem IsOptimal.terminal_representative_classification {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    (U : RawPathSystem G Q) (hUa : U.amount = S.amount)
    (hUe : U.assignedCount = S.assignedCount) (hUi : U.normalize.incident = S.incident)
    (hUvertices : ∀ v ∈ U.vertices, v ∈ Q ∨ v ∈ S.vertices)
    (hsingleton : ∀ l ∈ U.chains, ∀ x ∈ l, l.length = 1 ↔ x ∉ S.vertices)
    {x y : V} (hx : x ∈ U.representatives) (hy : y ∈ U.representatives) (hne : x ≠ y)
    (h : OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d) :
    x ∈ Q ∧ y ∈ Q ∧ S.amount = k - Q.card ∧ d * S.assignedCount ≤ S.amount ∧
      TerminalAlternative S k d x y := by
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨l', hl', heql⟩ := List.mem_map.mp hl
  subst l
  obtain ⟨m, hm, hy⟩ := List.mem_flatten.mp hy
  obtain ⟨m', hm', heqm⟩ := List.mem_map.mp hm
  subst m
  have hxc := chainRepresentatives_mem_cut hx
  have hyc := chainRepresentatives_mem_cut hy
  by_cases hlm : l' = m'
  · subst m'
    obtain ⟨P, R, hchains⟩ := List.append_of_mem hl'
    rcases repCuts_ordered (U.paths l' hl').1 hne hxc hyc with
      ⟨A, B, D, he, hA, hB⟩ | ⟨A, B, D, he, hA, hB⟩
    · exact False.elim (hopt.terminal_same_chain_exclusion ht hQk hkQ hQ hcycle hd hd'
        U hUa hUe hUvertices (by simpa [he] using hchains) hA hB h)
    · exact False.elim (hopt.terminal_same_chain_exclusion ht hQk hkQ hQ hcycle hd hd'
        U hUa hUe hUvertices (by simpa [he] using hchains) hA hB h.reverse)
  · obtain ⟨R, hp⟩ := U.bring_two_front hl' hm' hlm
    let U' := U.reorder (l' :: m' :: R) hp
    have hUa' : U'.amount = S.amount := by simpa [U'] using hUa
    have hUe' : U'.assignedCount = S.assignedCount := by simpa [U'] using hUe
    have hUi' : U'.normalize.incident = S.incident := by simpa [U'] using hUi
    have hUvertices' : ∀ v ∈ U'.vertices, v ∈ Q ∨ v ∈ S.vertices := by
      simpa [U'] using hUvertices
    obtain ⟨A, B, he₁, hA⟩ := hxc
    obtain ⟨C, D, he₂, hC⟩ := hyc
    have hsys : U'.chains = [] ++ (A ++ x :: B) :: [] ++ (C ++ y :: D) :: R := by
      simp [U', RawPathSystem.reorder, he₁, he₂]
    obtain ⟨hL, hAnil, hCnil, hde⟩ := hopt.terminal_different_chain_starts ht hQk hkQ hQ hcycle
      hd hd' U' hUa' hUe' hUvertices' hsys hA hC h
    subst A
    subst C
    have hmemB : x :: B ∈ U.chains := by
      have hh := hl'
      rw [he₁] at hh
      simpa using hh
    have hmemD : y :: D ∈ U.chains := by
      have hh := hm'
      rw [he₂] at hh
      simpa using hh
    have hBx : B = [] ↔ x ∉ S.vertices := by simpa using hsingleton _ hmemB x (by simp)
    have hDy : D = [] ↔ y ∉ S.vertices := by simpa using hsingleton _ hmemD y (by simp)
    obtain ⟨_, _, halt⟩ := hopt.terminal_starting_classification ht hQk hkQ hQ hcycle hd hd'
      U' hUa' hUe' hUi' hUvertices' (P := []) (M := []) (R := R) (by simpa using hsys) hBx hDy hne h
    exact ⟨(U.endpoints _ hmemB).1 x (by simp),
      (U.endpoints _ hmemD).1 y (by simp), hL, hde, halt⟩

theorem IsOptimal.terminal_completed_classification {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    (p : List V → Bool) {x y : V}
    (hx : x ∈ (S.toRaw.completeClique.orientChains p).representatives)
    (hy : y ∈ (S.toRaw.completeClique.orientChains p).representatives) (hne : x ≠ y)
    (h : OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d) :
    x ∈ Q ∧ y ∈ Q ∧ S.amount = k - Q.card ∧ d * S.assignedCount ≤ S.amount ∧
      TerminalAlternative S k d x y := by
  apply hopt.terminal_representative_classification ht hQk hkQ hQ hcycle hd hd'
    (S.toRaw.completeClique.orientChains p) (by simp) (by simp) (by simp) ?_
    (fun l hl x hx => S.oriented_complete_singleton_iff p hl hx) hx hy hne h
  intro v hv
  rw [RawPathSystem.orientChains_vertices, RawPathSystem.completeClique_vertices] at hv
  exact (Finset.mem_union.mp hv).symm

theorem TerminalAlternative.parameter_unique {k d d' : ℕ} {x y x' y' : V}
    (ht : 9 ≤ Q.card) (h : TerminalAlternative S k d x y)
    (h' : TerminalAlternative S k d' x' y') : d = d' := by
  rcases h with ⟨hd, hv, _⟩ | ⟨hd, _, _, hv, _, _, _⟩ | ⟨hd, ht9, _, _, hv, _, _, _⟩ <;>
    rcases h' with ⟨hd', hv', _⟩ | ⟨hd', _, _, hv', _, _, _⟩ |
      ⟨hd', ht9', _, _, hv', _, _, _⟩ <;> omega

end CycleClique.Construction.ExpandedPathSystem

end OAI
