import OAI.Combinatorics.Ramsey.CycleClique.Construction.PathJoining

namespace OAI

/-!
# Expanded path systems on a clique

Each nontrivial chain is stored as its actual simple vertex list. Distinct
chains are disjoint, both endpoints belong to the clique, and successive
clique vertices on a chain are separated by nonempty outside interiors.
Thus the assigned paths are recovered by splitting at clique vertices.
-/

namespace CycleClique.Construction
variable {V : Type*}

/-- The nontrivial chains of a path system, after expanding assigned paths. -/
structure ExpandedPathSystem (G : SimpleGraph V) (Q : Finset V) where
  chains : List (List V)
  nontrivial : ∀ l ∈ chains, 3 ≤ l.length
  paths : ∀ l ∈ chains, l.Nodup ∧ l.IsChain G.Adj
  disjoint : chains.Pairwise List.Disjoint
  endpoints : ∀ l ∈ chains,
    (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q)
  no_clique_steps : ∀ l ∈ chains,
    l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))

namespace ExpandedPathSystem

variable {G : SimpleGraph V} {Q : Finset V}

def empty (G : SimpleGraph V) (Q : Finset V) : ExpandedPathSystem G Q where
  chains := []
  nontrivial := by simp
  paths := by simp
  disjoint := .nil
  endpoints := by simp
  no_clique_steps := by simp

noncomputable def vertices (S : ExpandedPathSystem G Q) : Finset V := by
  classical
  exact S.chains.flatten.toFinset

/-- Total number of interior vertices outside the clique. -/
noncomputable def amount (S : ExpandedPathSystem G Q) : ℕ := by
  classical
  exact (S.vertices \ Q).card

/-- Clique vertices incident with at least one assigned path. -/
noncomputable def incident (S : ExpandedPathSystem G Q) : ℕ := by
  classical
  exact (S.vertices ∩ Q).card

/-- Each nontrivial chain with `c` clique vertices represents `c-1` paths. -/
noncomputable def assignedCount (S : ExpandedPathSystem G Q) : ℕ :=
  S.incident - S.chains.length

theorem flatten_nodup (S : ExpandedPathSystem G Q) : S.chains.flatten.Nodup :=
  List.nodup_flatten.mpr ⟨fun l hl => (S.paths l hl).1, S.disjoint⟩

theorem vertices_card (S : ExpandedPathSystem G Q) :
    S.vertices.card = S.chains.flatten.length := by
  classical
  exact List.toFinset_card_of_nodup S.flatten_nodup

theorem length_eq_amount_add_incident (S : ExpandedPathSystem G Q) :
    S.chains.flatten.length = S.amount + S.incident := by
  classical
  rw [← S.vertices_card]
  exact (Finset.card_sdiff_add_card_inter S.vertices Q).symm

@[simp] theorem empty_amount (G : SimpleGraph V) (Q : Finset V) :
    (empty G Q).amount = 0 := by
  classical
  simp [amount, vertices, empty]

@[simp] theorem empty_assignedCount (G : SimpleGraph V) (Q : Finset V) :
    (empty G Q).assignedCount = 0 := by
  classical
  simp [assignedCount, incident, vertices, empty]

/-- Closing the system after adjoining exactly the necessary unused
clique vertices: manuscript Lemma `path:interval`. -/
theorem forbidden_interval {k : ℕ} (hk : 3 ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (S : ExpandedPathSystem G Q)
    (hlow : k + 1 - Q.card ≤ S.amount)
    (hhigh : S.amount + S.incident ≤ k + 1) : False := by
  classical
  let u := k + 1 - (S.amount + S.incident)
  have hu : u ≤ (Q \ S.vertices).card := by
    have hcard := Finset.card_sdiff_add_card_inter Q S.vertices
    have hinter : (Q ∩ S.vertices).card = S.incident := by
      simp [incident, Finset.inter_comm]
    rw [hinter] at hcard
    omega
  obtain ⟨J, hJ, hJcard⟩ := Finset.exists_subset_card_eq hu
  let L := S.chains ++ J.toList.map (fun v => [v])
  have hnonempty : ∀ l ∈ L, l ≠ [] := by
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · have := S.nontrivial l hl
      intro heq
      simp [heq] at this
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
      simp
  have hpaths : ∀ l ∈ L, l.Nodup ∧ l.IsChain G.Adj := by
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact S.paths l hl
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
      exact ⟨by simp, .singleton v⟩
  have hdisjoint : L.Pairwise List.Disjoint := by
    apply List.pairwise_append.mpr
    refine ⟨S.disjoint, ?_, ?_⟩
    · apply List.pairwise_map.mpr
      apply J.nodup_toList.imp
      intro v w hvw
      simpa using hvw.symm
    · intro l hl m hm
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
      apply List.disjoint_left.mpr
      intro w hw hwv
      have heq : w = v := by simpa using hwv
      subst w
      have hvJ : v ∈ J := by simpa using hv
      have hvout := (Finset.mem_sdiff.mp (hJ hvJ)).2
      exact hvout (by
        change v ∈ S.chains.flatten.toFinset
        exact List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨l, hl, hw⟩))
  have hends : ∀ l ∈ L,
      (∀ v ∈ l.head?, v ∈ (Q : Set V)) ∧ (∀ v ∈ l.getLast?, v ∈ (Q : Set V)) := by
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact S.endpoints l hl
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hl
      have hvJ : v ∈ J := Finset.mem_toList.mp hv
      have hvQ : v ∈ Q := (Finset.mem_sdiff.mp (hJ hvJ)).1
      simpa using And.intro hvQ hvQ
  have hlen : L.flatten.length = k + 1 := by
    have hsingle : ∀ l : List V, (l.map (fun v => [v])).flatten = l := by
      intro l
      induction l with
      | nil => rfl
      | cons v l ih => simpa using congrArg (List.cons v) ih
    simp only [L, List.flatten_append, List.length_append, hsingle, Finset.length_toList]
    rw [S.length_eq_amount_add_incident, hJcard]
    omega
  have hc := hasCycle_of_disjoint_clique_paths hQ L hnonempty hpaths hdisjoint hends
    (by omega)
  exact hcycle (by simpa [hlen] using hc)

end ExpandedPathSystem

end CycleClique.Construction

end OAI
