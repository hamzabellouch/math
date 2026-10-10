import OAI.Combinatorics.Ramsey.CycleClique.Construction.ChainCounts
import OAI.Combinatorics.Ramsey.CycleClique.Construction.ListSurgery

namespace OAI

/-! Raw chain collections used during representative surgery. Isolated
clique vertices and empty pieces are allowed until normalization. -/

namespace CycleClique.Construction
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

structure RawPathSystem (G : SimpleGraph V) (Q : Finset V) where
  chains : List (List V)
  paths : ∀ l ∈ chains, l.Nodup ∧ l.IsChain G.Adj
  disjoint : chains.Pairwise List.Disjoint
  endpoints : ∀ l ∈ chains,
    (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q)
  no_clique_steps : ∀ l ∈ chains,
    l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))

namespace RawPathSystem

noncomputable def normalize (S : RawPathSystem G Q) : ExpandedPathSystem G Q :=
  normalizeChains S.chains S.paths S.disjoint S.endpoints S.no_clique_steps

noncomputable def vertices (S : RawPathSystem G Q) : Finset V := by
  classical
  exact S.chains.flatten.toFinset

noncomputable def amount (S : RawPathSystem G Q) : ℕ := by
  classical
  exact (S.vertices \ Q).card

noncomputable def assignedCount (S : RawPathSystem G Q) : ℕ :=
  rawAssignedCount Q S.chains

theorem flatten_nodup (S : RawPathSystem G Q) : S.chains.flatten.Nodup :=
  List.nodup_flatten.mpr ⟨fun l hl => (S.paths l hl).1, S.disjoint⟩

@[simp] theorem normalize_amount (S : RawPathSystem G Q) :
    S.normalize.amount = S.amount := by
  classical
  exact normalizeChains_amount S.chains S.paths S.disjoint S.endpoints S.no_clique_steps

@[simp] theorem normalize_assignedCount (S : RawPathSystem G Q) :
    S.normalize.assignedCount = S.assignedCount :=
  normalizeChains_assignedCount S.chains S.paths S.disjoint S.endpoints S.no_clique_steps

end RawPathSystem

namespace ExpandedPathSystem

def toRaw (S : ExpandedPathSystem G Q) : RawPathSystem G Q where
  chains := S.chains
  paths := S.paths
  disjoint := S.disjoint
  endpoints := S.endpoints
  no_clique_steps := S.no_clique_steps

@[simp] theorem toRaw_amount (S : ExpandedPathSystem G Q) : S.toRaw.amount = S.amount := rfl

@[simp] theorem toRaw_assignedCount (S : ExpandedPathSystem G Q) :
    S.toRaw.assignedCount = S.assignedCount := S.assignedCount_eq_raw.symm

end ExpandedPathSystem

end CycleClique.Construction

end OAI
