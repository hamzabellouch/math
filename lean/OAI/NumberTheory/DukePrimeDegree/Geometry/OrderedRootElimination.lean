import OAI.NumberTheory.DukePrimeDegree.Geometry.EliminationRootChart

namespace OAI

/-!
# Gaussian root elimination in row order

Clearing positive roots in lexicographic row order preserves all earlier
zeros. The restricted one-root chart is an open embedding into the
previous slice, so successive steps can build a chart for the full
upper unipotent group.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rootsBefore {n : ℕ} (a b : Fin n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ (p.1 < a ∨ (p.1 = a ∧ p.2 < b)))

def pivotsBefore {n : ℕ} (a : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun r => r < a)

lemma rootsBefore_stable {n : ℕ} {a b : Fin n} (_hab : a < b) :
    ∀ r, (r, b) ∈ rootsBefore a b → (r, a) ∈ rootsBefore a b := by
  intro r hr
  obtain ⟨_, hr⟩ := Finset.mem_filter.mp hr
  have hra : r < a := by
    rcases hr.2 with h | ⟨_, h⟩
    · exact h
    · exact (lt_irrefl b h).elim
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hra, Or.inl hra⟩

lemma notMem_pivotsBefore {n : ℕ} {a b : Fin n} (hab : a < b) :
    b ∉ pivotsBefore a := by
  intro h
  exact (not_lt_of_ge hab.le) (Finset.mem_filter.mp h).2

lemma one_mem_ordered_eliminationSlice {n : ℕ} (a b : Fin n) :
    ZeroPattern (rootsBefore a b) (1 : G n) ∧ NonzeroPivots (pivotsBefore a) (1 : G n) := by
  constructor
  · intro p hp
    have hlt := (Finset.mem_filter.mp hp).2.1
    change (1 : Matrix (Fin n) (Fin n) ℝ) p.1 p.2 = 0
    simp [ne_of_lt hlt]
  · intro r _
    change (1 : Matrix (Fin n) (Fin n) ℝ) r r ≠ 0
    simp

/-- The next root factor gives an open coordinate embedding into the
slice left by the earlier eliminations. -/
theorem eliminationRoot_isOpenEmbedding {n : ℕ}
    (P : Finset (Fin n × Fin n)) (D : Finset (Fin n))
    {a b : Fin n} (hab : a ≠ b)
    (hP : ∀ r, (r, b) ∈ P → (r, a) ∈ P) (hb : b ∉ D) :
    Topology.IsOpenEmbedding
      (fun z : EliminationSlice (insert (a, b) P) (insert a D) × ℝ =>
        ((eliminationRootHomeomorph P D hab hP hb).symm z).val) :=
  (elimination_pivot_isOpen P D a).isOpenEmbedding_subtypeVal.comp
    (eliminationRootHomeomorph P D hab hP hb).symm.isOpenEmbedding

def orderedEliminationRootHomeomorph {n : ℕ} {a b : Fin n} (hab : a < b) :=
  eliminationRootHomeomorph (rootsBefore a b) (pivotsBefore a) (ne_of_lt hab)
    (rootsBefore_stable hab) (notMem_pivotsBefore hab)

/-- An existing partial coordinate chart can be extended by the next
root while retaining openness and injectivity of the actual map. -/
theorem eliminationRoot_extend_embedding {n : ℕ}
    (P : Finset (Fin n × Fin n)) (D : Finset (Fin n))
    {a b : Fin n} (hab : a ≠ b)
    (hP : ∀ r, (r, b) ∈ P → (r, a) ∈ P) (hb : b ∉ D)
    {T Y : Type*} [TopologicalSpace T] [TopologicalSpace Y]
    (F : EliminationSlice P D × T → Y) (hF : Topology.IsOpenEmbedding F) :
    Topology.IsOpenEmbedding
      (fun z : EliminationSlice (insert (a, b) P) (insert a D) × (ℝ × T) =>
        F (((eliminationRootHomeomorph P D hab hP hb).symm (z.1, z.2.1)).val, z.2.2)) := by
  exact (hF.comp ((eliminationRoot_isOpenEmbedding P D hab hP hb).prodMap
    (Topology.IsOpenEmbedding.id (X := T)))).comp
      (Homeomorph.prodAssoc _ _ _).symm.isOpenEmbedding

end DukePrimeDegree

end

end OAI
