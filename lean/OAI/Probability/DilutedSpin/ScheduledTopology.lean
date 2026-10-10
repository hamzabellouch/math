import OAI.Probability.DilutedSpin.RegularDepth
import OAI.Probability.DilutedSpin.ShiftedTree

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Finite rooted topology with unary vertices suppressed. Children have
fixed distinct positions, hence leaves remain labeled throughout realization. -/
inductive ReducedTopology : Type
  | leaf : ReducedTopology
  | node (k : ℕ+) (hk : 2 ≤ (k:ℕ)) (C : Fin k → ReducedTopology) : ReducedTopology

namespace ReducedTopology

@[reducible] def Vertex : ReducedTopology → Type
  | .leaf => Empty
  | .node k _ C => Option ((i : Fin k) × Vertex (C i))

def Leaf : ReducedTopology → Type
  | .leaf => Unit
  | .node k _ C => (i : Fin k) × Leaf (C i)

instance vertexFintype : (S : ReducedTopology) → Fintype S.Vertex
  | .leaf => inferInstanceAs (Fintype Empty)
  | .node _ _ C => by
    letI : ∀ i, Fintype (Vertex (C i)) := fun i => vertexFintype (C i)
    exact inferInstanceAs (Fintype (Option ((i : _) × Vertex (C i))))

instance leafFintype : (S : ReducedTopology) → Fintype S.Leaf
  | .leaf => inferInstanceAs (Fintype Unit)
  | .node _ _ C => by
    letI : ∀ i, Fintype (Leaf (C i)) := fun i => leafFintype (C i)
    exact inferInstanceAs (Fintype ((i : _) × Leaf (C i)))

/-- Strict ancestry and the genuine terminal grid horizon. -/
def Admissible : (S : ReducedTopology) → (S.Vertex → ℕ) → ℕ → ℕ → Prop
  | .leaf, _, _, _ => True
  | .node _ _ C, q, lo, hi =>
    lo ≤ q none ∧ q none < hi ∧
      ∀ i, Admissible (C i) (fun v => q (some ⟨i,v⟩)) (q none+1) hi

lemma admissible_mono_lower (S : ReducedTopology) (q : S.Vertex → ℕ)
    {lo lo' hi : ℕ} (hlo : lo'≤lo) (h : Admissible S q lo hi) : Admissible S q lo' hi := by
  cases S with
  | leaf => trivial
  | node k hk C => exact ⟨hlo.trans h.1,h.2⟩

lemma admissible_lower (S : ReducedTopology) (q : S.Vertex → ℕ) {lo hi : ℕ}
    (h : Admissible S q lo hi) (v : S.Vertex) : lo ≤ q v := by
  induction S generalizing lo hi with
  | leaf => exact v.elim
  | node k hk C ih =>
    cases v with
    | none => exact h.1
    | some v => exact h.1.trans ((Nat.le_succ _).trans (ih v.1 _ (h.2.2 v.1) v.2))

lemma admissible_upper (S : ReducedTopology) (q : S.Vertex → ℕ) {lo hi : ℕ}
    (h : Admissible S q lo hi) (v : S.Vertex) : q v < hi := by
  induction S generalizing lo hi with
  | leaf => exact v.elim
  | node k hk C ih =>
    cases v with
    | none => exact h.2.1
    | some v => exact ih v.1 _ (h.2.2 v.1) v.2

/-- Expand a depth assignment into the actual leveled prescribed tree.
Outside admissible assignments this is still total; no such assignment is
used in the geometry or analytic theorems below. -/
def realize : (r : ℕ) → (d : ℕ) → (S : ReducedTopology) →
    (S.Vertex → ℕ) → PrescribedTree r
  | 0, _, _, _ => .leaf
  | r+1, d, .leaf, q => PrescribedTree.unary (realize r (d+1) .leaf q)
  | r+1, d, .node k hk C, q =>
    if d < q none then PrescribedTree.unary (realize r (d+1) (.node k hk C) q)
    else .node k (fun i => realize r (d+1) (C i) (fun v => q (some ⟨i,v⟩)))

lemma realize_leaves (r d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (h : Admissible S q d (d+r)) :
    PrescribedTree.leaves (realize r d S q) = Fintype.card S.Leaf := by
  induction r generalizing d S with
  | zero =>
    cases S with
    | leaf => rfl
    | node k hk C => have := h.2.1; have := h.1; omega
  | succ r ih =>
    cases S with
    | leaf =>
      rw [realize,PrescribedTree.leaves_unary]
      exact ih (d+1) .leaf q trivial
    | node k hk C =>
      rw [realize]
      split_ifs with hd
      · rw [PrescribedTree.leaves_unary]
        apply ih
        exact ⟨hd,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2⟩
      · have he : q none=d := by have := h.1; omega
        simp only [PrescribedTree.leaves]
        change _ = Fintype.card ((i : Fin k) × (C i).Leaf)
        rw [Fintype.card_sigma]
        apply Finset.sum_congr rfl
        intro i _
        apply ih
        simpa [he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2.2 i

/-- Actual vertex multiplicities, with assigned *absolute* depths. Aligned
copies may repeat a coordinate but never merge their branching vertices. -/
theorem realize_branchingCount (r d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (h : Admissible S q d (d+r)) (P : ℕ → Prop) :
    PrescribedTree.branchingCount (realize r d S q) (fun u => P (d+u)) =
      ∑ v : S.Vertex, if P (q v) then 1 else 0 := by
  classical
  induction r generalizing d S with
  | zero =>
    cases S with
    | leaf => exact (Finset.sum_empty).symm
    | node k hk C => have := h.2.1; have := h.1; omega
  | succ r ih =>
    cases S with
    | leaf =>
      rw [realize,PrescribedTree.branchingCount_unary]
      have hh := ih (d+1) .leaf q trivial
      convert hh using 1; simp [Nat.add_comm,Nat.add_left_comm]
    | node k hk C =>
      rw [realize]
      split_ifs with hd
      · rw [PrescribedTree.branchingCount_unary]
        have ha : Admissible (.node k hk C) q (d+1) ((d+1)+r) :=
          ⟨hd,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2⟩
        have hh := ih (d+1) (.node k hk C) q ha
        convert hh using 1; simp [Nat.add_comm,Nat.add_left_comm]
      · have he : q none=d := by have := h.1; omega
        change _ = ∑ v : Option ((i : Fin k) × (C i).Vertex), _
        rw [Fintype.sum_option,Fintype.sum_sigma]
        simp only [PrescribedTree.branchingCount,Nat.add_zero,show 1<(k:ℕ) by omega,and_true,he]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        have ha : Admissible (C i) (fun v => q (some ⟨i,v⟩)) (d+1) ((d+1)+r) := by
          simpa [he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2.2 i
        have hh := ih (d+1) (C i) (fun v => q (some ⟨i,v⟩)) ha
        convert hh using 1; simp [Nat.add_comm,Nat.add_left_comm]

end ReducedTopology
end DilutedSpinGlass
end

end

end OAI
