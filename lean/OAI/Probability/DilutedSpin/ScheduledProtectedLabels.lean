import OAI.Probability.DilutedSpin.RegularFrameExtraction
import OAI.Probability.DilutedSpin.TwoPointLabeling
import OAI.Probability.DilutedSpin.VertexContinuity

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

lemma leaves_stem {n : ℕ} (S : PrescribedTree n) (r : ℕ) :
    leaves (stem S r)=leaves S := by
  induction r with
  | zero => rfl
  | succ r ih => rw [stem,leaves_unary,ih]

lemma leaves_doubled {n : ℕ} (S : PrescribedTree n) :
    leaves (doubled S)=2*leaves S := by
  change (∑ _ : Fin 2, leaves S)=2*leaves S
  simp [Nat.two_mul]

lemma leaves_splitFrame {n : ℕ} (S : PrescribedTree n) (r d : ℕ) :
    leaves (splitFrame S r d)=2*leaves S := by
  rw [splitFrame,leaves_stem,leaves_doubled,leaves_stem]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
open scoped BigOperators

/-- The shifted children retain exactly their topology leaves. In particular
one fixed dictionary arity works for every admissible depth assignment. -/
lemma delayed_node_leaves (H lo : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (q : (j : Fin k) → (C j).Vertex → ℕ)
    (had : ∀ j, Admissible (C j) (q j) lo (lo+H)) :
    leaves (PrescribedTree.node k (fun j => realize H (lo+1) (C j)
      (fun v => q j v+1))) = Fintype.card (ReducedTopology.node k hk C).Leaf := by
  change (∑ j, leaves (realize H (lo+1) (C j) (fun v => q j v+1))) =
    Fintype.card ((j : Fin k) × (C j).Leaf)
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun j _ => by
    rw [realize_translate H lo 1,realize_leaves H lo (C j) (q j) (had j)])

/-- Actual assignment-dependent protected labeling for the genuinely delayed
multileaf target. The dictionary size depends only on the reduced topology,
not the grid horizon or any of its branching-coordinate assignments. -/
theorem delayed_node_protected_labeling (H lo r d : ℕ) (k : ℕ+)
    (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (q : (j : Fin k) → (C j).Vertex → ℕ)
    (had : ∀ j, Admissible (C j) (q j) lo (lo+H)) :
    let S := PrescribedTree.node k (fun j => realize H (lo+1) (C j)
      (fun v => q j v+1))
    let t := 2*Fintype.card (ReducedTopology.node k hk C).Leaf-2
    ∃ (b : S.Leaf) (e : Option (Fin (t+1)) ≃ (splitFrame S r d).Leaf),
      e none=splitFrameLeaf S r d 0 b ∧
      e (some (Fin.last t))=splitFrameLeaf S r d 1 b := by
  dsimp only
  let S := PrescribedTree.node k (fun j => realize H (lo+1) (C j)
    (fun v => q j v+1))
  have hcard := delayed_node_leaves H lo k hk C q had
  have hpos := leaves_pos S
  have hc : Fintype.card (splitFrame S r d).Leaf =
      2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+2 := by
    rw [card_leaf,leaves_splitFrame]
    change leaves S = _ at hcard
    rw [hcard]
    omega
  obtain ⟨b⟩ := leaf_nonempty S
  obtain ⟨e,he₀,he₁⟩ := splitFrame_canonical_labeling S r d
    (2*Fintype.card (ReducedTopology.node k hk C).Leaf-2) b hc
  exact ⟨b,e,he₀,he₁⟩

/-- Full regular-domain frame and protected-label extraction, with the exact
old and delayed integer levels used by the physical multileaf inequality. -/
theorem regular_node_labeled_frame {L : ℕ} [NeZero L] {η : ℝ} (hη : 0<η)
    (hlarge : 1<η*(L:ℝ)) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (Q : Option (ReducedTopology.node k hk C).Vertex → Fin L)
    (hQ : regularShapeDomain (.node k hk C) L η Q) :
    ∃ H r d : ℕ, L=H+1+1+r+1+(d+1) ∧ (Q none).val=d+1 ∧
      (Q (some none)).val=r+1+(d+1) ∧
      (∀ j, Admissible (C j) (fun v => (Q (some (some ⟨j,v⟩))).val)
        (r+1+(d+1)+1) (r+1+(d+1)+1+H)) ∧
      let S := PrescribedTree.node k (fun j =>
        realize H (r+1+1+(d+1)+1) (C j)
          (fun v => (Q (some (some ⟨j,v⟩))).val+1))
      let t := 2*Fintype.card (ReducedTopology.node k hk C).Leaf-2
      ∃ (b : S.Leaf) (e : Option (Fin (t+1)) ≃ (splitFrame S (r+1) (d+1)).Leaf),
        e none=splitFrameLeaf S (r+1) (d+1) 0 b ∧
        e (some (Fin.last t))=splitFrameLeaf S (r+1) (d+1) 1 b := by
  obtain ⟨H,r,d,hL,hd,he,ha⟩ := regular_node_frame hη hlarge k hk C Q hQ
  refine ⟨H,r,d,hL,hd,he,ha,?_⟩
  have hh := delayed_node_protected_labeling H (r+1+(d+1)+1) (r+1) (d+1) k hk C
      (fun j v => (Q (some (some ⟨j,v⟩))).val) ha
  dsimp only at hh ⊢
  rw [show r+1+(d+1)+1+1=r+1+1+(d+1)+1 by omega] at hh
  exact hh

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
