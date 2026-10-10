import OAI.NumberTheory.Ostmann.Tree.PairedPartitions
import OAI.NumberTheory.Ostmann.Characters.TreeLeafIndex

namespace OAI

/-! # Cycle projection for two actual rational diagrams -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable def pairedPartitionCorrelation {L C G : Type*}
    [Fintype L] [Fintype C] [DecidableEq L] [DecidableEq C]
    [CommGroup G] [Fintype G] [DecidableEq G]
    (component₁ component₂ : L → C) (f g : (L → G) → ℂ) : ℂ :=
  ((Fintype.card (L → G) : ℂ) *
      (Fintype.card G ^ (Fintype.card L - Fintype.card C) : ℕ))⁻¹ *
    ∑ x : L → G, ∑ y : L → G,
      if partitionProduct component₁ x = partitionProduct component₂ y
      then f x * conj (g y) else 0

/-- The counting denominator is exactly the size of the equal-total sample space. -/
theorem card_pairedPartitions {L C G : Type*}
    [Fintype L] [Fintype C] [DecidableEq L] [DecidableEq C]
    [CommGroup G] [Fintype G] [DecidableEq G]
    (component₁ component₂ : L → C)
    (pivot₂ : ∀ c, {i : L // component₂ i = c}) :
    (Finset.univ.filter fun xy : (L → G) × (L → G) =>
      partitionProduct component₁ xy.1 = partitionProduct component₂ xy.2).card =
        Fintype.card (L → G) * Fintype.card G ^ (Fintype.card L - Fintype.card C) :=
  card_pairedMaps _ _ _ (card_partitionProduct_filter component₂ pivot₂)

/-- The projection reduction in `tree-projection-reduction`, for the actual diagram values. -/
theorem pairedRationalTree_projection {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (n : ℕ) {C : Type*} [Fintype C] [DecidableEq C]
    (component₁ component₂ : TreeLeafIndex (n + 2) → C)
    (pivot₁ : ∀ c, {i : TreeLeafIndex (n + 2) // component₁ i = c})
    (pivot₂ : ∀ c, {i : TreeLeafIndex (n + 2) // component₂ i = c})
    (hc : Fintype.card C ≤ 3 * 2 ^ n)
    (D₁ D₂ : (ZMod p)ˣ) {K₁ K₂ : (ZMod p)ˣ}
    (T₁ : RationalTreeData (ZMod p)ˣ (n + 2) K₁)
    (T₂ : RationalTreeData (ZMod p)ˣ (n + 2) K₂)
    (XL₁ XR₁ XL₂ XR₂ : (ZMod p)ˣ) (c₁ c₂ : TreeLeafTuple Bool (n + 2)) :
    let W₁ := indexedRationalAmplitude g D₁ T₁ XL₁ XR₁ c₁
    let W₂ := indexedRationalAmplitude g D₂ T₂ XL₂ XR₂ c₂
    ∃ cycle : BalancedIncidenceCycle component₁ (bottomQuartet n),
      ‖pairedPartitionCorrelation component₁ component₂ W₁ W₂‖ ^ 2 ≤
        (3 : ℝ) ^ (2 ^ (n + 2)) *
          ((∑ m : TreeLeafIndex (n + 2) → (ZMod p)ˣ,
            ‖cycleAverage cycle.sign W₁ m‖ ^ 2) /
              (Fintype.card (TreeLeafIndex (n + 2) → (ZMod p)ˣ) : ℝ)) := by
  dsimp only
  have hcard : Fintype.card C + Fintype.card (TreeLeafIndex n) ≤
      Fintype.card (TreeLeafIndex (n + 2)) := by
    rw [card_treeLeafIndex, card_treeLeafIndex, pow_add]
    norm_num
    omega
  obtain ⟨cycle⟩ := exists_balancedIncidenceCycle component₁ (bottomQuartet n) hcard
  refine ⟨cycle, ?_⟩
  have h := pairedPartitions_projection component₁ component₂ pivot₁ pivot₂ cycle.sign
    cycle.component_balanced (indexedRationalAmplitude g D₁ T₁ XL₁ XR₁ c₁)
      (indexedRationalAmplitude g D₂ T₂ XL₂ XR₂ c₂)
  apply h.trans
  have hsecond := indexedRationalAmplitude_l2_bound hp g hg henergy D₂ T₂ XL₂ XR₂ c₂
  have hfirst : 0 ≤
      (∑ m : TreeLeafIndex (n + 2) → (ZMod p)ˣ,
        ‖cycleAverage cycle.sign (indexedRationalAmplitude g D₁ T₁ XL₁ XR₁ c₁) m‖ ^ 2) /
          (Fintype.card (TreeLeafIndex (n + 2) → (ZMod p)ˣ) : ℝ) := by positivity
  exact (mul_le_mul_of_nonneg_left hsecond hfirst).trans_eq (mul_comm _ _)

end Ostmann

end OAI
