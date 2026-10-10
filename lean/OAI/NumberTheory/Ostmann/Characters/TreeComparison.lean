import OAI.NumberTheory.Ostmann.Characters.QuartetOuterAverage
import OAI.NumberTheory.Ostmann.Tree.PairedRationalReduction

namespace OAI

/-! # Quantitative paired comparison for the actual rational diagrams

This assembles the graph cycle, all six local quartet estimates, exact
product-fiber coordinates, and horizontal density domination. The error
is explicit; no tree-comparison theorem is taken as an input.
-/

namespace Ostmann

open scoped BigOperators

theorem pairedRationalTree_comparison {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hflat : MixedFourierBound g ε)
    (n : ℕ) {C : Type*} [Fintype C] [DecidableEq C]
    (component₁ component₂ : TreeLeafIndex (n + 2) → C)
    (pivot₁ : ∀ c, {i : TreeLeafIndex (n + 2) // component₁ i = c})
    (pivot₂ : ∀ c, {i : TreeLeafIndex (n + 2) // component₂ i = c})
    (hc : Fintype.card C ≤ 3 * 2 ^ n)
    (D₁ D₂ : (ZMod p)ˣ) {K₁ K₂ : (ZMod p)ˣ}
    (T₁ : RationalTreeData (ZMod p)ˣ (n + 2) K₁)
    (T₂ : RationalTreeData (ZMod p)ˣ (n + 2) K₂)
    (XL₁ XR₁ XL₂ XR₂ : (ZMod p)ˣ) (c₁ c₂ : TreeLeafTuple Bool (n + 2))
    (cL cR : TreeLeafIndex n → Bool)
    (hconj : ∀ q, quartetBlockEquiv Bool n c₁ q = ((cL q, !(cL q)), (cR q, !(cR q)))) :
    ‖pairedPartitionCorrelation component₁ component₂
      (indexedRationalAmplitude g D₁ T₁ XL₁ XR₁ c₁)
      (indexedRationalAmplitude g D₂ T₂ XL₂ XR₂ c₂)‖ ^ 2 ≤
      (3 : ℝ) ^ (2 ^ (n + 2)) * ((2 : ℝ) ^ (2 ^ n - 1) * (quartetLocalMeanError p ε *
        (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4) ^ (2 ^ n - 1))) := by
  obtain ⟨cycle, hcycle⟩ := pairedRationalTree_projection hp g hg henergy n
    component₁ component₂ pivot₁ pivot₂ hc D₁ D₂ T₁ T₂ XL₁ XR₁ XL₂ XR₂ c₁ c₂
  obtain ⟨choice, δ, _, hsign, i, hi⟩ := cycle.quartet_coordinates n
  have hmean := projectedTree_mean_le g hg henergy ε hε hflat D₁ n T₁ XL₁ XR₁ c₁
    cL cR hconj choice cycle.sign δ hsign i hi
  have hindexed :
      (∑ m : TreeLeafIndex (n + 2) → (ZMod p)ˣ,
        ‖cycleAverage cycle.sign (indexedRationalAmplitude g D₁ T₁ XL₁ XR₁ c₁) m‖ ^ 2) /
        (Fintype.card (TreeLeafIndex (n + 2) → (ZMod p)ˣ) : ℝ) ≤
      (2 : ℝ) ^ (2 ^ n - 1) * (quartetLocalMeanError p ε *
        (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4) ^ (2 ^ n - 1)) := by
    rw [← (treeLeafTupleEquiv (ZMod p)ˣ (n + 2)).sum_comp
      (fun m => ‖cycleAverage cycle.sign (indexedRationalAmplitude g D₁ T₁ XL₁ XR₁ c₁) m‖ ^ 2),
      ← Fintype.card_congr (treeLeafTupleEquiv (ZMod p)ˣ (n + 2))]
    exact hmean
  exact hcycle.trans (mul_le_mul_of_nonneg_left hindexed (by positivity))

end Ostmann

end OAI
