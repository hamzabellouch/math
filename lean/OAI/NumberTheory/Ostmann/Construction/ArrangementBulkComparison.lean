import OAI.NumberTheory.Ostmann.Construction.ArrangementUniformLaw
import OAI.NumberTheory.Ostmann.Tree.ArrangementTreeComparison
import OAI.NumberTheory.Ostmann.Construction.FiniteEnumeration

namespace OAI

/-! # The quartet estimate for the original independent bulk-slot residues -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem arrangement_tree_bulk_comparison {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hflat : MixedFourierBound g ε)
    (n m : ℕ) (hm : 0 < m)
    (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (D₁ D₂ : (ZMod p)ˣ) {K₁ K₂ : (ZMod p)ˣ}
    (T₁ : RationalTreeData (ZMod p)ˣ (n + 2) K₁)
    (T₂ : RationalTreeData (ZMod p)ˣ (n + 2) K₂)
    (XL₁ XR₁ XL₂ XR₂ : (ZMod p)ˣ) (c₁ c₂ : TreeLeafTuple Bool (n + 2))
    (cL cR : TreeLeafIndex n → Bool)
    (hconj : ∀ q, quartetBlockEquiv Bool n c₁ q = ((cL q, !(cL q)), (cR q, !(cR q)))) :
    ‖bulkPairCorrelation e
      (indexedRationalAmplitude g D₁ T₁ XL₁ XR₁ c₁)
      (indexedRationalAmplitude g D₂ T₂ XL₂ XR₂ c₂)‖ ^ 2 ≤
      (3 : ℝ) ^ (2 ^ (n + 2)) * ((2 : ℝ) ^ (2 ^ n - 1) * (quartetLocalMeanError p ε *
        (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4) ^ (2 ^ n - 1))) := by
  apply arrangement_uniform_norm_sq_le hm e
  simpa only [pairedPartitionCorrelation_fintype] using
    (arrangement_tree_comparison hp g hg henergy ε hε hflat n m hm e hgood
      D₁ D₂ T₁ T₂ XL₁ XR₁ XL₂ XR₂ c₁ c₂ cL cR hconj)

end Ostmann

end OAI
