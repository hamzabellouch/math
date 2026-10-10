import OAI.NumberTheory.Ostmann.Characters.QuartetCutAverages
import OAI.NumberTheory.Ostmann.Characters.QuartetCycleMean

namespace OAI

/-! # Averaging the projected bound over all bottom-quartet products -/

namespace Ostmann

open scoped BigOperators

theorem card_treeLeafTuple_quartet {U : Type*} [CommGroup U] [Fintype U]
    (n : ℕ) (P : TreeLeafIndex n → U) :
    Fintype.card (TreeLeafTuple U (n + 2)) =
      Fintype.card (TreeLeafIndex n → U) * Fintype.card (QuartetProductFiber U n P) := by
  rw [card_treeLeafTuple, Fintype.card_fun, card_treeLeafIndex, card_quartetProductFiber,
    ← mul_pow, ← pow_succ', ← pow_mul]
  congr 1
  rw [pow_add]
  norm_num
  omega

theorem mean_treeLeafTuple_by_quartetProducts {U : Type*} [CommGroup U] [Fintype U]
    (n : ℕ) (f : TreeLeafTuple U (n + 2) → ℝ) :
    (∑ m : TreeLeafTuple U (n + 2), f m) /
      (Fintype.card (TreeLeafTuple U (n + 2)) : ℝ) =
      (∑ P : TreeLeafIndex n → U, (Fintype.card (QuartetProductFiber U n P) : ℝ)⁻¹ *
        ∑ m : QuartetProductFiber U n P, f m.1) / (Fintype.card (TreeLeafIndex n → U) : ℝ) := by
  rw [sum_treeLeafTuple_by_quartetProducts]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro P _
  rw [card_treeLeafTuple_quartet n P, Nat.cast_mul]
  simp only [div_eq_mul_inv, mul_inv_rev, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem projectedTree_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hflat : MixedFourierBound g ε)
    (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (cL cR : TreeLeafIndex n → Bool)
    (hc : ∀ q, quartetBlockEquiv Bool n c q = ((cL q, !(cL q)), (cR q, !(cR q))))
    (choice : TreeLeafIndex n → QuartetMovingCase)
    (sign : TreeLeafIndex (n + 2) → ℤ) (δ : TreeLeafIndex n → ℤ)
    (hs : ∀ q j, sign (quartetLeafIndex n q j) =
      treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ q * s) 2 (quartetMovingSign (choice q))) j)
    (i : TreeLeafIndex n) (hi : δ i = 1 ∨ δ i = -1) :
    (∑ m : TreeLeafTuple (ZMod p)ˣ (n + 2),
      ‖cycleAverage sign (indexedRationalAmplitude g D T XL XR c)
        (treeLeafTupleEquiv _ (n + 2) m)‖ ^ 2) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ (n + 2)) : ℝ) ≤
      (2 : ℝ) ^ (2 ^ n - 1) * (quartetLocalMeanError p ε *
        (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4) ^ (2 ^ n - 1)) := by
  rw [mean_treeLeafTuple_by_quartetProducts]
  let B := fun q => quartetMovingMajorant g (cL q) (cR q) (choice q)
  calc
    _ ≤ (∑ P : TreeLeafIndex n → (ZMod p)ˣ,
        rationalCutCharacterSum D n T XL XR c B δ ((treeLeafTupleEquiv _ n).symm P)) /
        (Fintype.card (TreeLeafIndex n → (ZMod p)ˣ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun P _ => projectedTree_cut_le g D n T XL XR c P cL cR hc choice sign δ hs
    _ = (∑ P : TreeLeafTuple (ZMod p)ˣ n, rationalCutCharacterSum D n T XL XR c B δ P) /
        (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) := by
      rw [(treeLeafTupleEquiv (ZMod p)ˣ n).symm.sum_comp,
        ← Fintype.card_congr (treeLeafTupleEquiv (ZMod p)ˣ n)]
    _ ≤ _ := rationalCutCharacterSum_mean_le D n T XL XR c B δ i hi
      (quartetLocalMeanError p ε) _ (quartetLocalMeanError_nonneg p ε)
      (fun q ρ y => quartetMovingMajorant_nonneg g (cL q) (cR q) (choice q) ρ y)
      (fun ρ => quartetMovingMajorant_mean_le g hg henergy ε hε hflat (cL i) (cR i) (choice i) ρ)
      (fun q => quartetMovingMajorant_total_mean_le g hg henergy (cL q) (cR q) (choice q))

end Ostmann

end OAI
