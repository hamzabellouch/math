import OAI.NumberTheory.Ostmann.Characters.QuartetProductCoordinates
import OAI.NumberTheory.Ostmann.Characters.QuartetCycleCoordinates
import OAI.NumberTheory.Ostmann.Characters.QuartetProductProjection

namespace OAI

/-! # The full tree in held and moving quartet coordinates -/

namespace Ostmann

open scoped BigOperators

noncomputable def fullQuartetFiberCoordinates {U : Type*} [CommGroup U] (n : ℕ)
    (choice : TreeLeafIndex n → QuartetMovingCase) (P : TreeLeafIndex n → U) :
    QuartetProductFiber U n P ≃ (TreeLeafIndex n → U × U) × (TreeLeafIndex n → U) :=
  (quartetProductFiberEquiv n P).trans (quartetProductCoordinates choice P)

theorem fullQuartetFiberCoordinates_block {U : Type*} [CommGroup U] (n : ℕ)
    (choice : TreeLeafIndex n → QuartetMovingCase) (P : TreeLeafIndex n → U)
    (h : TreeLeafIndex n → U × U) (r : TreeLeafIndex n → U) (i : TreeLeafIndex n) :
    quartetBlockEquiv U n ((fullQuartetFiberCoordinates n choice P).symm (h, r)).1 i =
      quartetMovingLeaves (choice i) (P i) (h i).1 (h i).2 (r i) := by
  exact (quartetProductFiberEquiv_symm n P _ i).trans
    (quartetProductCoordinates_symm choice P h r i)

theorem mean_fullQuartetFiberCoordinates {U : Type*} [CommGroup U] [Fintype U]
    (n : ℕ) (choice : TreeLeafIndex n → QuartetMovingCase) (P : TreeLeafIndex n → U)
    (f : QuartetProductFiber U n P → ℝ) :
    (Fintype.card (QuartetProductFiber U n P) : ℝ)⁻¹ * (∑ m, f m) =
      ((Fintype.card (U × U) : ℝ) ^ Fintype.card (TreeLeafIndex n))⁻¹ *
        (∑ h : TreeLeafIndex n → U × U,
          ((Fintype.card U : ℝ) ^ Fintype.card (TreeLeafIndex n))⁻¹ *
            ∑ r : TreeLeafIndex n → U, f ((fullQuartetFiberCoordinates n choice P).symm (h, r))) := by
  have hs := (fullQuartetFiberCoordinates n choice P).symm.bijective.sum_comp f
  rw [← hs, Fintype.sum_prod_type,
    Fintype.card_congr (fullQuartetFiberCoordinates n choice P), Fintype.card_prod]
  simp only [Fintype.card_fun, Nat.cast_mul, Nat.cast_pow, mul_inv_rev, Finset.mul_sum]
  congr 1
  ext h
  congr 1
  ext r
  ring

theorem fullQuartetFiberCoordinates_action {U : Type*} [CommGroup U] (n : ℕ)
    (choice : TreeLeafIndex n → QuartetMovingCase) (P : TreeLeafIndex n → U)
    (sign : TreeLeafIndex (n + 2) → ℤ) (δ : TreeLeafIndex n → ℤ)
    (hs : ∀ q j, sign (quartetLeafIndex n q j) =
      treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ q * s) 2 (quartetMovingSign (choice q))) j)
    (h : TreeLeafIndex n → U × U) (r : TreeLeafIndex n → U) (z : U) :
    cycleMultiply sign z (treeLeafTupleEquiv U (n + 2)
      ((fullQuartetFiberCoordinates n choice P).symm (h, r)).1) =
      treeLeafTupleEquiv U (n + 2)
        ((fullQuartetFiberCoordinates n choice P).symm (h, cycleMultiply δ z r)).1 := by
  funext k
  obtain ⟨q, j, hk⟩ : ∃ q j, quartetLeafIndex n q j = k :=
    ⟨_, _, quartetLeafIndex_coordinates n k⟩
  subst k
  change z ^ sign (quartetLeafIndex n q j) *
      treeLeafTupleEquiv U (n + 2) _ (quartetLeafIndex n q j) = _
  rw [← quartetBlockEquiv_read, ← quartetBlockEquiv_read,
    fullQuartetFiberCoordinates_block, fullQuartetFiberCoordinates_block, hs]
  have he := congrArg (fun m => treeLeafTupleEquiv U 2 m j)
    (quartetMovingLeaves_scaled_sign (choice q) (δ q) (P q) (h q).1 (h q).2 (r q) z)
  rw [treeLeafTupleEquiv_scale] at he
  exact he

theorem rationalTreeAmplitude_fullCoordinates {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafIndex n → (ZMod p)ˣ)
    (S : TreeLeafTuple (RationalQuartetState p) n)
    (hS : rationalQuartetStates n T XL XR c ((treeLeafTupleEquiv _ n).symm P) = some S)
    (choice : TreeLeafIndex n → QuartetMovingCase)
    (h : TreeLeafIndex n → (ZMod p)ˣ × (ZMod p)ˣ) (r : TreeLeafIndex n → (ZMod p)ˣ) :
    rationalTreeAmplitude g D T XL XR c
      ((fullQuartetFiberCoordinates n choice P).symm (h, r)).1 =
      quartetStateProduct g D (treeLeafTupleEquiv _ n S) P choice h r := by
  rw [rationalTreeAmplitude_product_of_cut g D n T XL XR c P S hS]
  unfold quartetStateProduct
  apply Finset.prod_congr rfl
  intro i _
  rw [fullQuartetFiberCoordinates_block]

theorem cycleAverage_fullCoordinates {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafIndex n → (ZMod p)ˣ)
    (S : TreeLeafTuple (RationalQuartetState p) n)
    (hS : rationalQuartetStates n T XL XR c ((treeLeafTupleEquiv _ n).symm P) = some S)
    (choice : TreeLeafIndex n → QuartetMovingCase)
    (sign : TreeLeafIndex (n + 2) → ℤ) (δ : TreeLeafIndex n → ℤ)
    (hs : ∀ q j, sign (quartetLeafIndex n q j) =
      treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ q * s) 2 (quartetMovingSign (choice q))) j)
    (h : TreeLeafIndex n → (ZMod p)ˣ × (ZMod p)ˣ) (r : TreeLeafIndex n → (ZMod p)ˣ) :
    cycleAverage sign (indexedRationalAmplitude g D T XL XR c)
      (treeLeafTupleEquiv _ (n + 2) ((fullQuartetFiberCoordinates n choice P).symm (h, r)).1) =
      cycleAverage δ (quartetStateProduct g D (treeLeafTupleEquiv _ n S) P choice h) r := by
  unfold cycleAverage
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  rw [fullQuartetFiberCoordinates_action n choice P sign δ hs]
  simp only [indexedRationalAmplitude, Equiv.symm_apply_apply]
  exact rationalTreeAmplitude_fullCoordinates g D n T XL XR c P S hS choice h _

end Ostmann

end OAI
