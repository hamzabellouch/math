import OAI.NumberTheory.Ostmann.Tree.RationalQuartetCut

namespace OAI

/-! # Indexed products and means at a horizontal tree level -/

namespace Ostmann

open scoped BigOperators

theorem treeLeafTupleEquiv_map {A B : Type*} (f : A → B) (n : ℕ)
    (a : TreeLeafTuple A n) (i : TreeLeafIndex n) :
    treeLeafTupleEquiv B n (treeLeafMap f n a) i = f (treeLeafTupleEquiv A n a i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases i with
    | inl i => exact ih a.1 i
    | inr i => exact ih a.2 i

theorem treeLeafZipProduct_eq_prod {A B R : Type*} [CommMonoid R]
    (f : A → B → R) (n : ℕ) (a : TreeLeafTuple A n) (b : TreeLeafTuple B n) :
    treeLeafZipProduct f n a b =
      ∏ i : TreeLeafIndex n, f (treeLeafTupleEquiv A n a i) (treeLeafTupleEquiv B n b i) := by
  induction n with
  | zero =>
    change f a b = ∏ _ : Unit, f a b
    simp
  | succ n ih =>
    change treeLeafZipProduct f n a.1 b.1 * treeLeafZipProduct f n a.2 b.2 =
      ∏ i : TreeLeafIndex n ⊕ TreeLeafIndex n,
        f (treeLeafTupleEquiv A (n + 1) a i) (treeLeafTupleEquiv B (n + 1) b i)
    rw [Fintype.prod_sum_type, ih, ih]
    rfl

theorem treeWeightsNonneg_iff {p : ℕ} (n : ℕ)
    (w : TreeLeafTuple (ZMod p → ℝ) n) :
    treeWeightsNonneg n w ↔ ∀ i : TreeLeafIndex n, ∀ x, 0 ≤ treeLeafTupleEquiv _ n w i x := by
  induction n with
  | zero =>
    constructor
    · intro h _ x; exact h x
    · intro h x; exact h () x
  | succ n ih =>
    constructor
    · intro h i x
      cases i with
      | inl i => exact (ih w.1).mp h.1 i x
      | inr i => exact (ih w.2).mp h.2 i x
    · intro h
      exact ⟨(ih w.1).mpr (fun i x => h (.inl i) x),
        (ih w.2).mpr (fun i x => h (.inr i) x)⟩

theorem treeProfileMean_eq_prod {p : ℕ} [Fact p.Prime] (n : ℕ)
    (w : TreeLeafTuple (ZMod p → ℝ) n) :
    treeProfileMean n w = ∏ i : TreeLeafIndex n,
      (∑ x : (ZMod p)ˣ, treeLeafTupleEquiv _ n w i x) / (Fintype.card (ZMod p)ˣ : ℝ) := by
  induction n with
  | zero =>
    change (∑ x : (ZMod p)ˣ, w x) / (Fintype.card (ZMod p)ˣ : ℝ) =
      ∏ _ : Unit, (∑ x : (ZMod p)ˣ, w x) / (Fintype.card (ZMod p)ˣ : ℝ)
    simp
  | succ n ih =>
    change treeProfileMean n w.1 * treeProfileMean n w.2 =
      ∏ i : TreeLeafIndex n ⊕ TreeLeafIndex n,
        (∑ x : (ZMod p)ˣ, treeLeafTupleEquiv _ (n + 1) w i x) /
          (Fintype.card (ZMod p)ˣ : ℝ)
    rw [Fintype.prod_sum_type, ih, ih]
    rfl

theorem quartetProducts_eq_map {U : Type*} [CommGroup U] (n : ℕ)
    (m : TreeLeafTuple U (n + 2)) :
    quartetProducts n m = treeLeafTupleEquiv U n
      (treeLeafMap (treeLeafProduct 2) n (quartetBlockTupleEquiv U n m)) := by
  funext i
  exact (treeLeafTupleEquiv_map (treeLeafProduct 2) n (quartetBlockTupleEquiv U n m) i).symm

theorem rationalTreeAmplitude_product_of_cut {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafIndex n → (ZMod p)ˣ)
    (S : TreeLeafTuple (RationalQuartetState p) n)
    (hS : rationalQuartetStates n T XL XR c ((treeLeafTupleEquiv _ n).symm P) = some S)
    (m : QuartetProductFiber (ZMod p)ˣ n P) :
    rationalTreeAmplitude g D T XL XR c m.1 = ∏ i : TreeLeafIndex n,
      rationalQuartetStateAmplitude g D (treeLeafTupleEquiv _ n S i)
        (quartetBlockEquiv (ZMod p)ˣ n m.1 i) := by
  have hP : treeLeafMap (treeLeafProduct 2) n (quartetBlockTupleEquiv (ZMod p)ˣ n m.1) =
      (treeLeafTupleEquiv _ n).symm P := by
    apply (treeLeafTupleEquiv _ n).injective
    rw [Equiv.apply_symm_apply, ← quartetProducts_eq_map]
    exact m.property
  rw [rationalTreeAmplitude_cut, hP, hS]
  exact treeLeafZipProduct_eq_prod _ n S _

/-- On any fixed valid cut, the conditional second moment factors into
the exact independent quartet second moments. -/
theorem rationalTreeAmplitude_cut_secondMoment {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafIndex n → (ZMod p)ˣ)
    (S : TreeLeafTuple (RationalQuartetState p) n)
    (hS : rationalQuartetStates n T XL XR c ((treeLeafTupleEquiv _ n).symm P) = some S) :
    (Fintype.card (QuartetProductFiber (ZMod p)ˣ n P) : ℝ)⁻¹ *
      (∑ m : QuartetProductFiber (ZMod p)ˣ n P,
        ‖rationalTreeAmplitude g D T XL XR c m.1‖ ^ 2) =
      ∏ i : TreeLeafIndex n, (Fintype.card (TreeLeafFiber (ZMod p)ˣ 2 (P i)) : ℝ)⁻¹ *
        ∑ m : TreeLeafFiber (ZMod p)ˣ 2 (P i),
          ‖rationalQuartetStateAmplitude g D (treeLeafTupleEquiv _ n S i) m.1‖ ^ 2 := by
  simp only [rationalTreeAmplitude_product_of_cut g D n T XL XR c P S hS,
    norm_prod, ← Finset.prod_pow]
  exact average_quartetProductFiber_product n P
    (fun i m => ‖rationalQuartetStateAmplitude g D (treeLeafTupleEquiv _ n S i) m‖ ^ 2)

end Ostmann

end OAI
