import OAI.NumberTheory.Ostmann.Characters.QuartetProjectedCut
import OAI.NumberTheory.Ostmann.Characters.QuartetHorizontalMean

namespace OAI

/-! # Projected cut bounds with invalid ancestors included -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance cutAverageCharFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance cutAverageCharDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

theorem treeLeafTupleEquiv_zip {A B : Type*} (n : ℕ)
    (a : TreeLeafTuple A n) (b : TreeLeafTuple B n) (i : TreeLeafIndex n) :
    treeLeafTupleEquiv (A × B) n (treeLeafZip n a b) i =
      (treeLeafTupleEquiv A n a i, treeLeafTupleEquiv B n b i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases i with
    | inl i => exact ih a.1 b.1 i
    | inr i => exact ih a.2 b.2 i

theorem rationalCutCharacterSum_of_valid {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafIndex n → (ZMod p)ˣ)
    (S : TreeLeafTuple (RationalQuartetState p) n)
    (hS : rationalQuartetStates n T XL XR c ((treeLeafTupleEquiv _ n).symm P) = some S)
    (B : TreeLeafIndex n → MulChar (ZMod p) ℂ → ZMod p → ℝ) (δ : TreeLeafIndex n → ℤ) :
    rationalCutCharacterSum D n T XL XR c B δ ((treeLeafTupleEquiv _ n).symm P) =
      ∑ ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ,
        if (∏ q : TreeLeafIndex n, (ρ q) ^ δ q) = 1 then
          ∏ q : TreeLeafIndex n, B q (ρ q)
            (rationalQuartetStateArgument D (treeLeafTupleEquiv _ n S q) (P q)) else 0 := by
  unfold rationalCutCharacterSum
  simp only [hS, quartetCutValue, treeLeafZipProduct_eq_prod, treeLeafTupleEquiv_zip,
    Equiv.apply_symm_apply]

theorem rationalTreeAmplitude_zero_of_cut {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafIndex n → (ZMod p)ˣ)
    (hS : rationalQuartetStates n T XL XR c ((treeLeafTupleEquiv _ n).symm P) = none)
    (m : QuartetProductFiber (ZMod p)ˣ n P) :
    rationalTreeAmplitude g D T XL XR c m.1 = 0 := by
  have hP : treeLeafMap (treeLeafProduct 2) n (quartetBlockTupleEquiv (ZMod p)ˣ n m.1) =
      (treeLeafTupleEquiv _ n).symm P := by
    apply (treeLeafTupleEquiv _ n).injective
    rw [Equiv.apply_symm_apply, ← quartetProducts_eq_map]
    exact m.property
  rw [rationalTreeAmplitude_cut, hP, hS]
  rfl

theorem projectedTree_cut_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafIndex n → (ZMod p)ˣ)
    (cL cR : TreeLeafIndex n → Bool)
    (hc : ∀ q, quartetBlockEquiv Bool n c q = ((cL q, !(cL q)), (cR q, !(cR q))))
    (choice : TreeLeafIndex n → QuartetMovingCase)
    (sign : TreeLeafIndex (n + 2) → ℤ) (δ : TreeLeafIndex n → ℤ)
    (hs : ∀ q j, sign (quartetLeafIndex n q j) =
      treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ q * s) 2 (quartetMovingSign (choice q))) j) :
    (Fintype.card (QuartetProductFiber (ZMod p)ˣ n P) : ℝ)⁻¹ *
      (∑ m : QuartetProductFiber (ZMod p)ˣ n P,
        ‖cycleAverage sign (indexedRationalAmplitude g D T XL XR c)
          (treeLeafTupleEquiv _ (n + 2) m.1)‖ ^ 2) ≤
      rationalCutCharacterSum D n T XL XR c
        (fun q => quartetMovingMajorant g (cL q) (cR q) (choice q)) δ
        ((treeLeafTupleEquiv _ n).symm P) := by
  cases hS : rationalQuartetStates n T XL XR c ((treeLeafTupleEquiv _ n).symm P) with
  | some S =>
    rw [rationalCutCharacterSum_of_valid D n T XL XR c P S hS]
    exact projectedTree_valid_cut_le g D n T XL XR c P S hS cL cR hc choice sign δ hs
  | none =>
    have hz (h : TreeLeafIndex n → (ZMod p)ˣ × (ZMod p)ˣ) (r : TreeLeafIndex n → (ZMod p)ˣ) :
        cycleAverage sign (indexedRationalAmplitude g D T XL XR c)
          (treeLeafTupleEquiv _ (n + 2) ((fullQuartetFiberCoordinates n choice P).symm (h, r)).1) = 0 := by
      unfold cycleAverage
      have hterm (z : (ZMod p)ˣ) :
          indexedRationalAmplitude g D T XL XR c
            (cycleMultiply sign z (treeLeafTupleEquiv _ (n + 2)
              ((fullQuartetFiberCoordinates n choice P).symm (h, r)).1)) = 0 := by
        rw [fullQuartetFiberCoordinates_action n choice P sign δ hs]
        simp only [indexedRationalAmplitude, Equiv.symm_apply_apply]
        exact rationalTreeAmplitude_zero_of_cut g D n T XL XR c P hS _
      simp only [hterm, Finset.sum_const_zero, mul_zero]
    rw [mean_fullQuartetFiberCoordinates n choice P]
    simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, mul_zero]
    unfold rationalCutCharacterSum
    simp only [hS, quartetCutValue, ite_self, Finset.sum_const_zero, le_refl]

end Ostmann

end OAI
