import OAI.NumberTheory.Ostmann.Characters.QuartetFullCoordinates
import OAI.NumberTheory.Ostmann.Characters.QuartetCutConjugations

namespace OAI

/-! # Conditional projected norm bound on the actual tree cut -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance projectedCutCharFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance projectedCutCharDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

theorem projectedTree_valid_cut_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafIndex n → (ZMod p)ˣ)
    (S : TreeLeafTuple (RationalQuartetState p) n)
    (hS : rationalQuartetStates n T XL XR c ((treeLeafTupleEquiv _ n).symm P) = some S)
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
      ∑ ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ,
        if (∏ q : TreeLeafIndex n, (ρ q) ^ δ q) = 1 then
          ∏ q : TreeLeafIndex n, quartetMovingMajorant g (cL q) (cR q) (choice q) (ρ q)
            (rationalQuartetStateArgument D (treeLeafTupleEquiv _ n S q) (P q)) else 0 := by
  rw [mean_fullQuartetFiberCoordinates n choice P]
  simp_rw [cycleAverage_fullCoordinates g D n T XL XR c P S hS choice sign δ hs]
  apply quartetStateProduct_projection_le g D (treeLeafTupleEquiv _ n S) P cL cR
  intro q
  rw [rationalQuartetStates_conjugations_at n T XL XR c _ S hS q]
  exact hc q

end Ostmann

end OAI
