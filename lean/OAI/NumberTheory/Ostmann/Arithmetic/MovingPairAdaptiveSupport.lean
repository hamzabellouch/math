import OAI.NumberTheory.Ostmann.Tree.PairedFrequencyProjection
import OAI.NumberTheory.Ostmann.Arithmetic.VariableModulusSupport

namespace OAI

/-! # Paired adaptive data from the original two moving histories -/

namespace Ostmann
open scoped Classical

noncomputable def movingPairAdaptiveData {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ s ∈ S, s.natAbs ∣ R)
    (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n)
    (XL XR : ℕ) : (ZMod (R ^ (n + 2)))ˣ → List (ZMod (R ^ (n + 2)))ˣ →
      Option (ArithmeticSplitData (R ^ (n + 2)) × ArithmeticSplitData (R ^ (n + 2))) :=
  let D := fun b => movingSampleAncestorScheme value S n
    (frequencyPairProjection S n b t) (small b) (a b) XL XR
  let hs := fun (b : Bool) (i : Fin (2 ^ n - 1)) => hS _ (singleTreeNodeFrequencies_root_mem S n
    (frequencyPairProjection S n b t) i.val i.isLt)
  let hsr := fun (b : Bool) (i : Fin (2 ^ n - 1)) => hR _ (singleTreeNodeFrequencies_root_mem S n
    (frequencyPairProjection S n b t) i.val i.isLt)
  compensatedPairData n R n (D false) (D true)
    (movingSampleCompensation value n (small false) (a false))
    (movingSampleCompensation value n (small true) (a true))
    (hs false) (hs true) (hsr false) (hsr true)

theorem movingPairAdaptiveData_frequencies {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ s ∈ S, s.natAbs ∣ R)
    (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n)
    (XL XR : ℕ) (total : (ZMod (R ^ (n + 2)))ˣ) (past : List (ZMod (R ^ (n + 2)))ˣ)
    (d e : ArithmeticSplitData (R ^ (n + 2)))
    (hde : movingPairAdaptiveData value S n R t hS hR small a XL XR total past = some (d, e)) :
    d.hasFrequencies (treeNodeFrequencies S n t past.length).1 ∧
      e.hasFrequencies (treeNodeFrequencies S n t past.length).2 := by
  by_cases hj : past.length < 2 ^ n - 1
  · have h := compensatedPairData_frequencies n R n
      (movingSampleAncestorScheme value S n (frequencyPairProjection S n false t)
        (small false) (a false) XL XR)
      (movingSampleAncestorScheme value S n (frequencyPairProjection S n true t)
        (small true) (a true) XL XR)
      (movingSampleCompensation value n (small false) (a false))
      (movingSampleCompensation value n (small true) (a true))
      _ _ _ _ total past hj d e hde
    simpa only [movingSampleAncestorScheme, forwardTreeAncestorScheme, treeAncestorScheme,
      treeNodeFrequencies_projection, Bool.false_eq_true, ite_false, ite_true] using h
  · simp only [movingPairAdaptiveData, compensatedPairData, compensatedAdaptiveData,
      hj, dite_false, pairArithmeticData] at hde
    cases hde

/-- Each nonzero original weight forces its own tests; both use precisely
the same bulk tuple. Their paired support is consequently one. -/
theorem movingPairAdaptiveData_actual_support {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → MovingSlotState σ → ℤ → ℂ)
    (E : Bool → MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (S : Finset ℤ) (n R : ℕ) [NeZero (R ^ (n + 2))] (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ s ∈ S, s.natAbs ∣ R)
    (small : Bool → TreeLeafTuple (List σ) n) (bulk : TreeLeafTuple (List σ) n)
    (a : Bool → MovingSampleSlots σ n) (XL XR : ℕ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) (R : ℤ))
    (y : TreeLeafTuple (ZMod (R ^ (n + 2)))ˣ n)
    (hy : treeIntegerResidues (R ^ (n + 2)) n
      (treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n bulk)) y)
    (hw : ∀ b, recursiveTransferWeight (movingSlotSystem value childBound pivotBound) (F b)
      (movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside (E b))) n
      ⟨n, buildMovingSlotData n (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
        (small b) bulk (a b), XL, XR⟩
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)) ≠ 0) :
    arithmeticLeafSupport n
      (movingPairAdaptiveData value S n R t hS hR small a XL XR) y = 1 := by
  change arithmeticLeafSupport n
    (fun total past => pairArithmeticData
      (compensatedAdaptiveData n R n
        (movingSampleAncestorScheme value S n (frequencyPairProjection S n false t)
          (small false) (a false) XL XR)
        (movingSampleCompensation value n (small false) (a false)) _ _ total past)
      (compensatedAdaptiveData n R n
        (movingSampleAncestorScheme value S n (frequencyPairProjection S n true t)
          (small true) (a true) XL XR)
        (movingSampleCompensation value n (small true) (a true)) _ _ total past)) y = 1
  rw [arithmeticLeafSupport_pair,
    movingSample_adaptive_support value outside childBound pivotBound (F false) (E false)
      S n R (frequencyPairProjection S n false t) (fun s hs => ⟨hS s hs, hR s hs⟩)
      (small false) bulk (a false) XL XR hsmall y hy (hw false),
    movingSample_adaptive_support value outside childBound pivotBound (F true) (E true)
      S n R (frequencyPairProjection S n true t) (fun s hs => ⟨hS s hs, hR s hs⟩)
      (small true) bulk (a true) XL XR hsmall y hy (hw true), one_mul]

end Ostmann

end OAI
