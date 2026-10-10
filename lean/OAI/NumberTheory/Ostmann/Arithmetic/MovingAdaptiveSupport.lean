import OAI.NumberTheory.Ostmann.Arithmetic.MovingNodeUnits
import OAI.NumberTheory.Ostmann.Construction.CompensatedAdaptiveSupport
import OAI.NumberTheory.Ostmann.Arithmetic.ForwardHistorySupport

namespace OAI

/-! # Constructed adaptive support for the original moving-giant sampler -/

namespace Ostmann
open scoped Classical

noncomputable def movingSampledPivotHistory {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (n Q : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (XL XR : ℕ)
    (y : TreeLeafTuple (ZMod Q)ˣ n)
    (hy : treeIntegerResidues Q n
      (treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n bulk)) y) :
    SampledPivotHistory n Q where
  bulk := treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n bulk)
  residue := y
  pivots := movingGiantArray value childBound pivotBound n
    ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t
  compatible := hy

theorem movingSampledPivotHistory_valid {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (S : Finset ℤ) (n Q : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (XL XR : ℕ)
    (y : TreeLeafTuple (ZMod Q)ˣ n)
    (hy : treeIntegerResidues Q n
      (treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n bulk)) y)
    (hsmall : ∀ i s, s ∈ S → IsCoprime (value i : ℤ) s)
    (hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E)) n
      ⟨n, buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a, XL, XR⟩
      (frequencyTreeMap Subtype.val n t) ≠ 0) :
    (movingSampledPivotHistory value childBound pivotBound n Q
      (frequencyTreeMap Subtype.val n t) small bulk a XL XR y hy).compensatedValid
        (movingSampleAncestorScheme value S n t small a XL XR)
        (movingSampleCompensation value n small a) := by
  exact ⟨movingSample_compensatedEquations value childBound pivotBound F
    (movingGuardedExtra value outside E) S n t small bulk a XL XR hw,
    movingSample_coefficient_units value outside childBound pivotBound F E S n t
      small bulk a XL XR hsmall hw⟩

theorem movingFrameConstants_compensation_coprime {σ : Type*} (value : σ → ℕ)
    (R : ℤ) (hsmall : ∀ i, IsCoprime (value i : ℤ) R) (n : ℕ)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (path : List Bool) :
    IsCoprime ((movingFrameConstants value n small a path).compensation : ℤ) R := by
  induction n generalizing path with
  | zero =>
    cases a
    change IsCoprime (1 : ℤ) R
    exact isCoprime_one_left
  | succ n ih =>
    cases a with
    | node a l r =>
      cases path with
      | nil => exact movingNaturalProduct_coprime value _ R (fun i _ => hsmall i)
      | cons b path => cases b <;> apply ih

/-- The prefix tests are built from actual samples and are passed by every
nonzero original history. There is no assumed adaptive-support event. -/
theorem movingSample_adaptive_support {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (S : Finset ℤ) (n R : ℕ) [NeZero (R ^ (n + 2))] (t : FrequencyTree S n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ∣ R)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (XL XR : ℕ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) (R : ℤ))
    (y : TreeLeafTuple (ZMod (R ^ (n + 2)))ˣ n)
    (hy : treeIntegerResidues (R ^ (n + 2)) n
      (treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n bulk)) y)
    (hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E)) n
      ⟨n, buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a, XL, XR⟩
      (frequencyTreeMap Subtype.val n t) ≠ 0) :
    let D := movingSampleAncestorScheme value S n t small a XL XR
    let hs : ∀ i, (D.frequencies i).root ≠ 0 :=
      fun i => (hS _ (singleTreeNodeFrequencies_root_mem S n t i.val i.isLt)).1
    let hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R :=
      fun i => (hS _ (singleTreeNodeFrequencies_root_mem S n t i.val i.isLt)).2
    singleArithmeticLeafSupport n
      (compensatedAdaptiveData n R n D (movingSampleCompensation value n small a) hs hsR) y = 1 := by
  dsimp only
  let hist := movingSampledPivotHistory value childBound pivotBound n (R ^ (n + 2))
    (frequencyTreeMap Subtype.val n t) small bulk a XL XR y hy
  have hs : ∀ i s, s ∈ S → IsCoprime (value i : ℤ) s := by
    intro i s hmem
    exact (hsmall i).of_isCoprime_of_dvd_right
      (Int.natAbs_dvd.mp (Int.natCast_dvd_natCast.mpr (hS s hmem).2))
  apply compensatedAdaptiveData_actual_support n R n
    (movingSampleAncestorScheme value S n t small a XL XR)
    (movingSampleCompensation value n small a)
    (fun i => movingFrameConstants_compensation_coprime value R hsmall n small a _)
    (fun i => (preorderNodePath_length n i).le)
    (fun i => (hS _ (singleTreeNodeFrequencies_root_mem S n t i.val i.isLt)).1)
    (fun i => (hS _ (singleTreeNodeFrequencies_root_mem S n t i.val i.isLt)).2)
    hist
  exact movingSampledPivotHistory_valid value outside childBound pivotBound F E S n _ t
    small bulk a XL XR y hy hs hw

end Ostmann

end OAI
