import OAI.NumberTheory.Ostmann.Arithmetic.MovingNodeDivisibility
import OAI.NumberTheory.Ostmann.Construction.ScheduledNodeFrequencies
import OAI.NumberTheory.Ostmann.Construction.CompensatedAdaptiveCoefficients

namespace OAI

namespace Ostmann
open scoped Classical

noncomputable def movingSampleAncestorScheme {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (XL XR : ℕ) :
    PivotDependencyScheme (2 ^ n - 1) :=
  forwardTreeAncestorScheme S n t XL XR
    (fun path => (movingFrameConstants value n small a path).leftSmall)
    (fun path => (movingFrameConstants value n small a path).rightSmall)

def movingSampleCompensation {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n)
    (j : Fin (2 ^ n - 1)) : ℤ :=
  (movingFrameConstants value n small a (preorderNodePath n j)).compensation

theorem movingSampleNode_products {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n)
    (XL XR : ℕ) (j : Fin (2 ^ n - 1)) :
    let tz := frequencyTreeMap Subtype.val n t
    let x : MovingSlotState σ := ⟨n, buildMovingSlotData n tz small bulk a, XL, XR⟩
    let p := movingGiantArray value childBound pivotBound n x tz
    let D := movingSampleAncestorScheme value S n t small a XL XR
    let z := transferNodeArray (movingSlotSystem value childBound pivotBound) n x tz j
    let b := (actualChildProducts n (treeLeafMap (fun q : ℕ => (q : ℤ)) n
      (movingSlotValues value n bulk))).getD j.val (1, 1)
    (z.state.compensation value : ℤ) = movingSampleCompensation value n small a j ∧
      (z.state.leftProduct value : ℤ) = D.rightCoefficient p j * b.1 ∧
      (z.state.rightProduct value : ℤ) = D.leftCoefficient p j * b.2 := by
  dsimp only
  let tz := frequencyTreeMap Subtype.val n t
  let T := buildMovingSlotData n tz small bulk a
  let x : MovingSlotState σ := ⟨n, T, XL, XR⟩
  let z := transferNodeArray (movingSlotSystem value childBound pivotBound) n x tz j
  let p := movingGiantArray value childBound pivotBound n x tz
  have hf := movingNodeAtPath_products value childBound pivotBound n tz small bulk a XL XR
    (preorderNodePath n j) (preorderNodePath_length n j)
  rw [← transferNodeArray_path] at hf
  have hg := movingGiantArray_sources value childBound pivotBound n T tz XL XR j
  have hb := movingBulkProducts_preorder_intCast value n bulk j
  have hl := congrArg Prod.fst hg
  have hr := congrArg Prod.snd hg
  have hbl := congrArg Prod.fst hb
  have hbr := congrArg Prod.snd hb
  dsimp only at hl hr hbl hbr
  refine ⟨congrArg (fun q : ℕ => (q : ℤ)) hf.1, ?_, ?_⟩
  · change (z.state.leftProduct value : ℤ) = _
    rw [hf.2.1, Nat.cast_mul, Nat.cast_mul]
    change _ = (forwardTreeAncestorScheme S n t XL XR _ _).rightCoefficient p j * _
    rw [forwardTreeAncestorScheme_right, ← hl, ← hbl]
    ring
  · change (z.state.rightProduct value : ℤ) = _
    rw [hf.2.2, Nat.cast_mul, Nat.cast_mul]
    change _ = (forwardTreeAncestorScheme S n t XL XR _ _).leftCoefficient p j * _
    rw [forwardTreeAncestorScheme_left, ← hr, ← hbr]
    ring

/-- No node equation is assumed here: all are forced by a nonzero original
recursive coefficient and its compensation cutoff. -/
theorem movingSample_compensatedEquations {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (XL XR : ℕ)
    (hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound E) n
      ⟨n, buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a, XL, XR⟩
      (frequencyTreeMap Subtype.val n t) ≠ 0) :
    let tz := frequencyTreeMap Subtype.val n t
    let x : MovingSlotState σ := ⟨n, buildMovingSlotData n tz small bulk a, XL, XR⟩
    let b := actualChildProducts n (treeLeafMap (fun q : ℕ => (q : ℤ)) n
      (movingSlotValues value n bulk))
    (movingSampleAncestorScheme value S n t small a XL XR).compensatedEquations
      (movingSampleCompensation value n small a)
      (fun j => (b.getD j.val (1, 1)).1) (fun j => (b.getD j.val (1, 1)).2)
      (movingGiantArray value childBound pivotBound n x tz) := by
  dsimp only
  intro j
  let sys := movingSlotSystem value childBound pivotBound
  let tz := frequencyTreeMap Subtype.val n t
  let x : MovingSlotState σ := ⟨n, buildMovingSlotData n tz small bulk a, XL, XR⟩
  let z := transferNodeArray sys n x tz j
  have hv := recursiveTransferWeight_nonzero_valid sys F
    (movingSlotCutoff value childBound pivotBound E) n x tz hw
  have hz := transferNodeArray_valid sys n x tz hv j
  have hd := movingSlotWeight_node_divisible value childBound pivotBound F E n x tz hw j
  have hf := transferNodeArray_frequencies sys S n x t j
  have hp := movingSampleNode_products value childBound pivotBound S n t small bulk a XL XR j
  have he : (z.pivot sys : ℤ) = (z.state.compensation value : ℤ) *
      movingGiantArray value childBound pivotBound n x tz j := by
    dsimp only [movingGiantArray, movingNodeGiant]
    exact_mod_cast (Nat.mul_div_cancel' hd.2).symm
  have hroot := congrArg NodeFrequencies.root hf
  have hleft := congrArg NodeFrequencies.left hf
  have hright := congrArg NodeFrequencies.right hf
  have h := hz.relation
  change z.left * (z.state.rightProduct value : ℤ) -
    z.right * (z.state.leftProduct value : ℤ) = z.root * (z.pivot sys : ℤ) at h
  dsimp only [ReconstructedTransferNode.frequencies] at hroot hleft hright
  rw [he, hp.1, hp.2.1, hp.2.2, hroot, hleft, hright] at h
  simpa only [movingSampleAncestorScheme, forwardTreeAncestorScheme, treeAncestorScheme,
    mul_assoc] using h

end Ostmann

end OAI
