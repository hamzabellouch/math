import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.GroupAssignments
import OAI.LinearAlgebra.MatrixFields.Construction.Subdivision
import OAI.LinearAlgebra.MatrixFields.Extraction.GroupSelection

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open MatrixMultiplication.Foundation AllFieldParameters JointPopulation
open CWStrands HistorySymmetry InheritedMasks JointCanonicalization
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)

abbrev CanonicalWords := CanonicalPairs (activeCounts (K := K) (tick := tick) allocation dilation)
  (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength)

abbrev ProducedWords := ∀ h : Produced K tick,
  Fin (population allocation dilation h.val) → Fin (currentLength h.val.1) → Fin 7

abbrev CanonicalClassPosition :=
  Σ c : Active K tick × JointPopulation.Shape, Fin (activeCounts allocation dilation c.1 c.2)

abbrev CanonicalHalfPosition :=
  CanonicalClassPosition (K := K) (tick := tick) allocation dilation × Bool

def canonicalClassEquiv : CanonicalClassPosition (K := K) (tick := tick) allocation dilation ≃
    (Σ h : Active K tick, Σ u : JointPopulation.Shape, Fin (activeCounts allocation dilation h u)) where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun p := ⟨(p.1, p.2.1), p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def splitArrangeEquiv :
    (Σ h : Active K tick, Σ b : h.val.1.Branch,
      Fin (branchPopulation allocation dilation h.val b)) × Bool ≃
        SplitPositions (K := K) (tick := tick) allocation dilation where
  toFun p := ⟨p.1.1, p.1.2.1, p.2, p.1.2.2⟩
  invFun p := (⟨p.1, p.2.1, p.2.2.2⟩, p.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def canonicalSplitEquiv :
    CanonicalHalfPosition (K := K) (tick := tick) allocation dilation ≃
      SplitPositions (K := K) (tick := tick) allocation dilation :=
  (Equiv.prodCongr
    ((canonicalClassEquiv allocation dilation).trans
      (Equiv.sigmaCongrRight fun h : Active K tick =>
        branchPositionEquiv allocation dilation h.val))
    (Equiv.refl Bool)).trans (splitArrangeEquiv allocation dilation)

def canonicalProducedEquiv :
    CanonicalHalfPosition (K := K) (tick := tick) allocation dilation ≃
      ProducedPositions (K := K) (tick := tick) allocation dilation :=
  (canonicalSplitEquiv allocation dilation).trans
    (producedPositionEquiv allocation dilation).symm

theorem splitProduced_length (p : SplitPositions (K := K) (tick := tick) allocation dilation) :
    currentLength ((producedPositionEquiv allocation dilation).symm p).1.val.1 =
      activeHalfLength p.1 := by
  simpa only [Equiv.apply_symm_apply, activeHalfLength] using
    producedPositionEquiv_length allocation dilation
      ((producedPositionEquiv allocation dilation).symm p)

def splitWord (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (p : SplitPositions (K := K) (tick := tick) allocation dilation) :
    Fin (activeHalfLength p.1) → Fin 7 :=
  let q := (producedPositionEquiv allocation dilation).symm p
  fun i => x q.1 q.2 (Fin.cast (splitProduced_length allocation dilation p).symm i)

def producedHalfWord (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool) :
    Fin (branchPopulation allocation dilation h.val b) → Fin (activeHalfLength h) → Fin 7 :=
  fun i => splitWord allocation dilation x ⟨h, b, right, i⟩

def regroupAt (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (p : CanonicalHalfPosition (K := K) (tick := tick) allocation dilation) :
    Fin (activeHalfLength p.1.1.1) → Fin 7 :=
  splitWord allocation dilation x (canonicalSplitEquiv allocation dilation p)

def regroupWords (x : ProducedWords (K := K) (tick := tick) allocation dilation) :
    CanonicalWords (K := K) (tick := tick) allocation dilation where
  left c i := regroupAt allocation dilation x (⟨c, i⟩, false)
  right c i := regroupAt allocation dilation x (⟨c, i⟩, true)

def branchClassEquiv (h : Active K tick) (b : h.val.1.Branch) :
    Fin (branchPopulation allocation dilation h.val b) ≃
      Fin (activeCounts allocation dilation h (branchShape h.val b)) :=
  { toFun := fun i => ⟨i.val, by
      change i.val < jointCounts allocation dilation h.val (branchShape h.val b)
      rw [jointCounts_at]
      exact i.isLt⟩
    invFun := fun i => ⟨i.val, by
      simpa only [activeCounts, jointCounts_at] using i.isLt⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

def branchClassIndex (h : Active K tick) (b : h.val.1.Branch)
    (i : Fin (branchPopulation allocation dilation h.val b)) :
    Fin (activeCounts allocation dilation h (branchShape h.val b)) :=
  branchClassEquiv allocation dilation h b i

theorem regroupWords_branch (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool)
    (i : Fin (branchPopulation allocation dilation h.val b)) :
    (if right then (regroupWords allocation dilation x).right
      (h, branchShape h.val b) (branchClassIndex allocation dilation h b i)
    else (regroupWords allocation dilation x).left
      (h, branchShape h.val b) (branchClassIndex allocation dilation h b i)) =
        producedHalfWord allocation dilation x h b right i := by
  have he := (branchPositionEquiv allocation dilation h.val).apply_symm_apply ⟨b, i⟩
  cases right <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact congrArg (fun q : Σ b : h.val.1.Branch,
        Fin (branchPopulation allocation dilation h.val b) =>
      producedHalfWord allocation dilation x h q.1 false q.2) he
  · exact congrArg (fun q : Σ b : h.val.1.Branch,
        Fin (branchPopulation allocation dilation h.val b) =>
      producedHalfWord allocation dilation x h q.1 true q.2) he

def canonicalHalfShape
    (p : CanonicalHalfPosition (K := K) (tick := tick) allocation dilation) : AllFieldParameters.Shape :=
  if p.2 then activeParentShape p.1.1.1 - JointCanonicalCW.shapeNat p.1.1.2
  else JointCanonicalCW.shapeNat p.1.1.2

theorem canonicalProduced_length
    (p : CanonicalHalfPosition (K := K) (tick := tick) allocation dilation) :
    currentLength (canonicalProducedEquiv allocation dilation p).1.val.1 =
      activeHalfLength p.1.1.1 :=
  splitProduced_length allocation dilation (canonicalSplitEquiv allocation dilation p)

theorem canonicalProduced_shape
    (p : CanonicalHalfPosition (K := K) (tick := tick) allocation dilation) :
    currentPhysicalShape (canonicalProducedEquiv allocation dilation p).1.val =
      canonicalHalfShape allocation dilation p := by
  let w := p.1.1.1
  let q := branchPositionEquiv allocation dilation w.val ⟨p.1.1.2, p.1.2⟩
  have hu : physicalShape w.val.2 (w.val.1.splitShape q.1) =
      JointCanonicalCW.shapeNat p.1.1.2 := by
    change physicalShape w.val.2 (w.val.1.splitShape q.1) = decodeShape p.1.1.2
    have hh := congrArg decodeShape
      (branchPositionEquiv_shape allocation dilation w.val ⟨p.1.1.2, p.1.2⟩)
    simpa only [branchShape, decode_encodePhysicalShape] using hh
  let shapeOfSplit (r : SplitPositions (K := K) (tick := tick) allocation dilation) :
      AllFieldParameters.Shape :=
    physicalShape r.1.val.2 (halfShape r.1.val.1.parentShape
      (r.1.val.1.splitShape r.2.1) r.2.2.1)
  have hs : currentPhysicalShape
      ((producedPositionEquiv allocation dilation).symm
        (canonicalSplitEquiv allocation dilation p)).1.val =
      shapeOfSplit ((producedPositionEquiv allocation dilation)
        ((producedPositionEquiv allocation dilation).symm
          (canonicalSplitEquiv allocation dilation p))) :=
    producedPositionEquiv_shape allocation dilation
      ((producedPositionEquiv allocation dilation).symm
        (canonicalSplitEquiv allocation dilation p))
  rw [Equiv.apply_symm_apply] at hs
  change currentPhysicalShape (canonicalProducedEquiv allocation dilation p).1.val =
    physicalShape w.val.2 (halfShape w.val.1.parentShape
      (w.val.1.splitShape q.1) p.2) at hs
  rw [hs]
  cases hr : p.2 <;>
    simp [canonicalHalfShape, halfShape, hr, physicalShape_complement, hu,
      activeParentShape]
  rfl

variable {F : Type*} [Field F]

theorem shapeTensor_finCast {m n : ℕ} (h : m = n) (g : AllFieldParameters.Shape)
    (x y z : Fin n → Fin 7) :
    shapeTensor (F := F) (Fin m) g (x ∘ Fin.cast h) (y ∘ Fin.cast h) (z ∘ Fin.cast h) =
      shapeTensor (Fin n) g x y z := by
  cases h
  rfl

def canonicalChildren : Tensor F
    (CanonicalWords (K := K) (tick := tick) allocation dilation)
    (CanonicalWords (K := K) (tick := tick) allocation dilation)
    (CanonicalWords (K := K) (tick := tick) allocation dilation) :=
  pairClassProduct (P := ClassPositions (activeCounts allocation dilation))
    (JointCanonicalCW.leftTensor activeHalfLength)
    (JointCanonicalCW.rightTensor activeHalfLength activeParentShape)

def producedBase : Tensor F
    (ProducedWords (K := K) (tick := tick) allocation dilation)
    (ProducedWords (K := K) (tick := tick) allocation dilation)
    (ProducedWords (K := K) (tick := tick) allocation dilation) :=
  CommonDimensions.familyProduct (fun h : Produced K tick =>
    Tensor.power (shapeTensor (Fin (currentLength h.val.1)) (currentPhysicalShape h.val))
      (population allocation dilation h.val))

def canonicalHalfWord (x : CanonicalWords (K := K) (tick := tick) allocation dilation)
    (p : CanonicalHalfPosition (K := K) (tick := tick) allocation dilation) :
    Fin (activeHalfLength p.1.1.1) → Fin 7 :=
  if p.2 then x.right p.1.1 p.1.2 else x.left p.1.1 p.1.2

theorem regroupWords_half (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (p : CanonicalHalfPosition (K := K) (tick := tick) allocation dilation) :
    canonicalHalfWord allocation dilation (regroupWords allocation dilation x) p =
      regroupAt allocation dilation x p := by
  rcases p with ⟨⟨c, i⟩, right⟩
  cases right <;> simp only [canonicalHalfWord, regroupWords, Bool.false_eq_true, ↓reduceIte]

theorem canonicalChildren_flat
    (x y z : CanonicalWords (K := K) (tick := tick) allocation dilation) :
    canonicalChildren (F := F) allocation dilation x y z =
      ∏ p : CanonicalHalfPosition (K := K) (tick := tick) allocation dilation,
        shapeTensor (Fin (activeHalfLength p.1.1.1)) (canonicalHalfShape allocation dilation p)
          (canonicalHalfWord allocation dilation x p)
          (canonicalHalfWord allocation dilation y p)
          (canonicalHalfWord allocation dilation z p) := by
  simp only [CanonicalHalfPosition, Fintype.prod_prod_type, CanonicalClassPosition,
    Fintype.prod_sigma, Fintype.prod_bool, canonicalHalfShape, canonicalHalfWord,
    Bool.false_eq_true, ↓reduceIte, Finset.prod_mul_distrib,
    canonicalChildren, pairClassProduct, classProduct, JointCanonicalCW.leftTensor,
    JointCanonicalCW.rightTensor]
  exact mul_comm _ _

theorem producedBase_flat
    (x y z : ProducedWords (K := K) (tick := tick) allocation dilation) :
    producedBase (F := F) allocation dilation x y z =
      ∏ p : ProducedPositions (K := K) (tick := tick) allocation dilation,
        shapeTensor (Fin (currentLength p.1.val.1)) (currentPhysicalShape p.1.val)
          (x p.1 p.2) (y p.1 p.2) (z p.1 p.2) := by
  simp only [producedBase, CommonDimensions.familyProduct, Tensor.power,
    ProducedPositions, Fintype.prod_sigma]

theorem regroup_coefficient_at
    (x y z : ProducedWords (K := K) (tick := tick) allocation dilation)
    (p : CanonicalHalfPosition (K := K) (tick := tick) allocation dilation) :
    shapeTensor (F := F) (Fin (activeHalfLength p.1.1.1)) (canonicalHalfShape allocation dilation p)
      (regroupAt allocation dilation x p) (regroupAt allocation dilation y p)
      (regroupAt allocation dilation z p) =
    shapeTensor (Fin (currentLength (canonicalProducedEquiv allocation dilation p).1.val.1))
      (currentPhysicalShape (canonicalProducedEquiv allocation dilation p).1.val)
      (x (canonicalProducedEquiv allocation dilation p).1 (canonicalProducedEquiv allocation dilation p).2)
      (y (canonicalProducedEquiv allocation dilation p).1 (canonicalProducedEquiv allocation dilation p).2)
      (z (canonicalProducedEquiv allocation dilation p).1 (canonicalProducedEquiv allocation dilation p).2) := by
  rw [← canonicalProduced_shape allocation dilation p]
  exact shapeTensor_finCast (canonicalProduced_length allocation dilation p).symm _ _ _ _

theorem regroup_coefficient
    (x y z : ProducedWords (K := K) (tick := tick) allocation dilation) :
    canonicalChildren (F := F) allocation dilation
      (regroupWords allocation dilation x) (regroupWords allocation dilation y)
      (regroupWords allocation dilation z) = producedBase allocation dilation x y z := by
  rw [canonicalChildren_flat, producedBase_flat]
  simp only [regroupWords_half]
  exact Fintype.prod_equiv (canonicalProducedEquiv allocation dilation) _ _
    (regroup_coefficient_at allocation dilation x y z)

theorem regroup_pullback :
    Tensor.pullback (regroupWords allocation dilation) (regroupWords allocation dilation)
      (regroupWords allocation dilation) (canonicalChildren (F := F) allocation dilation) =
        producedBase (K := K) (tick := tick) allocation dilation := by
  funext x y z
  exact regroup_coefficient allocation dilation x y z

def regroupMatrix :
    ProducedWords (K := K) (tick := tick) allocation dilation →
      CanonicalWords (K := K) (tick := tick) allocation dilation → F :=
  fun x s => if s = regroupWords allocation dilation x then 1 else 0

def producedBaseMap :
    AllFieldFiniteFamily.LocalMap
      (canonicalChildren (F := F) (K := K) (tick := tick) allocation dilation)
      (producedBase (F := F) (K := K) (tick := tick) allocation dilation) where
  x := regroupMatrix allocation dilation
  y := regroupMatrix allocation dilation
  z := regroupMatrix allocation dilation
  coefficient := by
    unfold regroupMatrix
    rw [← Tensor.pullback_eq_restrict]
    exact regroup_pullback allocation dilation

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryProducedMasks

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldHistoryChildLaws InheritedMasks
open JointCanonicalization
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def nativeChildWidth (ε : ℝ) (h : Active K tick) : ℝ :=
  (ε / 16 ^ h.val.1.stage.val) / 8

def halfPositionEquiv (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool) :
    Fin (branchPopulation allocation dilation w b) ≃
      Fin (population allocation dilation (w.1.child b right, w.2)) where
  toFun := halfPosition allocation dilation w b right
  invFun := unhalfPosition allocation dilation w b right
  left_inv := unhalf_halfPosition allocation dilation w b right
  right_inv := half_unhalfPosition allocation dilation w b right

def childHalfWord (allocation : Allocation) (dilation : ℕ)
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool)
    (v : HistoryWord allocation dilation (h.val.1.child b right, h.val.2)) :
    Fin (branchPopulation allocation dilation h.val b) →
      Fin (activeHalfLength h) → Fin 7 :=
  fun i j => v (halfPosition allocation dilation h.val b right i)
    (Fin.cast (child_length h.val.1 b right).symm j)

theorem subsingleton_typeWindow {P A : Type*} [Fintype P] [Nonempty P]
    [Subsingleton A] [DecidableEq A] (η : ℝ) (hη : 0 ≤ η) (w : P → A) :
    typeWindow (fun _ : A => 1) η w := by
  intro a
  have hcount : wordPopulation w a = Fintype.card P := by
    apply Fintype.card_congr
    exact
      { toFun := Subtype.val
        invFun := fun i => ⟨i, Subsingleton.elim _ _⟩
        left_inv := fun i => Subtype.ext rfl
        right_inv := fun i => rfl }
  have hpos : (0 : ℝ) < Fintype.card P := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card P)
  simpa only [empiricalLaw, hcount, div_self (ne_of_gt hpos), sub_self, abs_zero] using hη

theorem childHalfWord_window (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool)
    (v : HistoryWord allocation dilation (h.val.1.child b right, h.val.2))
    (hv : residentMask allocation dilation ε (h.val.1.child b right, h.val.2) side v)
    (hp : 0 < branchPopulation allocation dilation h.val b) :
    typeWindow (fun a => (h.val.1.childLaw
        (halfShape h.val.1.parentShape (h.val.1.splitShape b) right)
        (h.val.2.symm side) a : ℝ)) (nativeChildWidth ε h)
      (h.val.1.statistic ∘ childHalfWord allocation dilation h b right v) := by
  rcases h with ⟨⟨work, phi⟩, ht⟩
  cases work with
  | stageA parent =>
      have hp' : 0 < population allocation dilation
          ((Work.stageA parent).child b right, phi) := by
        rw [branchPopulation_half allocation dilation (.stageA parent, phi) b right]
        exact hp
      have hw := (Subdivision.typeWindow_reindex
        (residentLaw ((Work.stageA parent).child b right, phi) side)
        (ε / 8) (fun i => residentStatistic ((Work.stageA parent).child b right) (v i))
        (halfPositionEquiv allocation dilation (.stageA parent, phi) b right)).mpr (hv hp')
      have he : nativeChildWidth ε (⟨(.stageA parent, phi), ht⟩ : Active K tick) = ε / 8 := by
        norm_num [nativeChildWidth, Work.stage]
      rw [he]
      exact hw
  | stageB parent =>
      have hp' : 0 < population allocation dilation
          ((Work.stageB parent).child b right, phi) := by
        rw [branchPopulation_half allocation dilation (.stageB parent, phi) b right]
        exact hp
      have hw := (Subdivision.typeWindow_reindex
        (residentLaw ((Work.stageB parent).child b right, phi) side)
        (ε / 128) (fun i => residentStatistic ((Work.stageB parent).child b right) (v i))
        (halfPositionEquiv allocation dilation (.stageB parent, phi) b right)).mpr (hv hp')
      have he : nativeChildWidth ε (⟨(.stageB parent, phi), ht⟩ : Active K tick) = ε / 128 := by
        norm_num [nativeChildWidth, Work.stage, div_div]
      rw [he]
      exact hw
  | stageC parent =>
      let : Nonempty (Fin (branchPopulation allocation dilation (.stageC parent, phi) b)) :=
        ⟨⟨0, hp⟩⟩
      let : Subsingleton (Work.stageC parent).Statistic := by
        change Subsingleton PUnit
        infer_instance
      simp only [Work.childLaw, Rat.cast_one]
      apply subsingleton_typeWindow
      unfold nativeChildWidth
      positivity

theorem afterB_mask_of_part_masks (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (h : BPositive K) (phi : Placement) (side : Fin 3)
    (w : ∀ i : Fin 3, HistoryWord allocation dilation (.partC (h, i), phi))
    (hw : ∀ i, residentMask allocation dilation ε (.partC (h, i), phi) side (w i)) :
    residentMask allocation dilation ε (.afterB h.val, phi) side
      (fun j => w (bSubdivisionPositionEquiv allocation dilation h phi j).1
        (bSubdivisionPositionEquiv allocation dilation h phi j).2) := by
  intro hp
  let P : Fin 3 → Type := fun i =>
    Fin (population allocation dilation (.partC (h, i), phi))
  let e := bSubdivisionPositionEquiv allocation dilation h phi
  have hsize : 0 < Fintype.card (Σ i, P i) := by
    rw [← Fintype.card_congr e]
    simpa only [Fintype.card_fin] using hp
  have hwidth : ∀ _ : Fin 3, ε / 256 ≤ ε / 128 := by
    intro i
    linarith
  have hparts : Subdivision.partWindows P
      (residentLaw (.afterB h.val, phi) side) (fun _ => ε / 256)
      (fun i => CWCompleteStatistics.twoStatistic ∘ w i) := by
    intro i hi
    have hi' : 0 < population allocation dilation (.partC (h, i), phi) := by
      simpa only [P, Fintype.card_fin] using hi
    exact hw i hi'
  exact Subdivision.statisticWindow_concatenate_at
    (A := ResidentStatistic (.afterB h.val)) P e CWCompleteStatistics.twoStatistic
    (residentLaw (.afterB h.val, phi) side) (ε / 128) (fun _ => ε / 256)
    (div_nonneg hε (by norm_num)) hwidth hsize w hparts

def producedChildWord (allocation : Allocation) (dilation : ℕ)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool) :
    HistoryWord allocation dilation (h.val.1.child b right, h.val.2) := by
  rcases h with ⟨⟨work, phi⟩, ht⟩
  cases work with
  | stageA parent => exact x ⟨(.afterA ⟨parent, b, right⟩, phi), ht.symm⟩
  | stageB parent =>
      by_cases hp : positive (bShape (⟨parent, b, right⟩ : AfterB K)) = true
      · let g : BPositive K := ⟨⟨parent, b, right⟩, hp⟩
        let e := bSubdivisionPositionEquiv allocation dilation g phi
        exact fun j => x ⟨(.partC (g, (e j).1), phi), ht.symm⟩ (e j).2
      · exact x ⟨(.afterB ⟨parent, b, right⟩, phi), ht.symm, hp⟩
  | stageC parent => exact x ⟨(.afterC (parent, b, right), phi), ht.symm⟩

theorem producedChildWord_mask (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (hx : ∀ h : Produced K tick, residentMask allocation dilation ε h.val side (x h))
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool) :
    residentMask allocation dilation ε (h.val.1.child b right, h.val.2) side
      (producedChildWord allocation dilation x h b right) := by
  rcases h with ⟨⟨work, phi⟩, ht⟩
  cases work with
  | stageA parent => exact hx ⟨(.afterA ⟨parent, b, right⟩, phi), ht.symm⟩
  | stageB parent =>
      by_cases hp : positive (bShape (⟨parent, b, right⟩ : AfterB K)) = true
      · simp only [producedChildWord]
        erw [dite_eq_left hp]
        exact afterB_mask_of_part_masks allocation dilation hε
          ⟨⟨parent, b, right⟩, hp⟩ phi side
          (fun i => x ⟨(.partC (⟨⟨parent, b, right⟩, hp⟩, i), phi), ht.symm⟩)
          (fun i => hx ⟨(.partC (⟨⟨parent, b, right⟩, hp⟩, i), phi), ht.symm⟩)
      · simp only [producedChildWord]
        erw [dite_eq_right hp]
        exact hx (⟨(.afterB ⟨parent, b, right⟩, phi), ht.symm, hp⟩ : Produced K tick)
  | stageC parent => trivial

private theorem splitWord_eq_of_position (allocation : Allocation) (dilation : ℕ)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (p : SplitPositions (K := K) (tick := tick) allocation dilation)
    (q : ProducedPositions (K := K) (tick := tick) allocation dilation)
    (hq : (producedPositionEquiv allocation dilation).symm p = q)
    (hlen : currentLength q.1.val.1 = activeHalfLength p.1) :
    splitWord allocation dilation x p =
      fun i => x q.1 q.2 (Fin.cast hlen.symm i) := by
  subst q
  rfl

theorem producedHalfWord_eq_childHalfWord (allocation : Allocation) (dilation : ℕ)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool) :
    producedHalfWord allocation dilation x h b right =
      childHalfWord allocation dilation h b right
        (producedChildWord allocation dilation x h b right) := by
  rcases h with ⟨⟨work, phi⟩, ht⟩
  cases work with
  | stageA parent => rfl
  | stageB parent =>
      by_cases hp : positive (bShape (⟨parent, b, right⟩ : AfterB K)) = true
      · funext i
        let g : BPositive K := ⟨⟨parent, b, right⟩, hp⟩
        let part := bSubdivisionPositionEquiv allocation dilation g phi
          (halfPosition allocation dilation (.stageB parent, phi) b right i)
        let q : ProducedPositions (K := K) (tick := tick) allocation dilation :=
          ⟨⟨(.partC (g, part.1), phi), ht.symm⟩, part.2⟩
        have hq : (producedPositionEquiv allocation dilation).symm
            ⟨⟨(.stageB parent, phi), ht⟩, b, right, i⟩ = q := by
          simp only [producedPositionEquiv, Equiv.symm, Equiv.coe_fn_mk,
            splitToProduced, dite_eq_left hp]
          rfl
        simp only [producedHalfWord, producedChildWord]
        erw [dite_eq_left hp]
        exact splitWord_eq_of_position allocation dilation x
            ⟨⟨(.stageB parent, phi), ht⟩, b, right, i⟩ q hq rfl
      · funext i
        let q : ProducedPositions (K := K) (tick := tick) allocation dilation :=
          ⟨⟨(.afterB ⟨parent, b, right⟩, phi), ht.symm, hp⟩,
            halfPosition allocation dilation (.stageB parent, phi) b right i⟩
        have hq : (producedPositionEquiv allocation dilation).symm
            ⟨⟨(.stageB parent, phi), ht⟩, b, right, i⟩ = q := by
          simp only [producedPositionEquiv, Equiv.symm, Equiv.coe_fn_mk,
            splitToProduced, dite_eq_right hp]
          rfl
        simp only [producedHalfWord, producedChildWord]
        erw [dite_eq_right hp]
        exact splitWord_eq_of_position allocation dilation x
            ⟨⟨(.stageB parent, phi), ht⟩, b, right, i⟩ q hq rfl
  | stageC parent => rfl

theorem producedHalfWord_window (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (hx : ∀ h : Produced K tick, residentMask allocation dilation ε h.val side (x h))
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool)
    (hp : 0 < branchPopulation allocation dilation h.val b) :
    typeWindow (fun a => (h.val.1.childLaw
        (halfShape h.val.1.parentShape (h.val.1.splitShape b) right)
        (h.val.2.symm side) a : ℝ)) (nativeChildWidth ε h)
      (h.val.1.statistic ∘ producedHalfWord allocation dilation x h b right) := by
  rw [producedHalfWord_eq_childHalfWord]
  exact childHalfWord_window allocation dilation hε side h b right _
    (producedChildWord_mask allocation dilation hε side x hx h b right) hp

theorem regroupBranch_window (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (hx : ∀ h : Produced K tick, residentMask allocation dilation ε h.val side (x h))
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool)
    (hp : 0 < branchPopulation allocation dilation h.val b) :
    typeWindow (fun a => (placedChildLawRat h.val (branchShape h.val b) side right a : ℝ))
      (nativeChildWidth ε h)
      (statistic h ∘ (if right then (regroupWords allocation dilation x).right
        (h, branchShape h.val b) else (regroupWords allocation dilation x).left
        (h, branchShape h.val b))) := by
  apply (Subdivision.typeWindow_reindex _ _ _ (branchClassEquiv allocation dilation h b)).mp
  have he : (statistic h ∘ (if right then (regroupWords allocation dilation x).right
      (h, branchShape h.val b) else (regroupWords allocation dilation x).left
      (h, branchShape h.val b))) ∘ branchClassEquiv allocation dilation h b =
        h.val.1.statistic ∘ producedHalfWord allocation dilation x h b right := by
    funext i
    have hi := regroupWords_branch allocation dilation x h b right i
    cases right <;> exact congrArg h.val.1.statistic hi
  rw [he]
  simpa only [placedChildLawRat_branchShape] using
    producedHalfWord_window allocation dilation hε side x hx h b right hp

theorem canonicalWindows_of_produced_masks (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (hx : ∀ h : Produced K tick, residentMask allocation dilation ε h.val side (x h)) :
    HistorySymmetry.childWindows
      (fun c : Active K tick × JointPopulation.Shape => statistic c.1)
      (fun c : Active K tick × JointPopulation.Shape => statistic c.1)
      (activeLaw (activeCounts allocation dilation) (fun c => leftLaw c.1 c.2 side))
      (activeLaw (activeCounts allocation dilation) (fun c => rightLaw c.1 c.2 side))
      (activeWidth (activeCounts allocation dilation) (fun c => nativeChildWidth ε c.1))
      (activeWidth (activeCounts allocation dilation) (fun c => nativeChildWidth ε c.1))
      (regroupWords allocation dilation x) := by
  rintro ⟨h, u⟩
  by_cases hp : 0 < activeCounts allocation dilation h u
  · obtain ⟨b, hb, hpos⟩ := shapeCounts_positive (branchShape h.val)
      (branchPopulation allocation dilation h.val) u hp
    subst u
    have hl := regroupBranch_window allocation dilation hε side x hx h b false hpos
    have hr := regroupBranch_window allocation dilation hε side x hx h b true hpos
    rw [activeLaw_of_pos (activeCounts allocation dilation)
      (fun c => leftLaw c.1 c.2 side) (h, branchShape h.val b) hp,
      activeLaw_of_pos (activeCounts allocation dilation)
      (fun c => rightLaw c.1 c.2 side) (h, branchShape h.val b) hp]
    simp only [activeWidth, ite_eq_left hp]
    exact ⟨hl, hr⟩
  · have hz : activeCounts allocation dilation h u = 0 := Nat.eq_zero_of_not_pos hp
    simp only [activeLaw, activeWidth, typeWindow, empiricalLaw,
      Fintype.card_fin, hz, Nat.cast_zero, div_zero, sub_zero, abs_zero,
      le_refl, implies_true, and_self, Nat.lt_irrefl, ite_false]

end MatrixMultiplication.AllFieldHistoryProducedMasks

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryProducedMasks

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldHistoryChildLaws AllFieldHistoryMasks InheritedMasks
open JointCanonicalization
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem childWindows_of_produced_masks (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (hx : ∀ h : Produced K tick, residentMask allocation dilation ε h.val side (x h)) :
    AllFieldHistoryMasks.childWindows allocation dilation ε side
      (regroupWords allocation dilation x) :=
  canonicalWindows_of_produced_masks allocation dilation hε side x hx

end MatrixMultiplication.AllFieldHistoryProducedMasks

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryProduced

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldHistoryProducedMasks
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ)

def passes (ε : ℝ) (side : Fin 3)
    (w : AllFieldHistory.ProducedWords (K := K) (tick := tick) allocation m) : Prop :=
  ∀ h : Produced K tick, residentMask allocation m ε h.val side (w h)

theorem producedTensor_eq_delete (F : Type*) [Field F] (ε : ℝ) :
    AllFieldHistoryRegrouping.producedTensor (K := K) (tick := tick) allocation m F ε =
      ExactRecovery.delete (producedBase (F := F) (K := K) (tick := tick) allocation m)
        (passes allocation m ε 0) (passes allocation m ε 1) (passes allocation m ε 2) := by
  funext x y z
  simp only [AllFieldHistoryRegrouping.producedTensor, CommonDimensions.familyProduct,
    historyTensor, ExactRecovery.delete, Fintype.prod_ite_zero,
    passes, forall_and, producedBase]

theorem canonical_eq_delete (F : Type*) [Field F] (ε : ℝ) :
    AllFieldHistoryRecovery.canonical F (K := K) (tick := tick) allocation m ε =
      ExactRecovery.delete (canonicalChildren (F := F) (K := K) (tick := tick) allocation m)
        (AllFieldHistoryMasks.childWindows allocation m ε 0)
        (AllFieldHistoryMasks.childWindows allocation m ε 1)
        (AllFieldHistoryMasks.childWindows allocation m ε 2) := by
  have hb := JointCanonicalCW.canonicalBase_eq_children (F := F)
    (activeCounts (K := K) (tick := tick) allocation m)
    activeHalfLength activeHalfLength activeParentShape
    AllFieldHistoryRecovery.halfLength_le_eight
    (fun h u hu => jointCounts_support_le allocation m h.val u hu)
  unfold AllFieldHistoryRecovery.canonical JointCanonicalization.canonicalIdeal
  change ExactRecovery.delete
    (JointCanonicalization.canonicalBase (activeCounts allocation m)
      (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength)
      (JointCanonicalCW.parentTensor activeHalfLength activeHalfLength activeParentShape)
      (JointCanonicalCW.coarse activeHalfLength activeHalfLength
        AllFieldHistoryRecovery.halfLength_le_eight))
    (AllFieldHistoryMasks.childWindows allocation m ε 0)
    (AllFieldHistoryMasks.childWindows allocation m ε 1)
    (AllFieldHistoryMasks.childWindows allocation m ε 2) = _
  rw [hb]
  rfl

def pulled (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (AllFieldHistory.ProducedWords (K := K) (tick := tick) allocation m)
      (AllFieldHistory.ProducedWords (K := K) (tick := tick) allocation m)
      (AllFieldHistory.ProducedWords (K := K) (tick := tick) allocation m) :=
  Tensor.pullback (regroupWords allocation m) (regroupWords allocation m)
    (regroupWords allocation m)
    (AllFieldHistoryRecovery.canonical F (K := K) (tick := tick) allocation m ε)

theorem delete_pulled (F : Type*) [Field F] {ε : ℝ} (hε : 0 ≤ ε) :
    ExactRecovery.delete (pulled (K := K) (tick := tick) allocation m F ε)
      (passes allocation m ε 0) (passes allocation m ε 1) (passes allocation m ε 2) =
    AllFieldHistoryRegrouping.producedTensor (K := K) (tick := tick) allocation m F ε := by
  rw [producedTensor_eq_delete]
  funext x y z
  by_cases hp : passes allocation m ε 0 x ∧ passes allocation m ε 1 y ∧
      passes allocation m ε 2 z
  · simp only [ExactRecovery.delete, ite_eq_left hp]
    unfold pulled Tensor.pullback
    rw [canonical_eq_delete]
    have hx := childWindows_of_produced_masks allocation m hε 0 x hp.1
    have hy := childWindows_of_produced_masks allocation m hε 1 y hp.2.1
    have hz := childWindows_of_produced_masks allocation m hε 2 z hp.2.2
    unfold ExactRecovery.delete
    rw [ite_eq_left ⟨hx, hy, hz⟩]
    exact regroup_coefficient allocation m x y z
  · simp only [ExactRecovery.delete, ite_eq_right hp]

def pullbackMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (AllFieldHistoryRecovery.canonical F (K := K) (tick := tick) allocation m ε)
      (pulled (K := K) (tick := tick) allocation m F ε) := by
  apply LocalMap.ofExists
  exact ⟨_, _, _, (Tensor.pullback_eq_restrict
    (regroupWords (K := K) (tick := tick) allocation m)
    (regroupWords (K := K) (tick := tick) allocation m)
    (regroupWords (K := K) (tick := tick) allocation m) _).symm⟩

def map (F : Type*) [Field F] {ε : ℝ} (hε : 0 ≤ ε) :
    LocalMap (AllFieldHistoryRecovery.canonical F (K := K) (tick := tick) allocation m ε)
      (AllFieldHistoryRegrouping.producedTensor (K := K) (tick := tick) allocation m F ε) := by
  let first := pullbackMap (K := K) (tick := tick) allocation m F ε
  let last := LocalMap.delete (pulled (K := K) (tick := tick) allocation m F ε)
    (passes allocation m ε 0) (passes allocation m ε 1) (passes allocation m ε 2)
  let combined := first.comp last
  exact ⟨combined.x, combined.y, combined.z,
    combined.coefficient.trans (delete_pulled allocation m F hε)⟩

end MatrixMultiplication.AllFieldHistoryProduced

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryTick

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldGroupSelection AllFieldHistoryGroupedRecovery
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ) (ε slack : ℝ)

abbrev Choices := ∀ sigma : Placement,
  Selected (K := K) (tick := tick) allocation m ε sigma slack

abbrev AmbientTag (sigma : Placement) :=
  JointCoarseHashing.Triple
    (AllFieldGroupOrbitData.Pos (K := K) (tick := tick) allocation m sigma)

abbrev Tags (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :=
  ∀ sigma : Placement, {e // e ∈ (chosen sigma).targets}

local instance tagsDecidableEq (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    DecidableEq (Tags allocation m ε slack chosen) := Classical.decEq _

@[instance_reducible] private def coarseTripleFintype (P : Type) [Fintype P] :
    Fintype (JointCoarseHashing.Triple P) := inferInstance

instance ambientTagFintype (sigma : Placement) :
    Fintype (AmbientTag (K := K) (tick := tick) allocation m sigma) :=
  coarseTripleFintype (AllFieldGroupOrbitData.Pos (K := K) (tick := tick) allocation m sigma)

instance ambientTagsFintype :
    Fintype (∀ sigma, AmbientTag (K := K) (tick := tick) allocation m sigma) := inferInstance

instance tagsFintype (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Fintype (Tags allocation m ε slack chosen) := inferInstance

def select (chosen : Choices (K := K) (tick := tick) allocation m ε slack)
    (j : Tags allocation m ε slack chosen) :
    ∀ sigma, AmbientTag (K := K) (tick := tick) allocation m sigma :=
  fun sigma => AllFieldGroupOrbitData.coarse allocation m sigma (j sigma).val

theorem select_injective
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Function.Injective (select allocation m ε slack chosen) := by
  intro j k h
  funext sigma
  apply Subtype.ext
  exact AllFieldGroupOrbitData.coarse_injective allocation m sigma (congrFun h sigma)

def targets (chosen : Choices (K := K) (tick := tick) allocation m ε slack)
    (j : Tags allocation m ε slack chosen) :
    AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m :=
  joinGroupTargets (activeCounts allocation m) (fun sigma => (j sigma).val)

def assignments (chosen : Choices (K := K) (tick := tick) allocation m ε slack)
    (sigma : Placement) :=
  AllFieldGroupAssignmentRetention.physicalAssignment allocation m ε sigma
    (JointOrdinarySelection.hashLevel
      (selectionHashRate (K := K) (tick := tick) allocation sigma slack) m)
    (JointOrdinarySelection.hashSet
      (selectionHashRate (K := K) (tick := tick) allocation sigma slack) m)
    (chosen sigma).sample

def assignment (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :=
  groupedAssignment allocation m (AmbientTag (K := K) (tick := tick) allocation m)
    (assignments allocation m ε slack chosen)

theorem coherent (F : Type*) [Field F]
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    JointExtraction.Coherent
      (AllFieldHistorySource.preparedSource (K := K) (tick := tick) allocation m F ε)
      (assignment allocation m ε slack chosen) := by
  apply AllFieldHistorySource.groupedAssignment_coherent allocation m F ε
  intro sigma
  exact AllFieldGroupAssignments.physicalAssignment_coherent F allocation m ε sigma
    _ _ (chosen sigma).sample

theorem repair (F : Type*) [Field F] (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack)
    (j : Tags allocation m ε slack chosen) :
    InverseLinearRecovery.RecoveredBy
      (AllFieldHistoryRecovery.ideal F allocation m ε (targets allocation m ε slack chosen j))
      (JointExtraction.branch
        (AllFieldHistorySource.preparedSource (K := K) (tick := tick) allocation m F ε)
        (assignment allocation m ε slack chosen) (select allocation m ε slack chosen j))
      (AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m) := by
  rw [AllFieldHistorySource.preparedSource_eq_delete]
  apply repair_grouped F allocation hε hm
    (AmbientTag (K := K) (tick := tick) allocation m)
    (assignments allocation m ε slack chosen)
    (select allocation m ε slack chosen j) (fun sigma => (j sigma).val)
  · intro sigma w hw
    have hs := AllFieldGroupAssignmentRetention.assigned_some_idealSide
      allocation m ε sigma _ _ (chosen sigma).sample (j sigma).val (sigma.symm 0, w) hw
    simpa only [Equiv.apply_symm_apply] using hs
  · intro sigma w hw
    have hs := AllFieldGroupAssignmentRetention.assigned_some_idealSide
      allocation m ε sigma _ _ (chosen sigma).sample (j sigma).val (sigma.symm 1, w) hw
    simpa only [Equiv.apply_symm_apply] using hs
  · intro sigma w hw
    have hs := AllFieldGroupAssignmentRetention.assigned_some_idealSide
      allocation m ε sigma _ _ (chosen sigma).sample (j sigma).val (sigma.symm 2, w) hw
    simpa only [Equiv.apply_symm_apply] using hs
  · intro side w hw sigma
    have hg := (chosen sigma).good (j sigma).val (j sigma).property
    have hh := AllFieldGroupAssignmentRetention.good_projected_failure_le F
      allocation m ε sigma _ _
      (JointOrdinarySelection.hashSet_AP (selectionHashRate allocation sigma slack) m)
      (m : ℝ) (chosen sigma).sample (targets allocation m ε slack chosen j)
      (by simpa only [targets, project_joinGroupTargets] using hg) side w hw
    simp only [targets, project_joinGroupTargets, assignments, select] at hh ⊢
    exact hh

def canonicalMap (F : Type*) [Field F]
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m) :
    LocalMap (AllFieldHistoryRecovery.ideal F allocation m ε e)
      (AllFieldHistoryRecovery.canonical (K := K) (tick := tick) F allocation m ε) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (AllFieldHistoryRecovery.coordinates allocation m e).symm
    (AllFieldHistoryRecovery.coordinates allocation m e).symm
    (AllFieldHistoryRecovery.coordinates allocation m e).symm _).symm.trans ?_⟩
  funext x y z
  change AllFieldHistoryRecovery.ideal F allocation m ε e _ _ _ = _
  rw [AllFieldHistoryRecovery.ideal_coordinates]
  simp only [Equiv.apply_symm_apply]

def activeExecution (F : Type*) [Field F] (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Execution
      (AllFieldHistoryRegrouping.activeTensor (K := K) (tick := tick) allocation m F ε)
      (Tensor.directSum (fun _ : Tags allocation m ε slack chosen =>
        AllFieldHistoryRegrouping.producedTensor (K := K) (tick := tick) allocation m F ε)) := by
  let prepared := (Execution.initial
    (AllFieldHistoryRegrouping.activeTensor (K := K) (tick := tick) allocation m F ε)).restrict _
      (AllFieldHistorySource.preparedMap (K := K) (tick := tick) allocation m F ε)
  let repaired := prepared.extractSelectedAndRepair
    (assignment allocation m ε slack chosen) (coherent allocation m ε slack F chosen)
    (select allocation m ε slack chosen) (select_injective allocation m ε slack chosen)
    (fun j => AllFieldHistoryRecovery.ideal F allocation m ε (targets allocation m ε slack chosen j))
    (AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m)
    (repair allocation m ε slack F hε hm chosen)
  let canonical := repaired.restrict _ (LocalMap.directSum _ _
    (fun j => canonicalMap allocation m ε F (targets allocation m ε slack chosen j)))
  exact canonical.restrict _
    ((AllFieldHistoryProduced.map (K := K) (tick := tick) allocation m F hε.le).parallelCopies _)

@[simp] theorem activeExecution_copies (F : Type*) [Field F] (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Fintype.card (activeExecution allocation m ε slack F hε hm chosen).Copies =
      2 ^ (3 * AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m) := by
  simp only [activeExecution, Execution.restrict]
  erw [Execution.extractSelectedAndRepair_copies]
  simp only [Execution.initial]
  exact mul_one _

theorem card_tags (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Fintype.card (Tags allocation m ε slack chosen) =
      ∏ _sigma : Placement,
        ⌊Real.exp ((m : ℝ) * (nativeCapacity (K := K) (tick := tick) allocation - slack))⌋₊ := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro sigma _
  simpa only [Fintype.card_coe] using (chosen sigma).card_targets

def execution (F : Type*) [Field F] (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Execution (stateTensor F (K := K) allocation m ε tick)
      (Tensor.directSum (fun _ : Tags allocation m ε slack chosen =>
        stateTensor F (K := K) allocation m ε (tick + 1))) :=
  AllFieldHistoryTickCarry.liftExecution (K := K) (tick := tick) allocation m F ε
    (activeExecution allocation m ε slack F hε hm chosen)

@[simp] theorem execution_copies (F : Type*) [Field F] (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Fintype.card (execution allocation m ε slack F hε hm chosen).Copies =
      2 ^ (3 * AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m) :=
  activeExecution_copies allocation m ε slack F hε hm chosen

end MatrixMultiplication.AllFieldHistoryTick

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryIteration

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

section Presentation

variable {F : Type*} [Field F] {SX SY SZ X Y Z : Type}
    [Fintype SX] [Fintype SY] [Fintype SZ]
    {source : Tensor F SX SY SZ} {target next : Tensor F X Y Z}

private def retarget (E : Execution source target) (h : target = next) :
    Execution source next where
  Copies := E.Copies
  copies_positive := E.copies_positive
  map := {
    x := E.map.x
    y := E.map.y
    z := E.map.z
    coefficient := E.map.coefficient.trans h
  }

@[simp] private theorem retarget_copies (E : Execution source target) (h : target = next) :
    Fintype.card (retarget E h).Copies = Fintype.card E.Copies := rfl

end Presentation

variable {K : ℕ} (allocation : Allocation) (m : ℕ) (ε slack : ℝ)

abbrev ScheduleChoices := ∀ t : Fin (K + 2),
  AllFieldHistoryTick.Choices (K := K) (tick := t.val) allocation m ε slack

def Labels (InitialTag : Type)
    (chosen : ScheduleChoices (K := K) allocation m ε slack) :
    (n : ℕ) → n ≤ K + 2 → Type
  | 0, _ => InitialTag
  | n + 1, hn =>
      Labels InitialTag chosen n (Nat.le_of_succ_le hn) ×
        AllFieldHistoryTick.Tags allocation m ε slack (chosen ⟨n, hn⟩)

instance labelsFintype (InitialTag : Type) [Fintype InitialTag]
    (chosen : ScheduleChoices (K := K) allocation m ε slack) :
    (n : ℕ) → (hn : n ≤ K + 2) →
      Fintype (Labels allocation m ε slack InitialTag chosen n hn)
  | 0, _ => inferInstanceAs (Fintype InitialTag)
  | n + 1, hn => by
      letI := labelsFintype InitialTag chosen n (Nat.le_of_succ_le hn)
      exact inferInstanceAs (Fintype
        (Labels allocation m ε slack InitialTag chosen n (Nat.le_of_succ_le hn) ×
          AllFieldHistoryTick.Tags allocation m ε slack (chosen ⟨n, hn⟩)))

theorem card_labels (InitialTag : Type) [Fintype InitialTag]
    (chosen : ScheduleChoices (K := K) allocation m ε slack)
    (n : ℕ) (hn : n ≤ K + 2) :
    Fintype.card (Labels allocation m ε slack InitialTag chosen n hn) =
      Fintype.card InitialTag * ∏ t : Fin n, ∏ _sigma : Placement,
        ⌊Real.exp ((m : ℝ) *
          (AllFieldGroupSelection.nativeCapacity (K := K) (tick := t.val) allocation - slack))⌋₊ := by
  induction n with
  | zero =>
      simp [Labels]
      rfl
  | succ n ih =>
      change Fintype.card
        (Labels allocation m ε slack InitialTag chosen n (Nat.le_of_succ_le hn) ×
          AllFieldHistoryTick.Tags allocation m ε slack (chosen ⟨n, hn⟩)) = _
      rw [Fintype.card_prod, AllFieldHistoryTick.card_tags, ih, Fin.prod_univ_castSucc]
      exact Nat.mul_assoc _ _ _

abbrev Tags (InitialTag : Type)
    (chosen : ScheduleChoices (K := K) allocation m ε slack) :=
  Labels allocation m ε slack InitialTag chosen (K + 2) le_rfl

theorem card_tags (InitialTag : Type) [Fintype InitialTag]
    (chosen : ScheduleChoices (K := K) allocation m ε slack) :
    Fintype.card (Tags allocation m ε slack InitialTag chosen) =
      Fintype.card InitialTag * ∏ t : Fin (K + 2), ∏ _sigma : Placement,
        ⌊Real.exp ((m : ℝ) *
          (AllFieldGroupSelection.nativeCapacity (K := K) (tick := t.val) allocation - slack))⌋₊ :=
  card_labels allocation m ε slack InitialTag chosen (K + 2) le_rfl

variable (F : Type*) [Field F] (hε : 0 < ε)
    (hm : ∀ t : Fin (K + 2),
      AllFieldHistoryRecovery.minimumDilation (K := K) (tick := t.val) allocation ε ≤ m)
    (chosen : ScheduleChoices (K := K) allocation m ε slack)
    {InitialTag : Type} [Fintype InitialTag]
    (start : Execution (cwSource F K (populationLength (K := K) allocation m))
      (Tensor.directSum (fun _ : InitialTag => stateTensor F (K := K) allocation m ε 0)))

def run : (n : ℕ) → (hn : n ≤ K + 2) →
    Execution (cwSource F K (populationLength (K := K) allocation m))
      (Tensor.directSum (fun _ : Labels allocation m ε slack InitialTag chosen n hn =>
        stateTensor F (K := K) allocation m ε n))
  | 0, _ => start
  | n + 1, hn =>
      let step := AllFieldHistoryTick.execution allocation m ε slack F hε
        (hm ⟨n, hn⟩) (chosen ⟨n, hn⟩)
      let operation := Execution.branchOperation
        (stateTensor F (K := K) allocation m ε n)
        (stateTensor F (K := K) allocation m ε (n + 1))
        (run n (Nat.le_of_succ_le hn)) step.copies_positive step.map
      retarget operation (by
        funext x y z
        simp only [Tensor.directSum]
        split_ifs <;> first | rfl | contradiction)

theorem run_copies (n : ℕ) (hn : n ≤ K + 2) :
    Fintype.card (run allocation m ε slack F hε hm chosen start n hn).Copies =
      Fintype.card start.Copies * ∏ t : Fin n,
        2 ^ (3 * AllFieldHistoryRecovery.shiftCount (K := K) (tick := t.val) allocation ε m) := by
  induction n with
  | zero =>
      simp [run]
      rfl
  | succ n ih =>
      rw [run]
      erw [retarget_copies, Execution.branchOperation_copies, AllFieldHistoryTick.execution_copies,
        ih, Fin.prod_univ_castSucc]
      ring

def execution :
    Execution (cwSource F K (populationLength (K := K) allocation m))
      (Tensor.directSum (fun _ : Tags allocation m ε slack InitialTag chosen =>
        stateTensor F (K := K) allocation m ε (K + 2))) :=
  run allocation m ε slack F hε hm chosen start (K + 2) le_rfl

@[simp] theorem execution_copies :
    Fintype.card (execution allocation m ε slack F hε hm chosen start).Copies =
      Fintype.card start.Copies * ∏ t : Fin (K + 2),
        2 ^ (3 * AllFieldHistoryRecovery.shiftCount (K := K) (tick := t.val) allocation ε m) :=
  run_copies allocation m ε slack F hε hm chosen start (K + 2) le_rfl

end MatrixMultiplication.AllFieldHistoryIteration

end
end

end MatrixAllFields

end OAI
