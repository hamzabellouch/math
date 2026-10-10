import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Positions
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CanonicalCW
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.FiniteFamily

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

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
    have hh := congrArg decodeShape
      (branchPositionEquiv_shape allocation dilation w.val ⟨p.1.1.2, p.1.2⟩)
    simp only [branchShape, decode_encodePhysicalShape] at hh
    exact hh
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

end OAI
