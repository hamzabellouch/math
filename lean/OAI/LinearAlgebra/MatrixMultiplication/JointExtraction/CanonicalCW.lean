import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.Canonicalization
import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWCoarseIndices

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointCanonicalCW

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization
open CWStrands HistorySymmetry InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H F : Type*} [Fintype H] [DecidableEq H] [CommRing F]
    (counts : H → Shape → ℕ) (leftLength rightLength : H → ℕ)
    (parentShape : H → Fin 3 → ℕ)
    (hleft : ∀ h, leftLength h ≤ 8)

abbrev Left (h : H) := Fin (leftLength h) → Fin 7
abbrev Right (h : H) := Fin (rightLength h) → Fin 7

def shapeNat (u : Shape) : Fin 3 → ℕ := fun s => (shapeSide s u).val

def parentTensor (h : H) : Tensor F
    (Left leftLength h × Right rightLength h)
    (Left leftLength h × Right rightLength h)
    (Left leftLength h × Right rightLength h) :=
  fun x y z => shapeTensor (Fin (leftLength h) ⊕ Fin (rightLength h)) (parentShape h)
    (Sum.elim x.1 x.2) (Sum.elim y.1 y.2) (Sum.elim z.1 z.2)

def coarse (_s : Fin 3) (h : H) (w : Left leftLength h × Right rightLength h) : Fin 17 :=
  CWCoarseIndices.coarseIndex (by simpa using hleft h) w.1

def leftTensor (c : ClassKey (H := H)) :
    Tensor F (Left leftLength c.1) (Left leftLength c.1) (Left leftLength c.1) :=
  shapeTensor (Fin (leftLength c.1)) (shapeNat c.2)

def rightTensor (c : ClassKey (H := H)) :
    Tensor F (Right rightLength c.1) (Right rightLength c.1) (Right rightLength c.1) :=
  shapeTensor (Fin (rightLength c.1)) (parentShape c.1 - shapeNat c.2)

omit [Fintype H] [DecidableEq H] in
theorem block_eq_product (h : H) (u : Shape)
    (hu : ∀ s, shapeNat u s ≤ parentShape h s) :
    block (Left leftLength) (Right rightLength)
      (parentTensor leftLength rightLength parentShape)
      (coarse leftLength rightLength hleft) (h, u) =
      Tensor.product (leftTensor (F := F) leftLength (h, u))
        (rightTensor rightLength parentShape (h, u)) := by
  have hadd : shapeNat u + (parentShape h - shapeNat u) = parentShape h := by
    funext s
    exact Nat.add_sub_of_le (hu s)
  funext x y z
  have hs := shape_split (F := F) (P := Fin (leftLength h))
    (Q := Fin (rightLength h)) (shapeNat u) (parentShape h - shapeNat u) x y z
  rw [hadd] at hs
  simpa [block, parentTensor, coarse, CWCoarseIndices.coarseIndex,
    Fin.ext_iff, leftTensor, rightTensor, shapeNat, shapeSide,
    Fin.isValue, ↓reduceIte] using hs

omit [DecidableEq H] in
theorem canonicalBase_eq_children
    (hsupport : ∀ h u, 0 < counts h u → ∀ s, shapeNat u s ≤ parentShape h s) :
    canonicalBase counts (Left leftLength) (Right rightLength)
      (parentTensor leftLength rightLength parentShape)
      (coarse leftLength rightLength hleft) =
      pairClassProduct (leftTensor (F := F) leftLength)
        (rightTensor rightLength parentShape) := by
  funext x y z
  unfold canonicalBase
  have hf : (∏ c : ClassKey (H := H), ∏ j : ClassPositions counts c,
      block (Left leftLength) (Right rightLength)
        (parentTensor leftLength rightLength parentShape)
        (coarse leftLength rightLength hleft) c
        (x.left c j, x.right c j) (y.left c j, y.right c j) (z.left c j, z.right c j)) =
      ∏ c : ClassKey (H := H), ∏ j : ClassPositions counts c,
        (leftTensor (F := F) leftLength c (x.left c j) (y.left c j) (z.left c j) *
          rightTensor rightLength parentShape c (x.right c j) (y.right c j) (z.right c j)) := by
    apply Finset.prod_congr rfl
    intro c _
    apply Finset.prod_congr rfl
    intro j _
    have hc : 0 < counts c.1 c.2 := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
    rw [block_eq_product leftLength rightLength parentShape hleft c.1 c.2
      (hsupport c.1 c.2 hc)]
    rfl
  rw [hf]
  simp only [pairClassProduct, classProduct, Finset.prod_mul_distrib]

abbrev RawStrands := ∀ h, Positions counts h →
  ((Fin (leftLength h) ⊕ Fin (rightLength h)) → Fin 7)

def rawParentSource : Tensor F (RawStrands counts leftLength rightLength)
    (RawStrands counts leftLength rightLength) (RawStrands counts leftLength rightLength) :=
  classProduct (fun h => shapeTensor (Fin (leftLength h) ⊕ Fin (rightLength h)) (parentShape h))

def joinWords (w : RawPairs counts (Left leftLength) (Right rightLength)) :
    RawStrands counts leftLength rightLength :=
  fun h i => Sum.elim (w h i).1 (w h i).2

def joinMatrix : RawPairs counts (Left leftLength) (Right rightLength) →
    RawStrands counts leftLength rightLength → F :=
  fun w v => if v = joinWords counts leftLength rightLength w then 1 else 0

theorem parentTensor_restrict :
    Tensor.restrict (joinMatrix (F := F) counts leftLength rightLength)
      (joinMatrix counts leftLength rightLength) (joinMatrix counts leftLength rightLength)
      (rawParentSource counts leftLength rightLength parentShape) =
      sourceTensor counts (Left leftLength) (Right rightLength)
        (parentTensor leftLength rightLength parentShape) := by
  classical
  funext x y z
  simp [Tensor.restrict, joinMatrix, rawParentSource, sourceTensor,
    classProduct, joinWords, parentTensor, ite_mul, mul_ite]

end MatrixMultiplication.JointCanonicalCW

end

end OAI
