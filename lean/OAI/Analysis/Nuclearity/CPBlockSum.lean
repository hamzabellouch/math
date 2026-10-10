import OAI.Analysis.PureInfiniteness.TwoMatrixNuclear
import OAI.Analysis.JiangSu.Nuclearity.CompletelyPositiveOperations

namespace OAI

/-! Finite corner maps and sums of completely positive maps used to retain
an independent scalar coordinate in a matrix approximation. -/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {D : Type*} [NonUnitalCStarAlgebra D]

def twoCornerInclusion (i : Fin 2) : D →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) D where
  toFun a := CStarMatrix.ofMatrix (fun j k => if j = i ∧ k = i then a else 0)
  map_zero' := by
    ext j k
    change (if j = i ∧ k = i then (0 : D) else 0) = 0
    split_ifs <;> rfl
  map_add' a b := by
    ext j k
    change (if j = i ∧ k = i then a + b else 0) =
      (if j = i ∧ k = i then a else 0) + (if j = i ∧ k = i then b else 0)
    split_ifs <;> simp
  map_smul' c a := by
    ext j k
    change (if j = i ∧ k = i then c • a else 0) =
      c • (if j = i ∧ k = i then a else 0)
    split_ifs <;> simp
  map_mul' a b := by
    ext j k
    change (if j = i ∧ k = i then a * b else 0) =
      ∑ l, (if j = i ∧ l = i then a else 0) * (if l = i ∧ k = i then b else 0)
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp
  map_star' a := by
    ext j k
    change (if j = i ∧ k = i then star a else 0) =
      star (if k = i ∧ j = i then a else 0)
    by_cases h : j = i ∧ k = i
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · have h' : ¬(k = i ∧ j = i) := by tauto
      simp [h, h']

@[simp] lemma twoCornerInclusion_apply (i : Fin 2) (a : D) (j k : Fin 2) :
    twoCornerInclusion i a j k = if j = i ∧ k = i then a else 0 := rfl

def matrixCornerLinear {n : Type*} [Fintype n] (i : n) : CStarMatrix n n D →L[ℂ] D where
  toFun M := M i i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_apply i).comp (continuous_apply i)

@[simp] lemma matrixCornerLinear_apply {n : Type*} [Fintype n] (i : n)
    (M : CStarMatrix n n D) : matrixCornerLinear i M = M i i := rfl

variable [PartialOrder D] [StarOrderedRing D]

local instance cpBlockOrder {n : Type*} [Fintype n] : PartialOrder (CStarMatrix n n D) :=
  CStarAlgebra.spectralOrder _
local instance cpBlockOrdered {n : Type*} [Fintype n] : StarOrderedRing (CStarMatrix n n D) :=
  CStarAlgebra.spectralOrderedRing _

lemma matrixCornerLinear_cp {n : Type*} [Fintype n] (i : n) :
    CompletelyPositive (matrixCornerLinear (D := D) i) := by
  intro k M hM
  exact (CompletelyPositiveOperations.corner i).map_cstarMatrix_nonneg M hM

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma completelyPositive_add {φ ψ : A →L[ℂ] D} (hφ : CompletelyPositive φ)
    (hψ : CompletelyPositive ψ) : CompletelyPositive (φ + ψ) := by
  intro n M hM
  exact add_nonneg (hφ n M hM) (hψ n M hM)

end WeakPureInfiniteness

end

end OAI
