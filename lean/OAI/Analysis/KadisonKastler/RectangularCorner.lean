import Mathlib.Analysis.CStarAlgebra.CStarMatrix

namespace OAI

/-!
# Isometric square corners of rectangular C⋆-matrices

The upper-right corner embeds a rectangular matrix into a square matrix
without changing its operator norm. We prove this directly on the finite
Hilbert C⋆-modules that define the matrix norms.
-/

namespace KadisonKastler

open scoped WithCStarModule InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {m n : Type*} [Fintype m] [Fintype n]

/-- Extension by zero into the left summand of a finite Hilbert C⋆-module. -/
def moduleExtendLeft (x : C⋆ᵐᵒᵈ(A, m → A)) : C⋆ᵐᵒᵈ(A, (m ⊕ n) → A) :=
  (WithCStarModule.equiv _ _).symm (Sum.elim x fun _ => 0)

/-- Extension by zero into the right summand. -/
def moduleExtendRight (x : C⋆ᵐᵒᵈ(A, n → A)) : C⋆ᵐᵒᵈ(A, (m ⊕ n) → A) :=
  (WithCStarModule.equiv _ _).symm (Sum.elim (fun _ => 0) x)

/-- Restriction to the left summand. -/
def moduleRestrictLeft (x : C⋆ᵐᵒᵈ(A, (m ⊕ n) → A)) : C⋆ᵐᵒᵈ(A, m → A) :=
  (WithCStarModule.equiv _ _).symm (fun i => x (Sum.inl i))

@[simp]
theorem norm_moduleExtendLeft (x : C⋆ᵐᵒᵈ(A, m → A)) :
    ‖moduleExtendLeft (n := n) x‖ = ‖x‖ := by
  simp [WithCStarModule.pi_norm, moduleExtendLeft, Fintype.sum_sum_type,
    WithCStarModule.inner_def, Sum.elim]

@[simp]
theorem norm_moduleExtendRight (x : C⋆ᵐᵒᵈ(A, n → A)) :
    ‖moduleExtendRight (m := m) x‖ = ‖x‖ := by
  simp [WithCStarModule.pi_norm, moduleExtendRight, Fintype.sum_sum_type,
    WithCStarModule.inner_def, Sum.elim]

theorem norm_moduleRestrictLeft_le (x : C⋆ᵐᵒᵈ(A, (m ⊕ n) → A)) :
    ‖moduleRestrictLeft x‖ ≤ ‖x‖ := by
  simp only [WithCStarModule.pi_norm, moduleRestrictLeft,
    WithCStarModule.equiv_symm_pi_apply, Fintype.sum_sum_type]
  apply Real.sqrt_le_sqrt
  apply CStarAlgebra.norm_le_norm_of_le_of_nonneg
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
      CStarModule.inner_self_nonneg)
  · exact Finset.sum_nonneg fun i _ => CStarModule.inner_self_nonneg

/-- A rectangular matrix as an upper-right corner of a square matrix. -/
def rectangularCorner (X : CStarMatrix m n A) :
    CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  fun i j =>
    match i, j with
    | Sum.inl i, Sum.inr j => X i j
    | _, _ => 0

omit [PartialOrder A] [StarOrderedRing A] in
theorem rectangularCorner_toCLM (X : CStarMatrix m n A)
    (x : C⋆ᵐᵒᵈ(A, (m ⊕ n) → A)) :
    CStarMatrix.toCLM (rectangularCorner X) x =
      moduleExtendRight (CStarMatrix.toCLM X (moduleRestrictLeft x)) := by
  ext j
  rcases j with j | j <;>
    simp [CStarMatrix.toCLM_apply_eq_sum, rectangularCorner, moduleExtendRight,
      moduleRestrictLeft, Fintype.sum_sum_type, Sum.elim]

/-- The square-corner embedding preserves the rectangular operator norm. -/
theorem norm_rectangularCorner (X : CStarMatrix m n A) :
    ‖rectangularCorner X‖ = ‖X‖ := by
  apply le_antisymm
  · change ‖CStarMatrix.toCLM (rectangularCorner X)‖ ≤ ‖X‖
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg X)
    intro x
    rw [rectangularCorner_toCLM, norm_moduleExtendRight]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_moduleRestrictLeft_le x) (norm_nonneg X))
  · change ‖CStarMatrix.toCLM X‖ ≤ ‖rectangularCorner X‖
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := ContinuousLinearMap.le_opNorm (CStarMatrix.toCLM (rectangularCorner X))
      (moduleExtendLeft (n := n) x)
    rw [rectangularCorner_toCLM, norm_moduleExtendRight, norm_moduleExtendLeft] at h
    exact h

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype n]
  [PartialOrder B] [StarOrderedRing B] in
theorem rectangularCorner_map (F : A →ₗ[ℂ] B) (X : CStarMatrix m n A) :
    rectangularCorner (CStarMatrix.mapₗ F X) =
      CStarMatrix.mapₗ F (rectangularCorner X) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [rectangularCorner]

end

end KadisonKastler

end OAI
