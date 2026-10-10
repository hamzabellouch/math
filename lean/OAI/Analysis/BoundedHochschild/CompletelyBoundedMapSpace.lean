import OAI.Analysis.BoundedHochschild.CompletelyBoundedArithmetic

namespace OAI

/-! The complex vector space of completely bounded maps. No completeness or
choice of a particular complete norm is needed for the averaging projection. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma completelyBounded_zero : CompletelyBoundedEstimate (0 : M →L[ℂ] M) 0 := by
  refine ⟨le_rfl, fun n A => ?_⟩
  have he : A.map (0 : M →L[ℂ] M) = 0 := by ext i j; rfl
  rw [he, norm_zero, zero_mul]

lemma completelyBounded_smul (z : ℂ) {T : M →L[ℂ] M} {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) :
    CompletelyBoundedEstimate (z • T) (‖z‖ * C) := by
  refine ⟨mul_nonneg (norm_nonneg z) hT.1, fun n A => ?_⟩
  have he : A.map (z • T) = z • A.map T := by ext i j; rfl
  rw [he, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hT.2 n A) (norm_nonneg z)

lemma completelyBounded_mono {T : M →L[ℂ] M} {C D : ℝ}
    (hT : CompletelyBoundedEstimate T C) (hCD : C ≤ D) : CompletelyBoundedEstimate T D :=
  ⟨hT.1.trans hCD, fun n A => (hT.2 n A).trans
    (mul_le_mul_of_nonneg_right hCD (norm_nonneg A))⟩

def completelyBoundedSubmodule : Submodule ℂ (M →L[ℂ] M) where
  carrier := {T | ∃ C, CompletelyBoundedEstimate T C}
  zero_mem' := ⟨0, completelyBounded_zero⟩
  add_mem' := by
    rintro T U ⟨C, hC⟩ ⟨D, hD⟩
    exact ⟨C+D, completelyBounded_add hC hD⟩
  smul_mem' := by
    rintro z T ⟨C, hC⟩
    exact ⟨‖z‖*C, completelyBounded_smul z hC⟩

abbrev CompletelyBoundedMap (M : Type*) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] :=
  completelyBoundedSubmodule (M := M)

def completelyBoundedBound (T : CompletelyBoundedMap M) : ℝ := Classical.choose T.property

lemma completelyBoundedBound_spec (T : CompletelyBoundedMap M) :
    CompletelyBoundedEstimate T.val (completelyBoundedBound T) := Classical.choose_spec T.property

def cbLeftSandwich (a b : M) (T : CompletelyBoundedMap M) : CompletelyBoundedMap M :=
  ⟨leftSandwichMap a b T.val, _, completelyBounded_leftSandwich a b (completelyBoundedBound_spec T)⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
