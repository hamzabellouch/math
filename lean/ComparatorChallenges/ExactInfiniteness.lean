import Mathlib

namespace OAI

noncomputable section
universe u v
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
namespace WeakPureInfiniteness

section CompletedOperators

variable {domain codomain : Type*}
  [NormedAddCommGroup domain] [NormedSpace ℂ domain]
  [NormedAddCommGroup codomain] [NormedSpace ℂ codomain]

lemma norm_completion_le (operator : domain →L[ℂ] codomain) :
    ‖operator.completion‖ ≤ ‖operator‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg operator)
  intro vector
  induction vector using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih vector => simpa using operator.le_opNorm vector

lemma norm_completion (operator : domain →L[ℂ] codomain) :
    ‖operator.completion‖ = ‖operator‖ := by
  apply le_antisymm (norm_completion_le operator)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro vector
  simpa using operator.completion.le_opNorm (vector : Completion domain)

end CompletedOperators

structure ComplexHilbert where
  Carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [innerProductSpace : InnerProductSpace ℂ Carrier]
  [completeSpace : CompleteSpace Carrier]

attribute [instance] ComplexHilbert.normedAddCommGroup
  ComplexHilbert.innerProductSpace ComplexHilbert.completeSpace
instance : CoeSort ComplexHilbert.{u} (Type u) := ⟨ComplexHilbert.Carrier⟩

instance completedTensorCStar (H K : ComplexHilbert.{u}) :
    CStarAlgebra (Completion (H ⊗[ℂ] K) →L[ℂ] Completion (H ⊗[ℂ] K)) := inferInstance

instance hilbertOperatorsCStar (H : ComplexHilbert.{u}) :
    CStarAlgebra (H →L[ℂ] H) := inferInstance

structure SpatialRepresentation (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] where
  left : ComplexHilbert.{max u v}
  right : ComplexHilbert.{max u v}
  leftRep : A →⋆ₙₐ[ℂ] (left →L[ℂ] left)
  rightRep : B →⋆ₙₐ[ℂ] (right →L[ℂ] right)

abbrev SpatialRepresentation.hilbert {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (π : SpatialRepresentation A B) : ComplexHilbert.{max u v} where
  Carrier := Completion (π.left ⊗[ℂ] π.right)

abbrev SpatialRepresentation.space {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (π : SpatialRepresentation A B) := Completion (π.left ⊗[ℂ] π.right)

def SpatialAmbient (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] : Type (max u v + 1) :=
  lp (fun π : SpatialRepresentation A B => π.space →L[ℂ] π.space) ∞

instance spatialAmbientCStar (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    NonUnitalCStarAlgebra (SpatialAmbient A B) := by
  unfold SpatialAmbient
  infer_instance

instance spatialAmbientCoeFun (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    CoeFun (SpatialAmbient A B) (fun _ => ∀ π : SpatialRepresentation A B, π.space →L[ℂ] π.space) :=
  ⟨fun z => z.val⟩

def spatialElementary {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (a : A) (b : B) : SpatialAmbient A B :=
  ⟨fun π => (TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion,
    memℓp_infty ⟨‖a‖ * ‖b‖, by
      rintro _ ⟨π, rfl⟩
      dsimp only
      rw [norm_completion]
      exact (TensorProduct.norm_mapL_le _ _).trans
        (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le π.leftRep a) (NonUnitalStarAlgHom.norm_apply_le π.rightRep b)
          (norm_nonneg _) (norm_nonneg _))⟩⟩

def minimalTensorSubalgebra (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    NonUnitalStarSubalgebra ℂ (SpatialAmbient A B) :=
  (NonUnitalStarAlgebra.adjoin ℂ (Set.range fun p : A × B => spatialElementary p.1 p.2)).topologicalClosure

abbrev MinimalTensor (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] := minimalTensorSubalgebra A B

instance (A : Type u) (B : Type v) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    NonUnitalCStarAlgebra (MinimalTensor A B) := by
  letI : IsClosed ((minimalTensorSubalgebra A B : NonUnitalStarSubalgebra ℂ
    (SpatialAmbient A B)) : Set (SpatialAmbient A B)) :=
    isClosed_closure
  exact inferInstance

section Exactness

variable {A : Type u} {C D : Type v}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

def SpatialRepresentation.precompRight (π : SpatialRepresentation A D)
    (q : C →⋆ₙₐ[ℂ] D) : SpatialRepresentation A C where
  left := π.left
  right := π.right
  leftRep := π.leftRep
  rightRep := π.rightRep.comp q

def tensorKernelIdeal (q : C →⋆ₙₐ[ℂ] D) : NonUnitalStarSubalgebra ℂ (SpatialAmbient A C) :=
  (NonUnitalStarAlgebra.adjoin ℂ
    {z | ∃ a : A, ∃ c : C, q c = 0 ∧ z = spatialElementary a c}).topologicalClosure

end Exactness

def Exact (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ (C D : Type u) [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    (q : C →⋆ₙₐ[ℂ] D), Function.Surjective q →
    ∀ z : MinimalTensor A C,
      (∀ π : SpatialRepresentation A D, (z.val : SpatialAmbient A C) (π.precompRight q) = 0) →
      z.val ∈ tensorKernelIdeal (A := A) q

section Definitions

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {m k : Type*} [Fintype m] [Fintype k]

def CuntzSubequiv (a : CStarMatrix m m A) (b : CStarMatrix k k A) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ v : CStarMatrix k m A, ‖v.conjTranspose * b * v - a‖ < ε

def blockSum (a : CStarMatrix m m A) (b : CStarMatrix k k A) :
    CStarMatrix (m ⊕ k) (m ⊕ k) A :=
  CStarMatrix.ofMatrix (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm a) 0 0
    (CStarMatrix.ofMatrix.symm b))

def ProperlyInfinite (a : CStarMatrix m m A) : Prop :=
  CuntzSubequiv (blockSum a a) a

def diagonalCopies (n : ℕ) (a : A) : CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrix (Matrix.diagonal fun _ => a)

variable (A)

def WeaklyPurelyInfinite : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a)

def StronglyPurelyInfinite : Prop :=
  ∀ a b : A, 0 ≤ a → 0 ≤ b → ∀ ε : ℝ, 0 < ε →
    ∃ s t : A, ‖star s * (a * a) * s - a * a‖ < ε ∧
      ‖star t * (b * b) * t - b * b‖ < ε ∧ ‖star s * a * b * t‖ < ε

end Definitions

theorem exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (hA : Exact A) (hW : WeaklyPurelyInfinite A) {a : A} (ha : 0 ≤ a) :
    ProperlyInfinite (diagonalCopies 1 a) := by
  sorry

theorem exact_weaklyPurelyInfinite_stronglyPurelyInfinite
    (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (hExact : Exact A) (hWeak : WeaklyPurelyInfinite A) : StronglyPurelyInfinite A := by
  sorry

end WeakPureInfiniteness

end

end OAI
