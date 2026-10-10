import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace OAI

/-!
# Restricting a bounded representation to a cyclic orbit closure

The representation need not preserve the involution. Its cyclic orbit is
a linear subspace, and its norm closure is invariant under each operator.
-/

namespace KadisonKastler

noncomputable section

variable {A H : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def representationOrbitMap (Φ : A →ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : A →ₗ[ℂ] H where
  toFun a := Φ a ξ
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def representationCyclicSpace (Φ : A →ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : Submodule ℂ H :=
  (representationOrbitMap Φ ξ).range.topologicalClosure

instance representationCyclicSpace_complete [CompleteSpace H] (Φ : A →ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    CompleteSpace (representationCyclicSpace Φ ξ) :=
  inferInstanceAs (CompleteSpace (representationOrbitMap Φ ξ).range.topologicalClosure)

theorem mem_representationCyclicSpace (Φ : A →ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    ξ ∈ representationCyclicSpace Φ ξ := by
  apply Submodule.le_topologicalClosure
  refine ⟨1, ?_⟩
  simp [representationOrbitMap]

theorem representationCyclicSpace_invariant (Φ : A →ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (a : A) {y : H} (hy : y ∈ representationCyclicSpace Φ ξ) :
    Φ a y ∈ representationCyclicSpace Φ ξ := by
  have h : (representationOrbitMap Φ ξ).range.topologicalClosure ≤
      (representationCyclicSpace Φ ξ).comap (Φ a).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨b, rfl⟩
      apply Submodule.le_topologicalClosure
      refine ⟨a * b, ?_⟩
      simp [representationOrbitMap, map_mul, mul_apply_eq_comp]
    · exact (Submodule.isClosed_topologicalClosure _).preimage (Φ a).continuous
  exact h hy

def representationCyclicVector (Φ : A →ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    representationCyclicSpace Φ ξ := ⟨ξ, mem_representationCyclicSpace Φ ξ⟩

def restrictCyclicRepresentation (Φ : A →ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    A →ₐ[ℂ] (representationCyclicSpace Φ ξ →L[ℂ] representationCyclicSpace Φ ξ) where
  toFun a := (Φ a).restrict (fun _ hy => representationCyclicSpace_invariant Φ ξ a hy)
  map_one' := by ext y; simp
  map_mul' a b := by ext y; simp [map_mul, mul_apply_eq_comp]
  map_zero' := by ext y; simp
  map_add' a b := by ext y; simp
  commutes' z := by ext y; simp

@[simp]
theorem restrictCyclicRepresentation_apply (Φ : A →ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (a : A) (y : representationCyclicSpace Φ ξ) :
    (restrictCyclicRepresentation Φ ξ a y).val = Φ a y.val := rfl

theorem restrictCyclicRepresentation_cyclic (Φ : A →ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    Dense (Set.range (fun a =>
      restrictCyclicRepresentation Φ ξ a (representationCyclicVector Φ ξ))) := by
  intro y
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨z, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp y.property ε hε
  exact ⟨restrictCyclicRepresentation Φ ξ a (representationCyclicVector Φ ξ),
    ⟨a, rfl⟩, ha⟩

theorem norm_restrictCyclicRepresentation_le (Φ : A →ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (a : A) : ‖restrictCyclicRepresentation Φ ξ a‖ ≤ ‖Φ a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  exact (Φ a).le_opNorm x.val

end

end KadisonKastler

end OAI
