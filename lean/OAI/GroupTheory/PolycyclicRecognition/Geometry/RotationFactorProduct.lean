import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationFactorLifts

namespace OAI

/-! # Global factor coordinates for the actual rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

private theorem surjective_of_coordinates {A X Y : Type*} (e : X → Y)
    (he : Function.Injective e) (f : A → X) (g : A → Y)
    (hf : ∀ a, e (f a) = g a) (hg : Function.Surjective g) : Function.Surjective f := by
  intro x
  obtain ⟨a,ha⟩ := hg (e x)
  exact ⟨a, he ((hf a).trans ha)⟩

private theorem rotationalTwistLift_mul_left {A G K : Type*}
    [Group A] [Group G] [CommGroup K] [TopologicalSpace G] [TopologicalSpace K]
    (α : K →* MulAut G) (τ : G →* K) (hinv : ∀ k g, τ (α k g) = τ g)
    (f : A →* G) (hfix : ∀ a b, α ((τ (f a))⁻¹) (f b) = f b)
    (a : A) (p : rotationalTwist α τ hinv) (ha : τ (f a) = 1) :
    (rotationalTwistLift α τ hinv f hfix a * p).val.left = f a * p.val.left := by
  change f a * α ((τ (f a))⁻¹) p.val.left = _
  rw [ha, inv_one, map_one]
  rfl

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

theorem rotationFactorProduct_coordinates (n : F.N.carrier) (d : F.D.carrier) :
    F.smoothRotationalModificationHomeomorph hExp
      (F.nilpotentFactorToRotation hExp n * F.cartanFactorToRotation hExp d) =
        F.inclusionN n * F.inclusionD d :=
  rotationalTwistLift_mul_left _ _ _ _ _ n _ (F.rotationCharacter_inclusionN n)

theorem rotationFactorProduct_surjective :
    Function.Surjective (fun p : F.N.carrier × F.D.carrier =>
      F.nilpotentFactorToRotation hExp p.1 * F.cartanFactorToRotation hExp p.2) := by
  exact surjective_of_coordinates (F.smoothRotationalModificationHomeomorph hExp)
    (F.smoothRotationalModificationHomeomorph hExp).injective _ _
    (fun p => F.rotationFactorProduct_coordinates hExp p.1 p.2) F.surjective

theorem closedEmbedding_nilpotentFactorToRotation :
    Topology.IsClosedEmbedding (F.nilpotentFactorToRotation hExp) :=
  Topology.IsClosedEmbedding.of_comp
    (F.smoothRotationalModificationHomeomorph hExp).isEmbedding F.closedN

theorem closedEmbedding_cartanFactorToRotation :
    Topology.IsClosedEmbedding (F.cartanFactorToRotation hExp) :=
  Topology.IsClosedEmbedding.of_comp
    (F.smoothRotationalModificationHomeomorph hExp).isEmbedding F.closedD

theorem rotationFactorProduct_open :
    IsOpenMap (fun p : F.N.carrier × F.D.carrier =>
      F.nilpotentFactorToRotation hExp p.1 * F.cartanFactorToRotation hExp p.2) := by
  let e := F.smoothRotationalModificationHomeomorph hExp
  have he : (fun p : F.N.carrier × F.D.carrier =>
      F.nilpotentFactorToRotation hExp p.1 * F.cartanFactorToRotation hExp p.2) =
      e.symm ∘ (fun p : F.N.carrier × F.D.carrier => F.inclusionN p.1 * F.inclusionD p.2) := by
    funext p
    apply e.injective
    exact (F.rotationFactorProduct_coordinates hExp p.1 p.2).trans (e.apply_symm_apply _).symm
  rw [he]
  exact e.symm.isOpenMap.comp F.openProduct

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
