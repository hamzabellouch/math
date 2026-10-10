import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationFactorAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTangentConjugation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FactorExponentialOverlap
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentAlgebraRepresentation

namespace OAI

/-! # Relations between the integrated representations of the two factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem forall_of_two_surjections {X Y N D : Type*}
    (f : X → N) (g : Y → D) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (P : N → D → Prop) (hP : ∀ x y, P (f x) (g y)) : ∀ n d, P n d := by
  intro n d
  obtain ⟨x,rfl⟩ := hf n
  obtain ⟨y,rfl⟩ := hg d
  exact hP x y

variable {E G A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
  (j : CartanRealShadow T H →ₗ⁅ℝ⁆ A)
  (ρN : F.N.carrier →* Aˣ) (ρD : F.D.carrier →* Aˣ)
  (hN : ∀ x : T.kernelIdeal, ρN (F.ExpN (F.N.equiv x)) =
    algebraExpUnit (j (cartanRealShadowEquiv T H x)))
  (hD : ∀ h : H, ρD (F.ExpD (F.D.equiv h)) =
    algebraExpUnit (j (cartanRealShadowEquiv T H h)))
attribute [local instance] semidirectProductTopology

include hN hD in
theorem rotationRepresentation_conjugation :
    ∀ d n, ρN (F.rotationFactorAction hExp d n) = ρD d * ρN n * (ρD d)⁻¹ := by
  apply forall_of_two_surjections (fun h : H => F.ExpD (F.D.equiv h))
    (fun x : T.kernelIdeal => F.ExpN (F.N.equiv x)) F.expD_surjective F.expN_surjective
  intro h x
  rw [F.rotationFactorAction_exponential hExp, hN, hD, hN]
  have he := realShadow_representation_rotated_adjoint T H hExp j h x
  change j (cartanRealShadowEquiv T H
    ((T.nilradicalRotation H (realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H h)⁻¹
      ⟨adjointLinearMap (E := E) (Exp h) (x : GroupLieAlgebra (𝓘(ℝ,E)) G),
        cartan_conjugation_mem hExp h x⟩) : GroupLieAlgebra (𝓘(ℝ,E)) G)) = _ at he
  rw [he]
  exact algebraExpUnit_conj (algebraExpUnit (j (cartanRealShadowEquiv T H h)))
    (j (cartanRealShadowEquiv T H x))

include hN hD in
theorem rotationRepresentation_overlap (n : F.N.carrier) (d : F.D.carrier)
    (he : F.nilpotentFactorToRotation hExp n = F.cartanFactorToRotation hExp d) :
    ρN n = ρD d := by
  have hg := congrArg (F.smoothRotationalModificationHomeomorph hExp) he
  change F.inclusionN n = F.inclusionD d at hg
  obtain ⟨x,hx,hy,hn,hd⟩ := F.factor_overlap_coordinates n d hg
  rw [hn, hd, hN, hD]

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
