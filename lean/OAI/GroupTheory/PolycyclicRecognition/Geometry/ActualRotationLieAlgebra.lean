import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationalTwistBracket
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FactorPhaseOperatorDerivative
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IndividualRotationDerivative
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothRotationExtension
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealShadowSplit
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularAdjointTransport

namespace OAI

/-! # The Lie algebra of the actual smooth rotational modification -/

noncomputable section
namespace PolycyclicRecognition
open VectorField
open scoped Manifold ContDiff

private theorem unitsHom_inverse_one {M K A : Type*} [Monoid M] [Group K] [Monoid A]
    (q : M →* K) (ρ : K →* Aˣ) : (ρ ((q 1)⁻¹) : A) = 1 := by
  simp only [map_one, inv_one, Units.val_one]

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

private theorem tangent_shadow_triangular :
    ∃ m : ℕ, Nonempty (TriangularAdjoint (CartanRealShadow T H) m) :=
  nonempty_cartanRealShadow_triangularAdjoint T H

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology
local instance : ChartedSpace E (F.SmoothRotationalModification hExp) :=
  F.smoothRotationalModificationChartedSpace hExp
local instance : LieGroup (𝓘(ℝ,E)) ∞ (F.SmoothRotationalModification hExp) :=
  F.smoothRotationalModificationLieGroup hExp
local instance : LieGroup (𝓘(ℝ,E)) (minSmoothness ℝ 3) (F.SmoothRotationalModification hExp) :=
  LieGroup.of_le (n := ∞) (by simp)

theorem smoothRotationalModification_bracket (v w : E) :
    (show E from mlieBracket (𝓘(ℝ,E))
      (mulInvariantVectorField (I := 𝓘(ℝ,E)) (G := F.SmoothRotationalModification hExp) v)
      (mulInvariantVectorField (I := 𝓘(ℝ,E)) (G := F.SmoothRotationalModification hExp) w) 1) =
    (cartanRealShadowEquiv T H).symm
      ⁅cartanRealShadowEquiv T H v,cartanRealShadowEquiv T H w⁆ := by
  let : Fact (Continuous F.rotationCharacter) := ⟨F.continuous_rotationCharacter⟩
  let R : G → E →L[ℝ] E := fun g => tangentTorusUnitAction H ((F.rotationCharacter g)⁻¹)
  let q := invMonoidHom.comp F.rotationCharacter
  have hR : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E →L[ℝ] E)) ∞ R :=
    contMDiff_tangentTorusRepresentation H hExp q F.continuous_rotationCharacter.inv
  have hR₀ : R 1 = ContinuousLinearMap.id ℝ E := by
    exact unitsHom_inverse_one F.rotationCharacter (tangentTorusUnitAction H)
  have hRd (g : G) (x : E) :
      mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E))
        (F.factorCompactRotationAction hExp ((F.rotationCharacter g)⁻¹)) 1 x = R g x :=
    F.mfderiv_individual_rotation hExp (F.factorCompactRotationAction hExp)
      (F.factorCompactRotationAction_formula hExp) ((F.rotationCharacter g)⁻¹) x
  have hb := rotationalTwist_bracket (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp)
    (F.contMDiff_inverse_factorCompactRotationAction hExp) R hR hR₀ hRd v w
  have hv := F.mfderiv_inverse_factorPhase_operator hExp v w
  have hw := F.mfderiv_inverse_factorPhase_operator hExp w v
  let B : E := mlieBracket (𝓘(ℝ,E))
    (mulInvariantVectorField (I := 𝓘(ℝ,E)) (G := G) v)
    (mulInvariantVectorField (I := 𝓘(ℝ,E)) (G := G) w) 1
  have hc := congrArg₂ (fun s t : E => B + s - t) hv hw
  have hs : (cartanRealShadowEquiv T H).symm
      ⁅cartanRealShadowEquiv T H v,cartanRealShadowEquiv T H w⁆ =
      B - (show E from T.weightImaginaryAction H v w) +
        (show E from T.weightImaginaryAction H w v) :=
    cartanRealShadow_bracket T H v w
  have halg : B + -(show E from T.weightImaginaryAction H v w) -
        -(show E from T.weightImaginaryAction H w v) =
      B - (show E from T.weightImaginaryAction H v w) +
        (show E from T.weightImaginaryAction H w v) := by abel
  exact hb.trans (hc.trans (halg.trans hs.symm))

/-- The actual graph has the real-shadow bracket in its original tangent coordinates. -/
def smoothRotationalModificationLieEquiv :
    GroupLieAlgebra (𝓘(ℝ,E)) (F.SmoothRotationalModification hExp) ≃ₗ⁅ℝ⁆ CartanRealShadow T H where
  __ := (cartanRealShadowEquiv T H :
    GroupLieAlgebra (𝓘(ℝ,E)) G ≃ₗ[ℝ] CartanRealShadow T H)
  map_lie' {x y} := by
    apply (cartanRealShadowEquiv T H).symm.injective
    change mlieBracket (𝓘(ℝ,E))
      (mulInvariantVectorField (I := 𝓘(ℝ,E)) (G := F.SmoothRotationalModification hExp) x)
      (mulInvariantVectorField (I := 𝓘(ℝ,E)) (G := F.SmoothRotationalModification hExp) y) 1 = _
    exact F.smoothRotationalModification_bracket hExp x y

/-- The simultaneous real triangular basis belongs to the actual graph Lie algebra. -/
theorem smoothRotationalModification_triangularAdjoint :
    ∃ m : ℕ, Nonempty
      (TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) (F.SmoothRotationalModification hExp)) m) := by
  exact nonempty_triangularAdjoint_of_lieEquiv
    (F.smoothRotationalModificationLieEquiv hExp)
    (tangent_shadow_triangular (T := T) (H := H))

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
