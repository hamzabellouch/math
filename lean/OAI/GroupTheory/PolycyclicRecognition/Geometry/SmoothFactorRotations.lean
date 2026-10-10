import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothRotationalAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FactorRotationCharacter
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TangentRotationRepresentation

namespace OAI

/-! # Smoothness of the actual compact rotations along their character -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

theorem contMDiff_factorRotation
    (hExp : IsGroupExponential Exp)
    (β : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H →* MulAut G)
    (hβ : ∀ z (x : T.kernelIdeal) d,
      β z (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD d) =
        F.inclusionN (F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) * F.inclusionD d)
    (q : G →* realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H)
    (hq : Continuous q) :
    ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
      (fun p : G × G => β (q p.1) p.2) := by
  let R : G → E →L[ℝ] E := fun g => tangentTorusUnitAction H (q g)
  have hR : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E →L[ℝ] E)) ∞ R :=
    contMDiff_tangentTorusRepresentation H hExp q hq
  exact F.contMDiff_action hExp β hβ q R hR (fun _ _ => rfl)

theorem contMDiff_inverse_factorRotation
    (hExp : IsGroupExponential Exp)
    (β : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H →* MulAut G)
    (hβ : ∀ z (x : T.kernelIdeal) d,
      β z (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD d) =
        F.inclusionN (F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) * F.inclusionD d) :
    ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
      (fun p : G × G => β ((F.rotationCharacter p.1)⁻¹) p.2) := by
  let q := invMonoidHom.comp F.rotationCharacter
  have hq : Continuous q := F.continuous_rotationCharacter.inv
  exact F.contMDiff_factorRotation hExp β hβ q hq

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
