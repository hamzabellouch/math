import OAI.GroupTheory.PolycyclicRecognition.Geometry.FactorPhaseDerivative

namespace OAI

/-! # Operator-valued differential of the inverse rotation character -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

section General

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]

theorem mfderiv_clm_evaluate {R : G → E →L[ℝ] E}
    (hR : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E →L[ℝ] E)) R 1) (x v : E) :
    (show E →L[ℝ] E from mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E →L[ℝ] E)) R 1 x) v =
      mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun g => R g v) 1 x := by
  let ev : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E v
  have he : HasMFDerivAt (𝓘(ℝ,E →L[ℝ] E)) (𝓘(ℝ,E)) ev (R 1) ev :=
    ev.hasMFDerivAt
  have hd := (he.comp (1 : G) hR.hasMFDerivAt).mfderiv
  have hv := congrArg (fun A : E →L[ℝ] E => A x) hd
  change (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun g => R g v) 1) x =
    ev (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E →L[ℝ] E)) R 1 x) at hv
  exact hv.symm

end General

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

theorem mfderiv_inverse_factorPhase_operator (hExp : IsGroupExponential Exp)
    (x v : GroupLieAlgebra (𝓘(ℝ,E)) G) :
    (show E →L[ℝ] E from mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E →L[ℝ] E))
      (fun g => (tangentTorusUnitAction H ((F.rotationCharacter g)⁻¹) : E →L[ℝ] E)) 1 x) v =
      -(T.weightImaginaryAction H x v) := by
  let q := invMonoidHom.comp F.rotationCharacter
  have hR : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun g => (tangentTorusUnitAction H (q g) : E →L[ℝ] E)) :=
    contMDiff_tangentTorusRepresentation H hExp q F.continuous_rotationCharacter.inv
  exact (mfderiv_clm_evaluate (hR.mdifferentiableAt (by simp)) x v).trans
    (F.mfderiv_inverse_factorPhase_apply hExp x v)

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
