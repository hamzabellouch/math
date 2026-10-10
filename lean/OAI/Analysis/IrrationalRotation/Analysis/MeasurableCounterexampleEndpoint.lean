import OAI.Analysis.IrrationalRotation.Rotation.CircleMeasurableObstruction
import OAI.Analysis.IrrationalRotation.Analysis.ParameterOrbitIdentity
import OAI.Analysis.IrrationalRotation.Rotation.RotationHilbert

namespace OAI

noncomputable section
namespace Invariant233

theorem measurable_counterexample_proof (θ : ℝ)
    (_hθ0 : 0 < θ) (_hθ1 : θ < 1) (hθ : Irrational θ)
    (p : CircleParameterData) (hp : CircleParameterLaws θ p) :
    p.measurableOperator θ hp ∈ Rotation.algebra θ ∧
      ∀ P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert,
        P ∈ Rotation.algebra θ → IsStarProjection P →
        0 < (Rotation.vacuumFunctional P).re →
        (Rotation.vacuumFunctional P).re < 1 →
        (1 - P) * p.measurableOperator θ hp * P ≠ 0 := by
  refine ⟨hp.measurableOperator_mem_algebra, ?_⟩
  intro P hmem hP htrace0 htrace1 hinv
  rcases hp.measurableOperator_hasOnlyTrivialInvariantProjections hθ P hmem hP hinv
    with hzero | hone
  · subst P
    simp [Rotation.vacuumFunctional] at htrace0
  · subst P
    simp [Rotation.vacuumFunctional_one] at htrace1

end Invariant233

end

end OAI
