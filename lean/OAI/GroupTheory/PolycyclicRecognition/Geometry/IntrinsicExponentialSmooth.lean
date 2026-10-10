import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicTriangularRealization
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothFaithfulRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraRepresentationDerivative

namespace OAI

/-! # Smoothness of the intrinsic real triangular exponential

The inducing representation first proves continuity. Smooth cancellation
then recovers the actual manifold regularity from the matrix exponential.
No global exponential chart is used.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

theorem intrinsic_exponential_contMDiff
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : E => Exp x) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨m, _, j, ρ, hj, hu, _, hρ, _, he⟩ :=
    exists_intrinsic_faithful_triangular_representation T Exp hExp
  have hind := intrinsic_triangular_representation_inducing T Exp hExp j hj hu ρ hρ he
  let J : E →L[ℝ] Matrix (Fin m) (Fin m) ℝ := j.toLinearMap.toContinuousLinearMap
  have hcoords (x : E) : (ρ (Exp x) : Matrix (Fin m) (Fin m) ℝ) =
      NormedSpace.exp (J x) := by
    exact congrArg Units.val (he x)
  have hc : Continuous (fun x : E => Exp x) := by
    apply hind.continuous_iff.mpr
    change Continuous (fun x : E => (ρ (Exp x) : Matrix (Fin m) (Fin m) ℝ))
    rw [show (fun x : E => (ρ (Exp x) : Matrix (Fin m) (Fin m) ℝ)) =
      (fun x => NormedSpace.exp (J x)) from funext hcoords]
    exact NormedSpace.exp_continuous.comp J.continuous
  have hsρ := contMDiff_of_continuous_unitsHom hExp ρ (Units.continuous_val.comp hρ)
  have hjρ : unitsHomLieDifferential ρ hsρ = j := by
    apply LieHom.ext
    intro x
    apply unitsHomLieDifferential_eq_of_exponential_line hExp ρ hsρ x (j x)
    intro t
    simpa only [map_smul] using he (t • x)
  have hdρ := hasMFDerivAt_unitsHomLieDifferential ρ hsρ
  rw [hjρ] at hdρ
  have hreg : ContDiff ℝ ∞ (fun y : E => NormedSpace.exp (J y)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (NormedSpace.exp_analytic (𝕂 := ℝ) (J x)).contDiffAt.comp x J.contDiff.contDiffAt
  have hscomp := hreg.contMDiff
  rw [← show (fun x : E => (ρ (Exp x) : Matrix (Fin m) (Fin m) ℝ)) =
    (fun x => NormedSpace.exp (J x)) from funext hcoords] at hscomp
  intro x
  exact contMDiffAt_of_unitsHom_injective_differential ρ hsρ J hdρ hj
    hc.continuousAt (hscomp x)

end PolycyclicRecognition

end

end OAI
