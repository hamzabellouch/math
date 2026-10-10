import OAI.Dynamics.EntropyCounterexample.AmbientPrediction
import OAI.Dynamics.EntropyCounterexample.SphereDoublingCharts
import OAI.Dynamics.EntropyCounterexample.Map
import OAI.Dynamics.EntropyCounterexample.SphereCutoffTransport

namespace OAI

noncomputable section
open scoped OnePoint

namespace Problem340

theorem ambientClockGate_model_eq (z : OnePoint ℂ) :
    SphereCutoffs.clockGateAmbient (complexSphereHomeomorph z).val =
      SphereCutoffs.onePointClockGate z :=
  SphereCutoffs.clockGate_complexSphereHomeomorph z

namespace PredictionModelBridge

def modelEmbedding (x : ℝ × OnePoint ℂ) : AmbientPrediction.Ambient :=
  (x.1, (complexSphereHomeomorph x.2).val)

theorem modelEmbedding_mem_cylinder (x : ℝ × OnePoint ℂ) :
    modelEmbedding x ∈ AmbientPrediction.cylinder :=
  ⟨Set.mem_univ _, (complexSphereHomeomorph x.2).property⟩

theorem semiconj_prediction (D : Construction.SphereData)
    (hgate : D.gate = SphereCutoffs.onePointClockGate) :
    Function.Semiconj modelEmbedding (Construction.prediction D)
      AmbientPrediction.predictor := by
  intro x
  apply Prod.ext
  · simp [modelEmbedding, Construction.prediction, AmbientPrediction.predictor,
      hgate, ambientClockGate_model_eq]
  · simpa [modelEmbedding, Construction.prediction, AmbientPrediction.predictor,
      perturbedSquare, SphereDoubling.sphereMap] using
      congrArg Subtype.val (sphereDoubling_complexSphereHomeomorph x.2).symm

theorem predictedClock_eq (D : Construction.SphereData)
    (hgate : D.gate = SphereCutoffs.onePointClockGate)
    (m : ℕ) (t : ℝ) (z : OnePoint ℂ) :
    Construction.predictedClock D m t z =
      AmbientPrediction.clockPrediction m (modelEmbedding (t, z)) := by
  exact congrArg Prod.fst ((semiconj_prediction D hgate).iterate_right m (t, z))

def affineEmbedding (x : ℝ × ℂ) : AmbientPrediction.Ambient :=
  (x.1, (sphereOfComplex x.2).val)

theorem contDiff_affineEmbedding {n : ℕ∞} : ContDiff ℝ n affineEmbedding :=
  contDiff_fst.prodMk (contDiff_sphereOfComplex_val.comp contDiff_snd)

theorem affineEmbedding_mem_cylinder (x : ℝ × ℂ) :
    affineEmbedding x ∈ AmbientPrediction.cylinder :=
  ⟨Set.mem_univ _, (sphereOfComplex x.2).property⟩

theorem predictedClock_affine_eq (D : Construction.SphereData)
    (hgate : D.gate = SphereCutoffs.onePointClockGate) (m : ℕ) :
    (fun x : ℝ × ℂ => Construction.predictedClock D m x.1 (x.2 : OnePoint ℂ)) =
      (AmbientPrediction.clockPrediction m) ∘ affineEmbedding := by
  funext x
  exact predictedClock_eq D hgate m x.1 (x.2 : OnePoint ℂ)

theorem contDiff_predictedClock_affine (D : Construction.SphereData)
    (hgate : D.gate = SphereCutoffs.onePointClockGate) (m : ℕ) {n : ℕ∞} :
    ContDiff ℝ n
      (fun x : ℝ × ℂ => Construction.predictedClock D m x.1 (x.2 : OnePoint ℂ)) := by
  rw [predictedClock_affine_eq D hgate m]
  exact (AmbientPrediction.contDiff_clockPrediction m).comp contDiff_affineEmbedding

theorem exists_predictedClock_affine_derivative_bound
    (D : Construction.SphereData) (hgate : D.gate = SphereCutoffs.onePointClockGate) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ K : Set (ℝ × ℂ), IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m x, x ∈ K →
        ‖fderiv ℝ (fun y : ℝ × ℂ =>
          Construction.predictedClock D m y.1 (y.2 : OnePoint ℂ)) x‖ ≤ B ^ m * C := by
  obtain ⟨B, hB, hbound⟩ := AmbientPrediction.exists_clockPrediction_derivative_bound
  refine ⟨B, hB, ?_⟩
  intro K hK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((contDiff_affineEmbedding (n := 1)).continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro m x hx
  rw [predictedClock_affine_eq D hgate m]
  exact AmbientPrediction.norm_fderiv_clockPrediction_chart_le
    (by linarith) hbound
    ((contDiff_affineEmbedding (n := 1)).differentiable one_ne_zero x)
    (affineEmbedding_mem_cylinder x) ((hC x hx).trans (le_max_right _ _)) m

end PredictionModelBridge

end Problem340

end

end OAI
