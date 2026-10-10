import OAI.Analysis.IrrationalRotation.Model.ContinuousCounterexample
import OAI.Analysis.IrrationalRotation.Rotation.CircleParametersExistence
import OAI.Analysis.IrrationalRotation.Rotation.CircleMeasurableObstruction
import OAI.Analysis.IrrationalRotation.Analysis.ContinuousCounterexampleAssembly
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

namespace OAI

/-! The spectral-radius hypothesis and its consequences for prescribed irrational angles. -/

noncomputable section
open Filter
open scoped ENNReal Topology

namespace Invariant233

structure PublishedRotationSpectralInput (θ : ℝ) : Prop where
  radius_zero : ∀ f : C(Circle, ℝ), IsContinuousCircleWeight f →
    spectralRadius ℂ (Rotation.weightedReal θ f) = 0

theorem PublishedRotationSpectralInput.normQuasinilpotent
    {θ : ℝ} (hpub : PublishedRotationSpectralInput θ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    NormQuasinilpotent (Rotation.weightedReal θ f) := by
  have h := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius
    (Rotation.weightedReal θ f)
  rw [hpub.radius_zero f hf] at h
  have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp h
  simpa only [NormQuasinilpotent, Function.comp_def, ENNReal.toReal_zero,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using ht

namespace Results

theorem prescribed_irrational_counterexample_of_published_spectral_input
    (θ : ℝ) (hθ : Irrational θ) (hpub : PublishedRotationSpectralInput θ) :
    ∃ f : C(Circle, ℝ), Rotation.IsContinuousCounterexample θ f := by
  obtain ⟨p, hp⟩ := exists_circle_parameters hθ
  obtain ⟨f, hf, hmem, hinv⟩ :=
    hp.exists_continuous_invariant_weight hθ
      (hp.measurableOperator_hasOnlyTrivialInvariantProjections hθ)
  exact ⟨f, hf, hmem, hinv, Rotation.weightedReal_ne_zero_of_isContinuousCircleWeight θ f hf,
    hpub.normQuasinilpotent f hf, Rotation.weightedReal_vectorDeterminant_zero θ f hf⟩

end Results
end Invariant233

end

end OAI
