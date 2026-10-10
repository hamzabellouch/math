import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.CubeCaps
import OAI.Probability.MemoryPrecision.PriorMeasurability

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

def CubeSphere {d : ℕ} (hd : 2 ≤ d) (u : Cube d) : UnitSphere d :=
  ⟨CubeEmbedding d u, by simpa [Metric.mem_sphere, dist_zero_right] using cubeEmbedding_norm hd u⟩
lemma cubeSphere_measurable {d : ℕ} (hd : 2 ≤ d) : Measurable (CubeSphere hd) :=
  (cubeEmbedding_measurable d).subtype_mk

def CubeSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (hd : 2 ≤ d) (ε : ℝ) : ℝ≥0∞ :=
  ((CubeLaw d).prod (ρ.prod (sampleLaw d T)))
    {z | Learner.angularError (CubeSphere hd z.1)
      (L.estimate (CubeSphere hd z.1) z.2.1 z.2.2) ≤ ε}
def CubeAmbient (d : ℕ) : Measure (Space d) := (CubeLaw d).map (CubeEmbedding d)
instance (d : ℕ) : IsProbabilityMeasure (CubeAmbient d) :=
  inferInstanceAs (IsProbabilityMeasure ((CubeLaw d).map (CubeEmbedding d)))

lemma cubeAmbient_support {d : ℕ} (hd : 2 ≤ d) : (CubeAmbient d).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  rw [mem_ae_iff, CubeAmbient, Measure.map_apply (cubeEmbedding_measurable d)
    Metric.isClosed_closedBall.measurableSet.compl]
  have he : CubeEmbedding d ⁻¹' (Metric.closedBall (0:Space d) 1)ᶜ = ∅ := by
    ext u
    simp [cubeEmbedding_norm hd, Metric.mem_closedBall, dist_zero_right]
  rw [he, measure_empty]

lemma cubeAmbient_polynomial {d : ℕ} (hd : 2 ≤ d) :
    PolynomialMass (CubeAmbient d) (d/2) (ENNReal.ofReal ((12:ℝ)^(d/2))) := by
  intro x r hr
  rw [CubeAmbient, Measure.map_apply (cubeEmbedding_measurable d) Metric.isClosed_closedBall.measurableSet]
  have hsub : CubeEmbedding d ⁻¹' Metric.closedBall x r ⊆
      CubeBall d (Real.sqrt (d/2:ℕ) • cubeProject d x) r := by
    intro u hu
    exact (cubeProject_parameter_dist hd u x).trans
      (mul_le_mul_of_nonneg_left hu (Real.sqrt_nonneg _))
  exact ((measure_mono hsub).trans (cubeBall_volume d _ hr)).trans_eq (ENNReal.ofReal_mul (by positivity))

lemma cube_observation_quasi {d : ℕ} (hd : 16 ≤ d) :
    Measure.QuasiMeasurePreserving
      (fun z : Cube d × Space d => (z.2,⟪CubeEmbedding d z.1,z.2⟫))
      ((CubeLaw d).prod (stdGaussian (Space d))) (observationReference d) := by
  have hac : projectionLaw (CubeAmbient d) 1 ≪ matrixLabelReference (E := Space d) 1 := by
    apply projectionLaw_absolutelyContinuous (cubeAmbient_polynomial (by omega : 2 ≤ d))
      (C := ENNReal.ofReal ((12:ℝ)^(d/2))) (n := 1)
    · positivity
    · exact ENNReal.ofReal_ne_top
    · exact cubeAmbient_support (by omega)
    · omega
    · omega
  have hp : Measure.QuasiMeasurePreserving
      (fun z : (Fin 1 → Space d) × Space d => (z.1,fun j => ⟪z.2,z.1 j⟫))
      ((Measure.pi (fun _ : Fin 1 => stdGaussian (Space d))).prod (CubeAmbient d))
      (matrixLabelReference (E := Space d) 1) := ⟨by fun_prop,hac⟩
  have h1 := ((measurePreserving_funUnique (stdGaussian (Space d)) (Fin 1)).symm
      (MeasurableEquiv.funUnique (Fin 1) (Space d))).prod
    ((cubeEmbedding_measurable d).measurePreserving (CubeLaw d))
  have h2 := (measurePreserving_funUnique (stdGaussian (Space d)) (Fin 1)).prod
    (volume_preserving_funUnique (Fin 1) ℝ)
  have h3 := h2.quasiMeasurePreserving.comp (hp.comp (h1.quasiMeasurePreserving.comp
    Measure.measurePreserving_swap.quasiMeasurePreserving))
  convert h3 using 1
  · ext z <;> simp [MeasurableEquiv.funUnique]
  · rfl

lemma cube_sample_observation_quasi {d T : ℕ} (hd : 16 ≤ d) (i : Fin T) :
    Measure.QuasiMeasurePreserving
      (fun z : Cube d × Samples d T => (z.2 i,⟪CubeEmbedding d z.1,z.2 i⟫))
      ((CubeLaw d).prod (sampleLaw d T)) (observationReference d) := by
  exact (cube_observation_quasi hd).comp
    ((MeasurePreserving.id (CubeLaw d)).prod
      (measurePreserving_eval (fun _ : Fin T => stdGaussian (Space d)) i)).quasiMeasurePreserving

lemma cube_estimate_aemeasurable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 16 ≤ d) :
    AEMeasurable (fun z : Cube d × (Ω × Samples d T) =>
      L.estimate (CubeSphere (by omega) z.1) z.2.1 z.2.2)
      ((CubeLaw d).prod (ρ.prod (sampleLaw d T))) :=
  prior_estimate_aemeasurable (CubeLaw d) ρ (CubeSphere (by omega)) L hL
    (cube_sample_observation_quasi hd)

end MemoryPrecision


end

end OAI
