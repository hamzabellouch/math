import OAI.MeasureTheory.Falconer.Radial.ProjectionEnergy

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable def sourceNormal (θ : ℝ) : Plane :=
  WithLp.toLp 2 ![-Real.sin θ, Real.cos θ]

theorem inner_sourceNormal (θ : ℝ) (x : Plane) :
    ⟪x, sourceNormal θ⟫ = sourceProjection θ x := by
  simp [sourceNormal, sourceProjection, PiLp.inner_apply, Fin.sum_univ_two]

theorem source_fourier_slice (μ : Measure Plane) [IsFiniteMeasure μ] (θ ξ : ℝ) :
    sourceFourier (projectedMeasure μ θ) ξ = sourceFourier μ (ξ • sourceNormal θ) := by
  simp only [sourceFourier, charFun_apply, projectedMeasure]
  rw [integral_map (by unfold sourceProjection; fun_prop) (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  simp only [inner_smul_right, inner_sourceNormal, Real.inner_apply, smul_eq_mul]
  congr 1
  ring

end PlanarFalconer

end OAI
