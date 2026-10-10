import OAI.MeasureTheory.Falconer.Measures.WeakApproximation
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.LiminfLimsup

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable def sourceArcLength : Measure UnitCircle :=
  (volume.restrict (Ioc 0 (2*Real.pi))).map sourceUnitDirection

instance sourceArcLength_finite : IsFiniteMeasure sourceArcLength := by
  unfold sourceArcLength
  infer_instance

noncomputable def sourceTestNorm (q : ℝ) (γ : Measure UnitCircle) : ℝ≥0∞ :=
  ⨆ (F : BoundedContinuousFunction UnitCircle ℝ)
    (_ : eLpNorm F (ENNReal.ofReal q) sourceArcLength ≤ 1),
      ENNReal.ofReal ‖∫ ω, F ω ∂γ‖

theorem sourceTestNorm_lowerSemicontinuous {X : Type*} [TopologicalSpace X]
    (γ : X → Measure UnitCircle) (q : ℝ)
    (hγ : ∀ F : BoundedContinuousFunction UnitCircle ℝ,
      Continuous (fun x => ∫ ω, F ω ∂γ x)) :
    LowerSemicontinuous (fun x => sourceTestNorm q (γ x)) := by
  unfold sourceTestNorm
  apply lowerSemicontinuous_biSup
  intro F _
  exact (ENNReal.continuous_ofReal.comp (hγ F).norm).lowerSemicontinuous

theorem sourceTestNorm_radial_lowerSemicontinuous {A B : Set Plane}
    (hAB : Disjoint A B) (μ : ProbabilityMeasure B) (q : ℝ) :
    LowerSemicontinuous (fun x : A => sourceTestNorm q (radialProbability hAB μ x)) := by
  apply sourceTestNorm_lowerSemicontinuous
  exact (ProbabilityMeasure.continuous_iff_forall_continuous_integral.mp
    (continuous_radialProbability hAB μ))

theorem sourceTestNorm_le_liminf (γ : Measure UnitCircle) (γn : ℕ → Measure UnitCircle)
    (q : ℝ) (hγ : ∀ F : BoundedContinuousFunction UnitCircle ℝ,
      Tendsto (fun n => ∫ ω, F ω ∂γn n) atTop (𝓝 (∫ ω, F ω ∂γ))) :
    sourceTestNorm q γ ≤ liminf (fun n => sourceTestNorm q (γn n)) atTop := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  have h := (ENNReal.continuous_ofReal.tendsto _).comp (hγ F).norm
  rw [← h.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall (fun n =>
    le_iSup_of_le F (le_iSup_of_le hF le_rfl)))

theorem sourceTestNorm_radial_mollification_le_liminf (α : Measure Plane) [IsFiniteMeasure α]
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (x : Plane) (hx : ∀ᵐ y ∂α, y ≠ x) (q : ℝ) :
    sourceTestNorm q (α.map (sourceRadialUnit x)) ≤
      liminf (fun n => sourceTestNorm q
        ((α ∗ sourceDensityMeasure (sourceMollifier (ε n) (hε n))).map (sourceRadialUnit x))) atTop :=
  sourceTestNorm_le_liminf _ _ q (sourceMollification_radial_test_tendsto α hε hlim x hx)

end PlanarFalconer

end OAI
