import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatPositiveSmooth
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.CompactParameterIntegral

namespace OAI

/-! Smoothness of the prescribed heat convolution at every positive time.
Compact parameter integration applies after using logarithmic time. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory
open scoped ContDiff

private abbrev HeatCell := Icc (0 : Plane) (fun _ => 1)
private instance : CompactSpace HeatCell :=
  isCompact_iff_compactSpace.mp
    (isCompact_Icc : IsCompact (Icc (0 : Plane) (fun _ => 1)))
local instance : MeasureSpace HeatCell := Measure.Subtype.measureSpace
private instance : IsFiniteMeasure (volume : Measure HeatCell) := by
  constructor
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
  exact (isCompact_Icc : IsCompact (Icc (0 : Plane) (fun _ => 1))).measure_lt_top

theorem torusHeatEvolution_exp_smooth (g : Plane → ℝ) (hg : Continuous g) :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => torusHeatEvolution g (Real.exp p.1) p.2) := by
  let E := (ℝ × Plane) × ℝ
  let f : E → ℝ := fun q => torusHeatKernel (Real.exp q.1.1) q.1.2 * q.2
  have hf : ContDiff ℝ ∞ f :=
    (torusHeatKernel_exp_smooth.comp contDiff_fst).mul contDiff_snd
  let b : C(HeatCell, E) := ⟨fun y => ((0, -(y : Plane)), g y),
    (continuous_const.prodMk continuous_subtype_val.neg).prodMk
      (hg.comp continuous_subtype_val)⟩
  let A : (ℝ × Plane) →L[ℝ] C(HeatCell, E) :=
    (ContinuousLinearMap.const ℝ HeatCell).comp (ContinuousLinearMap.inl ℝ (ℝ × Plane) ℝ)
  have hv : ContDiff ℝ ∞ (fun p => A p + b) := A.contDiff.add contDiff_const
  have h := Flow.contDiff_compactIntegral (volume : Measure HeatCell)
    (⟨f, hf.continuous⟩ : C(E, ℝ)) hf (fun p => A p + b) hv
  convert h using 1
  funext p
  rw [torusHeatEvolution, ite_eq_right (not_le.mpr (Real.exp_pos _)),
    ← integral_subtype measurableSet_Icc]
  congr 1
  funext y
  change torusHeatKernel (Real.exp p.1) (p.2 - (y : Plane)) * g y =
    torusHeatKernel (Real.exp (p.1 + 0)) (p.2 + -(y : Plane)) * (0 + g y)
  simp only [add_zero, zero_add, sub_eq_add_neg]


theorem torusHeatEvolution_smooth_positive (g : Plane → ℝ) (hg : Continuous g) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Plane => torusHeatEvolution g p.1 p.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  have hl : ContDiffOn ℝ ∞ (fun p : ℝ × Plane => (Real.log p.1, p.2))
      (Ioi (0 : ℝ) ×ˢ univ) :=
    (contDiff_fst.contDiffOn.log (fun _ hp => ne_of_gt hp.1)).prodMk
      contDiff_snd.contDiffOn
  have hs := (torusHeatEvolution_exp_smooth g hg).comp_contDiffOn hl
  apply hs.congr
  intro p hp
  change torusHeatEvolution g p.1 p.2 =
    torusHeatEvolution g (Real.exp (Real.log p.1)) p.2
  rw [Real.exp_log hp.1]


end ForcedComputation.VelocityDetector

end

end OAI
