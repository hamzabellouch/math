import OAI.Geometry.SurfaceImmersion.Correction.ChartedPolynomialMean
import OAI.Geometry.SurfaceImmersion.Correction.ChartedMetricMeanDifference
import OAI.Geometry.SurfaceImmersion.Geometry.SupportedQuadraticFamily
import OAI.Geometry.Immersion.ClosedSurface.FreeAmplitude

namespace OAI

/-! The combined mean of the actual transported free amplitude, with the
polynomial evaluated in the original coordinates and the metric transformed
as a two-tensor. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

def polynomialMeanField (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := Tensor) K :=
  ⟨(fun x k => normalizedPolynomialMean (P k) δ ε G φ (c.originalFreeSeed δ q b) τ 0 x),
    contDiff_pi.mpr (fun k => normalizedPolynomialMean_smooth c.openU c.openO (c.smoothP k)
      hG c.smoothPhase c.mapsG K c.supportU (c.originalFreeSeed δ q b) δ ε τ 0),
    fun x hx => by
      ext k
      exact image_eq_zero_of_notMem_tsupport (fun hz => hx
        ((c.originalFreeSeed δ q b).tsupport_subset
          (normalizedPolynomialMean_tsupport (P k) δ ε G c.smoothPhase
            (c.originalFreeSeed δ q b).contDiff τ 0 hz)))⟩

def combinedMeanField (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := Tensor) (modeSupport K) :=
  c.metricMeanField δ q b + pushSupported planeCoordinateIsometry K (c.polynomialMeanField δ q b)

def leadingFieldInChart (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := Tensor) c.chartCompact :=
  ⟨c.leadingInChart b,
    contDiff_pi.mpr (fun k => ((b.contDiff.pow 2).mul contDiff_const).mul contDiff_const),
    fun x hx => by
      ext k
      change b x ^ 2 * _ * _ = 0
      have hb : b x = (0 : ℝ) := b.zero_on_compl hx
      simp only [hb, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]⟩

def leadingField (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := Tensor) (modeSupport K) :=
  realTensorChartPull c.e c.smoothForward (modeSupport K) c.supportChart (c.leadingFieldInChart b)

lemma metric_zero_phase_identity {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) (x : SmallModes.Base) :
    phaseZeroTensor τ (coordinatePhase φ) (coordinateAmplitude (c.originalFreeSeed δ q b)) x =
      δ ^ 2 • (c.leadingField b x + c.metricMeanField δ q b x) := by
  by_cases hx : x ∈ c.e.source
  · rw [c.originalFreeSeed_zeroPhase hδ hτ q b hx]
    simp only [leadingField, realTensorChartPull_apply, metricMeanField_apply, Set.indicator_of_mem hx]
    rfl
  · have hn : x ∉ tsupport (coordinateAmplitude (c.originalFreeSeed δ q b)) :=
      fun hs => hx (c.supportChart (coordinateAmplitude_tsupport (c.originalFreeSeed δ q b) hs))
    have hz := RealModes.phaseZeroTensor_congr (φ := coordinatePhase φ) (ψ := coordinatePhase φ)
      Filter.EventuallyEq.rfl (notMem_tsupport_iff_eventuallyEq.mp hn) τ
    rw [hz]
    change phaseZeroTensor τ (coordinatePhase φ) (fun _ => (0 : SmallModes.Ambient 4)) x = _
    rw [RealModes.phaseZeroTensor_zero]
    simp only [leadingField, realTensorChartPull_apply, metricMeanField_apply,
      Set.indicator_of_notMem hx, zero_add, smul_zero]

theorem combined_zero_phase_identity {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) (x : SmallModes.Base) :
    phaseZeroTensor τ (coordinatePhase φ) (coordinateAmplitude (c.originalFreeSeed δ q b)) x +
      (fun k => quadraticMeanCoefficient (P k) ε G φ (c.originalFreeSeed δ q b) τ 0
        (planeCoordinateIsometry.symm x)) =
      δ ^ 2 • (c.leadingField b x + c.combinedMeanField δ q b x) := by
  rw [c.metric_zero_phase_identity hδ hτ q b x]
  funext k
  change δ ^ 2 * (_ + _) + _ = δ ^ 2 * (_ + (_ +
    normalizedPolynomialMean (P k) δ ε G φ (c.originalFreeSeed δ q b) τ 0 (planeCoordinateIsometry.symm x)))
  unfold normalizedPolynomialMean
  field_simp [hδ]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
