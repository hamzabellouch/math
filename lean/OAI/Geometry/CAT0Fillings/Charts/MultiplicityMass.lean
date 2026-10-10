import Mathlib
import OAI.Geometry.CAT0Fillings.Model
import OAI.Geometry.CAT0Fillings.Charts.DensityPush
import OAI.Geometry.CAT0Fillings.Charts.LinearMass
import OAI.Geometry.CAT0Fillings.Currents.MassBounds

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory
open scoped NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
lemma multiplicity_integral_le_mass (hC : IsMetricCurrent C.action)
    {U : ℝ≥0} (hU : AntilipschitzWith U C.param) :
    (∫ z in C.domain, |(C.multiplicity z : ℝ)|) ≤ (U : ℝ)^k * mass C.action := by
  obtain ⟨ν,hν,hcontrol,hmass⟩ := hC.exists_controls_mass_eq
  let := hν
  have hrow : ∀ (i : Fin k) y (hy : y ∈ C.domain) z (hz : z ∈ C.domain),
      |EuclideanSpace.proj i y - EuclideanSpace.proj i z| ≤
        (U : ℝ) * dist (C.param ⟨y,hy⟩) (C.param ⟨z,hz⟩) := by
    intro i y hy z hz
    calc
      _ = ‖(y-z).ofLp i‖ := by
        change |y.ofLp i-z.ofLp i| = ‖(y-z).ofLp i‖
        simp [Real.norm_eq_abs]
      _ ≤ ‖y-z‖ := PiLp.norm_apply_le (y-z) i
      _ ≤ _ := by simpa only [dist_eq_norm,Subtype.dist_eq] using
        hU.le_mul_dist ⟨y,hy⟩ ⟨z,hz⟩
  have hdet : |(Matrix.of fun (i j : Fin k) =>
      EuclideanSpace.proj i (EuclideanSpace.single j (1 : ℝ))).det| = 1 := by
    have he : (Matrix.of fun (i j : Fin k) =>
        EuclideanSpace.proj i (EuclideanSpace.single j (1 : ℝ))) = 1 := by
      ext i j
      change (EuclideanSpace.single j (1 : ℝ)).ofLp i = (1 : Matrix (Fin k) (Fin k) ℝ) i j
      simp [PiLp.single_apply,Matrix.one_apply]
    rw [he,Matrix.det_one,abs_one]
  have hle := C.linear_piece_mass_le hC hcontrol C.borel (Subset.refl _)
    (fun i => EuclideanSpace.proj i) U hrow
  simp only [hdet,mul_one] at hle
  have hle' := hle.trans (Measure.restrict_le_self)
  have hI := integral_mono_measure hle' (Eventually.of_forall (fun _ => (zero_le_one : (0:ℝ) ≤ 1)))
    (integrable_const (1 : ℝ) : Integrable (fun _ : X => (1 : ℝ)) ((U^k) • ν))
  rw [integral_densityPush (volume.restrict C.domain) C.measurable_paramExtended
    C.integrable.abs (Eventually.of_forall (fun _ => abs_nonneg _)) continuous_const] at hI
  rw [integral_smul_nnreal_measure] at hI
  simp only [mul_one,integral_const,smul_eq_mul,NNReal.smul_def,NNReal.coe_pow] at hI
  simpa only [hmass,mul_one] using hI

end IntegerChart
end CAT0Fillings

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable
open Set Metric
open scoped NNReal

end CAT0Fillings
end

end OAI
