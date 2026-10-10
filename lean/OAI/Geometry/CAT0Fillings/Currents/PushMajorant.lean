import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.DensityPush
import OAI.Geometry.CAT0Fillings.Currents.Pushforward
import OAI.Geometry.CAT0Fillings.Charts.Extensions
import OAI.Geometry.CAT0Fillings.Fillings.ConeBound

namespace OAI

section
section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
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
open Set MeasureTheory CurrentOperations
open scoped NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
theorem IsCAT0.exists_integral_filling_diam (hX : IsCAT0 X) {k : ℕ}
    {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0) :
    ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧ boundarySucc S = T ∧
      mass S ≤ (k+2:ℝ)*Metric.diam (univ : Set X)*mass T := by
  let o : X := Classical.choice inferInstance
  let R : ℝ≥0 := ⟨Metric.diam (univ : Set X),Metric.diam_nonneg⟩
  exact hX.exists_integral_filling_mass_le hT hz o R (fun x =>
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ o) (mem_univ x))

end CAT0Fillings

end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

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
attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable


attribute [local instance] Classical.propDecidable
open Set Metric
open scoped NNReal

end CAT0Fillings

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

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
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings
namespace CAT0Fillings
open MeasureTheory Set Filter CurrentOperations

namespace IntegerChart
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {k : ℕ} (C : IntegerChart X k)

theorem push_majorant_controls {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f)
    {J : Euc k → ℝ}
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| *J z) (volume.restrict C.domain))
    (hJ : 0 ≤ᵐ[volume.restrict C.domain] J)
    (hdet : ∀ π : Fin k → Y → ℝ, (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ z ∂volume.restrict C.domain, |C.jacobian (fun i => π i ∘ f) z| ≤ J z) :
    Controls (pushCurrent f C.action)
      (densityPush (volume.restrict C.domain) (f ∘ C.paramExtended)
        (fun z => |(C.multiplicity z : ℝ)| *J z)) := by
  intro b π hb hπ
  let μ := volume.restrict C.domain
  have hφ := hf.continuous.measurable.comp C.measurable_paramExtended
  have hbmeas := hb.continuous.measurable.comp hφ
  obtain ⟨M,hM⟩ := hb.2
  have hupper : Integrable
      (fun z => (|(C.multiplicity z : ℝ)| *J z)*|b (f (C.paramExtended z))|) μ :=
    hρ.mul_bdd hbmeas.abs.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs,abs_abs] using hM _)
  have hρ0 : 0 ≤ᵐ[μ] fun z => |(C.multiplicity z : ℝ)| *J z :=
    hJ.mono fun z hz => mul_nonneg (abs_nonneg _) hz
  rw [integral_densityPush μ hφ hρ hρ0 hb.continuous.abs]
  rw [pushCurrent_apply f C.action ⟨hb,fun i => ⟨1,hπ i⟩⟩,
    action,ite_eq_left (admissible_comp ⟨hb,fun i => ⟨1,hπ i⟩⟩ hf)]
  rw [←Real.norm_eq_abs]
  apply le_trans (norm_integral_le_integral_norm _) ?_
  change (∫ z, |(C.multiplicity z : ℝ)*C.scalar (b ∘ f) z*
    C.jacobian (fun i => π i ∘ f) z| ∂μ) ≤ _
  apply integral_mono_ae
    (C.integrable_action_integrand (boundedLip_comp hb hf)
      (admissible_comp ⟨hb,fun i => ⟨1,hπ i⟩⟩ hf).2).abs hupper
  filter_upwards [hdet π hπ,C.scalar_ae_paramExtended (b ∘ f)] with z hz hbz
  rw [abs_mul,abs_mul,hbz]
  change |(C.multiplicity z : ℝ)| *|b (f (C.paramExtended z))| *
    |C.jacobian (fun i => π i ∘ f) z| ≤ _
  calc _ ≤ (|(C.multiplicity z : ℝ)| *|b (f (C.paramExtended z))|)*J z :=
      mul_le_mul_of_nonneg_left hz (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

theorem push_mass_le_majorant {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f)
    {J : Euc k → ℝ}
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| *J z) (volume.restrict C.domain))
    (hJ : 0 ≤ᵐ[volume.restrict C.domain] J)
    (hdet : ∀ π : Fin k → Y → ℝ, (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ z ∂volume.restrict C.domain, |C.jacobian (fun i => π i ∘ f) z| ≤ J z) :
    mass (pushCurrent f C.action) ≤
      ∫ z, |(C.multiplicity z : ℝ)| *J z ∂volume.restrict C.domain := by
  let ν := densityPush (volume.restrict C.domain) (f ∘ C.paramExtended)
    (fun z => |(C.multiplicity z : ℝ)| *J z)
  have hfin : IsFiniteMeasure ν := densityPush_finite _ _ hρ
  have hc := C.push_majorant_controls hf hρ hJ hdet
  have hu : ν.real univ = ∫ z, |(C.multiplicity z : ℝ)| *J z ∂volume.restrict C.domain := by
    have hi := integral_densityPush (volume.restrict C.domain)
      (hf.continuous.measurable.comp C.measurable_paramExtended) hρ
      (hJ.mono fun z hz => mul_nonneg (abs_nonneg _) hz) continuous_const (b := fun _ => (1:ℝ))
    simpa only [integral_const,smul_eq_mul,mul_one] using hi
  exact (mass_le_measure hfin hc).trans_eq hu
end IntegerChart
end CAT0Fillings

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

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

end
end

end OAI
