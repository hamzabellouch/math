import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.LinearMass
import OAI.Geometry.CAT0Fillings.Charts.CurrentAxioms
import OAI.Geometry.CAT0Fillings.Charts.ExactMass
import OAI.Geometry.CAT0Fillings.Charts.JacobianBound
import OAI.Geometry.CAT0Fillings.Slicing.CoordinateChart
import OAI.Geometry.CAT0Fillings.Slicing.CoordinateDerivative
import OAI.Geometry.CAT0Fillings.Slicing.CoordinateIntegral
import OAI.Geometry.CAT0Fillings.Currents.MassTests

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {k : ℕ} (C : IntegerChart X k)
lemma majorant_test_bound {J : Euc k → ℝ}
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * J z) (volume.restrict C.domain))
    (hJ : 0 ≤ᵐ[volume.restrict C.domain] J)
    (b : X → ℝ) (π : Fin k → X → ℝ) (hb : BoundedLip b)
    (hπ : ∀ i, LipschitzWith 1 (π i))
    (hdet : ∀ᵐ z ∂volume.restrict C.domain, |C.jacobian π z| ≤ J z) :
    |C.action b π| ≤ ∫ x, |b x| ∂C.majorantMeasure J := by
  let μ := volume.restrict C.domain
  have hbmeas := hb.continuous.measurable.comp C.measurable_paramExtended
  obtain ⟨M,hM⟩ := hb.2
  have hupper : Integrable (fun z => (|(C.multiplicity z : ℝ)| * J z)*|b (C.paramExtended z)|) μ :=
    hρ.mul_bdd hbmeas.abs.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs,abs_abs] using hM _)
  have hρ0 : 0 ≤ᵐ[μ] fun z => |(C.multiplicity z : ℝ)| * J z :=
    hJ.mono fun z hz => mul_nonneg (abs_nonneg _) hz
  rw [majorantMeasure,integral_densityPush μ C.measurable_paramExtended hρ hρ0 hb.continuous.abs]
  rw [action,ite_eq_left ⟨hb,fun i => ⟨1,hπ i⟩⟩]
  rw [← Real.norm_eq_abs]
  apply le_trans (norm_integral_le_integral_norm _) ?_
  change (∫ z, |(C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z| ∂μ) ≤ _
  apply integral_mono_ae
    (C.integrable_action_integrand hb (fun i => ⟨1,hπ i⟩)).abs hupper
  filter_upwards [hdet,C.scalar_ae_paramExtended b] with z hz hbz
  rw [abs_mul,abs_mul,hbz]
  change |(C.multiplicity z : ℝ)| * |b (C.paramExtended z)| * |C.jacobian π z| ≤ _
  calc _ ≤ (|(C.multiplicity z : ℝ)| * |b (C.paramExtended z)|) * J z :=
      mul_le_mul_of_nonneg_left hz (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring
end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

lemma ae_integrable_coordinate {g : Euc (k+1) → ℝ}
    (hg : Integrable g (volume.restrict C.domain)) :
    ∀ᵐ t : ℝ, Integrable (fun z => g (coordinateLayer k t z))
      (volume.restrict (C.coordinateDomain t)) := by
  have hi : Integrable (C.domain.indicator g) := (integrable_indicator_iff C.borel).mpr hg
  have hip : Integrable (fun p : ℝ × Euc k => C.domain.indicator g ((Prism.split k).symm p)) :=
    ((Prism.split_symm_measurePreserving k).integrable_comp_emb
      (Prism.split k).symm.toHomeomorph.measurableEmbedding).mpr hi
  filter_upwards [hip.prod_right_ae] with t ht
  apply (integrable_indicator_iff (C.measurableSet_coordinateDomain t)).mp
  simpa only [C.coordinate_indicator g t] using ht

lemma ae_coordinate_of_ae {p : Euc (k+1) → Prop}
    (hp : ∀ᵐ w ∂volume.restrict C.domain, p w) :
    ∀ᵐ t : ℝ, ∀ᵐ z ∂volume.restrict (C.coordinateDomain t), p (coordinateLayer k t z) := by
  have hf := (ae_restrict_iff' C.borel).mp hp
  have hm := (Prism.split_symm_measurePreserving k).quasiMeasurePreserving.ae hf
  filter_upwards [Measure.ae_ae_of_ae_prod hm] with t ht
  exact (ae_restrict_iff' (C.measurableSet_coordinateDomain t)).mpr ht

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X (k+1))

theorem coordinate_coarea_majorant {J : Euc (k+1) → ℝ}
    (hρ : Integrable (fun z => |(C.multiplicity z:ℝ)| * J z) (volume.restrict C.domain))
    (hJ : ∀ z, 0 ≤ J z)
    (hdet : ∀ π : Fin k → X → ℝ, (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ z ∂volume.restrict C.domain, |C.coordinateMinor π z| ≤ J z) :
    ∃ G : ℝ → ℝ, Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∀ᵐ t : ℝ, mass (C.coordinateSliceTotal t).action ≤ G t) ∧
      (∫ t : ℝ, G t) = ∫ z in C.domain, |(C.multiplicity z:ℝ)| * J z := by
  let G : ℝ → ℝ := fun t => ∫ z in C.coordinateDomain t,
    |(C.multiplicity (coordinateLayer k t z):ℝ)| * J (coordinateLayer k t z)
  let μ : ℝ → Measure X := fun t => (C.coordinateSliceTotal t).majorantMeasure
    (fun z => J (coordinateLayer k t z))
  have hsliceρ : ∀ᵐ t : ℝ,
      Integrable (fun z => |((C.coordinateSliceTotal t).multiplicity z:ℝ)| *
        J (coordinateLayer k t z)) (volume.restrict (C.coordinateSliceTotal t).domain) := by
    filter_upwards [C.ae_coordinateSliceTotal_eq,C.ae_integrable_coordinate hρ] with t ht hρt
    obtain ⟨hi,heq⟩ := ht
    rw [heq]
    exact hρt
  have hfin : ∀ᵐ t : ℝ, IsFiniteMeasure (μ t) := by
    filter_upwards [hsliceρ] with t ht
    exact densityPush_finite _ _ ht
  have hcontrols : ∀ᵐ t : ℝ, Controls (C.coordinateSliceTotal t).action (μ t) := by
    apply Foundations.ae_controls_of_testwise_bound volume
      (Eventually.of_forall fun t => (C.coordinateSliceTotal t).action_isMetricCurrent) hfin
    intro b π hb hπ
    filter_upwards [hsliceρ,C.ae_coordinateSliceTotal_eq,
      C.ae_coordinateSlice_jacobian π (fun i => ⟨1,hπ i⟩),
      C.ae_coordinate_of_ae (hdet π hπ)] with t hρt ht hj hdt
    apply (C.coordinateSliceTotal t).majorant_test_bound hρt
      (Eventually.of_forall fun z => hJ (coordinateLayer k t z)) b π hb hπ
    obtain ⟨hi,heq⟩ := ht
    rw [heq]
    filter_upwards [hj hi,hdt] with z hz hd
    rw [hz]
    exact hd
  have hm : ∀ᵐ t : ℝ, (μ t).real univ = G t := by
    filter_upwards [hsliceρ,C.ae_coordinateSliceTotal_eq,hfin] with t hρt ht hμt
    let := hμt
    calc
      (μ t).real univ = ∫ x, (1:ℝ) ∂μ t := by simp
      _ = ∫ z in (C.coordinateSliceTotal t).domain,
          |((C.coordinateSliceTotal t).multiplicity z:ℝ)| * J (coordinateLayer k t z) := by
        rw [show μ t = (C.coordinateSliceTotal t).majorantMeasure
          (fun z => J (coordinateLayer k t z)) from rfl,majorantMeasure,
          integral_densityPush _ (C.coordinateSliceTotal t).measurable_paramExtended hρt
            (Eventually.of_forall fun z => mul_nonneg (abs_nonneg _) (hJ _)) continuous_const]
        simp only [mul_one]
      _ = G t := by
        obtain ⟨hi,heq⟩ := ht
        rw [heq]
        rfl
  refine ⟨G,C.integrable_coordinate_setIntegral hρ,fun t =>
    integral_nonneg (fun z => mul_nonneg (abs_nonneg _) (hJ _)),?_,?_⟩
  · filter_upwards [hcontrols,hfin,hm] with t hct hft hmt
    rw [←hmt]
    exact mass_le_measure hft hct
  · exact (C.coordinate_setIntegral hρ).symm

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X (k+1))

theorem sharp_coordinate_coarea_majorant (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1) :
    ∃ G : ℝ → ℝ, Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∀ᵐ t : ℝ, mass (C.coordinateSliceTotal t).action ≤ G t) ∧
      (∫ t : ℝ, G t) = K * mass C.action := by
  obtain ⟨P,hPm,hP,hρ,hfin,hctrl,hle,p,hpP,hpm,hp⟩ :=
    C.exists_exact_quadratic_mass hX C.action_isMetricCurrent
  let μ := C.majorantMeasure (fun z => Real.sqrt (P z).det)
  let : IsFiniteMeasure μ := hfin
  have hμmass : mass C.action = μ.real univ := by
    apply le_antisymm (mass_le_measure hfin hctrl)
    obtain ⟨ν,hνfin,hν,hνmass⟩ := C.action_isMetricCurrent.exists_controls_mass_eq
    let := hνfin
    rw [hνmass]
    exact ENNReal.toReal_mono (measure_ne_top ν univ) (hle ν hνfin hν univ)
  have hm : mass C.action = ∫ z in C.domain,
      |(C.multiplicity z:ℝ)| * Real.sqrt (P z).det := by
    rw [hμmass]
    calc
      μ.real univ = ∫ x, (1:ℝ) ∂μ := by simp
      _ = _ := by
        rw [show μ = C.majorantMeasure (fun z => Real.sqrt (P z).det) from rfl,
          majorantMeasure,integral_densityPush _ C.measurable_paramExtended hρ
            (Eventually.of_forall fun z => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
            continuous_const]
        simp only [mul_one]
  have hρK : Integrable (fun z => |(C.multiplicity z:ℝ)| *
      ((K:ℝ) * Real.sqrt (P z).det)) (volume.restrict C.domain) := by
    convert hρ.const_mul (K:ℝ) using 1
    ext z
    ring
  have hdet : ∀ π : Fin k → X → ℝ, (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ z ∂volume.restrict C.domain, |C.coordinateMinor π z| ≤
        (K:ℝ) * Real.sqrt (P z).det := by
    intro π hπ
    have hh := C.ae_jacobian_bound_quadratic p hp (Matrix.vecCons u π)
      (Matrix.vecCons K (fun _ => 1)) (fun i => by
        cases i using Fin.cases with
        | zero => exact hK
        | succ i => exact hπ i)
    filter_upwards [hh,C.ae_coordinate_minor_eq hu π] with z hz heq
    rw [heq] at hz
    simpa only [hpP,Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      NNReal.coe_one,Finset.prod_const_one,mul_one] using hz
  obtain ⟨G,hG,hG0,hGm,hGI⟩ := C.coordinate_coarea_majorant hρK
    (fun z => mul_nonneg K.coe_nonneg (Real.sqrt_nonneg _)) hdet
  refine ⟨G,hG,hG0,hGm,?_⟩
  rw [hGI,hm,←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by ring

end CAT0Fillings.IntegerChart

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

namespace CAT0Fillings.BorelCoefficients
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]
lemma integrable_boundedLip {b : X → ℝ} (hb : BoundedLip b) : Integrable b μ :=
  hb.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end CAT0Fillings.BorelCoefficients
end

end OAI
