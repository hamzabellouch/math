import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.CurrentAxioms
import OAI.Geometry.CAT0Fillings.Prism.Action
import OAI.Geometry.CAT0Fillings.Prism.TimeCoordinate

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma chart_abs_integrand_le [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [Nonempty X] {ν : Measure X} [IsFiniteMeasure ν] (hν : Controls C.action ν)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hb : BoundedLip b)
    (hπ : ∀ i, LipschitzWith 1 (π i)) :
    (∫ z in C.domain, |(C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z|) ≤
      ∫ x, |b x| ∂ν := by
  have hw := C.integrable_weighted_jacobian (fun i => ⟨1,hπ i⟩)
  have hm : densityPush (volume.restrict C.domain) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)*C.jacobian π z|) ≤ ν := by
    simpa using C.weighted_jacobian_le_measure C.action_isMetricCurrent hν π (fun _ => 1) hπ
  have hib : Integrable (fun x => |b x|) ν :=
    hb.continuous.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc _ = ∫ x, |b x| ∂(densityPush (volume.restrict C.domain) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)*C.jacobian π z|)) := by
        rw [integral_densityPush _ C.measurable_paramExtended hw.abs
          (Eventually.of_forall fun _ => abs_nonneg _) hb.continuous.abs]
        apply integral_congr_ae
        filter_upwards [C.scalar_ae_paramExtended b] with z hz
        dsimp only [Function.comp_apply] at hz
        rw [hz,abs_mul,abs_mul,abs_mul]
        ring
    _ ≤ _ := integral_mono_measure hm (Eventually.of_forall fun _ => abs_nonneg _) hib

lemma ae_prism_jacobian_bound (π : Fin (k+1) → ℝ × X → ℝ)
    (hπ : ∀ i, LipschitzWith 1 (π i)) :
    ∀ᵐ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain),
      |C.prism.jacobian π ((Prism.split k).symm p)| ≤
        ∑ i : Fin (k+1), |C.jacobian (fun j x => π (i.succAbove j) (p.1,x)) p.2| := by
  have hpz := Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Icc (0:ℝ) 1)) |>.ae
    (ae_restrict_mem (μ := volume) C.borel)
  filter_upwards [C.ae_prism_jacobian_decompose π (fun i => ⟨1,hπ i⟩),hpz] with p hd hz
  rw [hd]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hl : LipschitzWith 1 (fun t => C.scalar (fun x => π i (t,x)) p.2) := by
    have heq : (fun t => C.scalar (fun x => π i (t,x)) p.2) =
        (fun t => π i (t,C.param ⟨p.2,hz⟩)) := funext fun _ => C.scalar_eq hz
    rw [heq]
    exact lipschitz_time (hπ i) _
  have hD : |deriv (fun t => C.scalar (fun x => π i (t,x)) p.2) p.1| ≤ 1 := by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hl
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) hD

lemma prism_controls [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [Nonempty X] {ν : Measure X} [IsFiniteMeasure ν] (hν : Controls C.action ν) :
    Controls C.prism.action ((k+1 : ℝ≥0) • (volume.restrict (Icc (0:ℝ) 1)).prod ν) := by
  intro b π hb hπ
  let F (i : Fin (k+1)) (p : ℝ × Euc k) :=
    |(C.multiplicity p.2 : ℝ) * C.scalar (fun x => b (p.1,x)) p.2 *
      C.jacobian (fun j x => π (i.succAbove j) (p.1,x)) p.2|
  have hF (i : Fin (k+1)) : Integrable (F i)
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) :=
    (C.integrable_prism_slice b (fun j => π (i.succAbove j))
      ⟨hb,fun j => ⟨1,hπ _⟩⟩).abs
  have hib : Integrable (fun p : ℝ × X => |b p|)
      ((volume.restrict (Icc (0:ℝ) 1)).prod ν) := by
    obtain ⟨M,hM⟩ := hb.2
    exact Integrable.of_bound hb.continuous.abs.aestronglyMeasurable M
      (Eventually.of_forall fun p => by simpa using hM p)
  have hinner (i : Fin (k+1)) :
      (∫ p, F i p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) ≤
      ∫ p : ℝ × X, |b p| ∂(volume.restrict (Icc (0:ℝ) 1)).prod ν := by
    rw [integral_prod _ (hF i),integral_prod _ hib]
    apply integral_mono_ae (hF i).integral_prod_left hib.integral_prod_left
    exact Eventually.of_forall fun t => C.chart_abs_integrand_le hν
      (boundedLip_slice hb t) (fun j => lipschitz_slice (hπ (i.succAbove j)) t)
  rw [C.prism_action_eq b π ⟨hb,fun i => ⟨1,hπ i⟩⟩]
  calc _ ≤ ∫ p, |(C.multiplicity p.2 : ℝ)*C.scalar (fun x => b (p.1,x)) p.2*
        C.prism.jacobian π ((Prism.split k).symm p)|
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain) := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (μ := ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)))
            (fun p => (C.multiplicity p.2 : ℝ)*C.scalar (fun x => b (p.1,x)) p.2*
              C.prism.jacobian π ((Prism.split k).symm p))
    _ ≤ ∫ p, ∑ i, F i p
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain) := by
      apply integral_mono_ae (C.integrable_prism_formula b π ⟨hb,fun i => ⟨1,hπ i⟩⟩).abs
        (integrable_finsetSum _ fun i _ => hF i)
      filter_upwards [C.ae_prism_jacobian_bound π hπ] with p hp
      simp only [F,abs_mul,← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hp (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = ∑ i, ∫ p, F i p
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain) :=
      integral_finsetSum _ fun i _ => hF i
    _ ≤ ∑ _i : Fin (k+1), ∫ p : ℝ × X, |b p|
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod ν := Finset.sum_le_sum fun i _ => hinner i
    _ = _ := by
      rw [integral_smul_nnreal_measure]
      simp [NNReal.smul_def]

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
open MeasureTheory Set
open scoped NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

lemma mass_prism_le : mass C.prism.action ≤ (k+1 : ℝ) * mass C.action := by
  obtain ⟨ν,hfin,hν,heq⟩ := C.action_isMetricCurrent.exists_controls_mass_eq
  let : IsFiniteMeasure ν := hfin
  apply (mass_le_measure (inferInstance : IsFiniteMeasure
    ((k+1 : ℝ≥0) • (volume.restrict (Icc (0:ℝ) 1)).prod ν)) (C.prism_controls hν)).trans_eq
  rw [heq,measureReal_nnreal_smul_apply]
  simp [measureReal_def,← Set.univ_prod_univ, Measure.prod_prod]

end CAT0Fillings.IntegerChart

end
end

end OAI
