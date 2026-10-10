import Mathlib
import OAI.Geometry.IntegralFillings.Currents.Basic
import OAI.Geometry.IntegralFillings.Currents.WeakMass

namespace OAI

universe u

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

namespace SharpIntegralFillings
namespace MassMeasure
variable {X : Type u} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
noncomputable def weighted (μ : Measure X) (f : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (f x))

lemma weighted_finite (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Continuous f) : IsFiniteMeasure (weighted μ f) :=
  isFiniteMeasure_withDensity_ofReal
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).hasFiniteIntegral

omit [CompactSpace X] in
lemma integral_weighted (μ : Measure X) {f : X → ℝ}
    (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) (g : X → ℝ) :
    (∫ x, g x ∂weighted μ f) = ∫ x, f x * g x ∂μ := by
  rw [weighted, integral_withDensity_eq_integral_toReal_smul
    (hf.measurable.ennreal_ofReal) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hpos _), smul_eq_mul]

omit [CompactSpace X] in
lemma weighted_total (μ : Measure X) {f : X → ℝ}
    (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) :
    (weighted μ f).real univ = ∫ x, f x ∂μ := by
  simpa using integral_weighted μ hf hpos (fun _ => 1)

variable {k : ℕ} {T : Functional X k}

lemma controls_splice (hT : IsMetricCurrent T) {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Controls T μ) (hν : Controls T ν)
    {f : X → ℝ} (hf : BoundedLip f) (hpos : ∀ x, 0 ≤ f x) (hbound : ∀ x, f x ≤ 1) :
    Controls T (weighted μ (fun x => 1 - f x) + weighted ν f) := by
  have hg : BoundedLip (fun x => 1 - f x) := by
    simpa only [neg_mul, one_mul, sub_eq_add_neg] using
      (BoundedLip.const 1).add (hf.const_mul (-1))
  let := weighted_finite μ hg.continuous
  let := weighted_finite ν hf.continuous
  intro b π hb hπ
  have hlin : T b π = T (fun x => b x * (1 - f x)) π + T (fun x => b x * f x) π := by
    have h := hT.linearFirst (fun x => b x * (1-f x)) (fun x => b x * f x) π 1 1
      (hb.mul hg) (hb.mul hf) (fun i => ⟨1, hπ i⟩)
    have heq : (fun x => 1 * (b x * (1-f x)) + 1 * (b x * f x)) = b := by
      funext x; ring
    rwa [heq, one_mul, one_mul] at h
  rw [hlin]
  calc |T (fun x => b x * (1-f x)) π + T (fun x => b x * f x) π| ≤
        |T (fun x => b x * (1-f x)) π| + |T (fun x => b x * f x) π| := abs_add_le _ _
    _ ≤ (∫ x, |b x * (1-f x)| ∂μ) + ∫ x, |b x * f x| ∂ν :=
      add_le_add (hμ _ _ (hb.mul hg) hπ) (hν _ _ (hb.mul hf) hπ)
    _ = ∫ x, |b x| ∂(weighted μ (fun x => 1-f x) + weighted ν f) := by
      rw [integral_add_measure
        (hb.continuous.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (hb.continuous.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
        integral_weighted μ hg.continuous (fun x => sub_nonneg.mpr (hbound x)),
        integral_weighted ν hf.continuous hpos]
      congr 1
      · apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change |b x * (1-f x)| = (1-f x) * |b x|
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hbound x)), mul_comm]
      · apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change |b x * f x| = f x * |b x|
          rw [abs_mul, abs_of_nonneg (hpos x), mul_comm]

lemma integral_cutoff_le (hT : IsMetricCurrent T) {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Controls T μ) (hν : Controls T ν)
    (hm : mass T = μ.real univ)
    {f : X → ℝ} (hf : BoundedLip f) (hpos : ∀ x, 0 ≤ f x) (hbound : ∀ x, f x ≤ 1) :
    (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν := by
  have hg : Continuous (fun x => 1-f x) := continuous_const.sub hf.continuous
  let := weighted_finite μ hg
  let := weighted_finite ν hf.continuous
  have h := mass_le_measure (T := T)
    (μ := weighted μ (fun x => 1-f x) + weighted ν f) inferInstance
    (controls_splice hT hμ hν hf hpos hbound)
  rw [hm] at h
  have heq : (weighted μ (fun x => 1-f x) + weighted ν f).real univ =
      μ.real univ - (∫ x, f x ∂μ) + ∫ x, f x ∂ν := by
    rw [measureReal_add_apply (by finiteness) (by finiteness),
      weighted_total μ hg (fun x => sub_nonneg.mpr (hbound x)),
      weighted_total ν hf.continuous hpos]
    rw [integral_sub (integrable_const 1)
      (hf.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      integral_const, smul_eq_mul, mul_one]
  rw [heq] at h
  linarith

lemma measure_closed_le (hT : IsMetricCurrent T) {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Controls T μ) (hν : Controls T ν)
    (hm : mass T = μ.real univ) {K : Set X} (hK : IsClosed K) : μ K ≤ ν K := by
  let fs : ℕ → X → ℝ := fun n x =>
    thickenedIndicator (δ := (1 : ℝ)/(n+1)) (by positivity) K x
  have hlimμ : Tendsto (fun n => ∫ x, fs n x ∂μ) atTop (𝓝 (μ.real K)) :=
    tendsto_integral_thickenedIndicator_of_isClosed μ hK (δs := fun n => (1 : ℝ)/(n+1))
      (fun _ => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  have hlimν : Tendsto (fun n => ∫ x, fs n x ∂ν) atTop (𝓝 (ν.real K)) :=
    tendsto_integral_thickenedIndicator_of_isClosed ν hK (δs := fun n => (1 : ℝ)/(n+1))
      (fun _ => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  have hle : ∀ n, (∫ x, fs n x ∂μ) ≤ ∫ x, fs n x ∂ν := by
    intro n
    have hp x : 0 ≤ fs n x := by simp [fs]
    have hb x : fs n x ≤ 1 :=
      thickenedIndicator_le_one _ _ _
    apply integral_cutoff_le hT hμ hν hm _ hp hb
    refine ⟨⟨_, NNReal.isometry_coe.lipschitzWith.comp
      (lipschitzWith_thickenedIndicator
        (δ := (1 : ℝ)/(n+1)) (by positivity) K)⟩, 1, ?_⟩
    intro x
    rw [abs_of_nonneg (hp x)]
    exact hb x
  exact (ENNReal.toReal_le_toReal (measure_ne_top μ K) (measure_ne_top ν K)).mp
    (le_of_tendsto_of_tendsto hlimμ hlimν (Eventually.of_forall hle))

lemma measure_le (hT : IsMetricCurrent T) {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Controls T μ) (hν : Controls T ν)
    (hm : mass T = μ.real univ) : μ ≤ ν := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [hs.measure_eq_iSup_isCompact μ]
  refine iSup_le fun K => iSup_le fun hKs => iSup_le fun hK => ?_
  exact (measure_closed_le hT hμ hν hm hK.isClosed).trans (measure_mono hKs)

lemma measure_unique (hT : IsMetricCurrent T) {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Controls T μ) (hν : Controls T ν)
    (hmμ : mass T = μ.real univ) (hmν : mass T = ν.real univ) : μ = ν :=
  le_antisymm (measure_le hT hμ hν hmμ) (measure_le hT hν hμ hmν)

noncomputable def currentMassMeasure (hT : IsMetricCurrent T) : Measure X :=
  hT.exists_controls_mass_eq.choose

instance currentMassMeasure_finite (hT : IsMetricCurrent T) :
    IsFiniteMeasure (currentMassMeasure hT) :=
  hT.exists_controls_mass_eq.choose_spec.1

lemma currentMassMeasure_controls (hT : IsMetricCurrent T) :
    Controls T (currentMassMeasure hT) :=
  hT.exists_controls_mass_eq.choose_spec.2.1

lemma currentMassMeasure_total (hT : IsMetricCurrent T) :
    (currentMassMeasure hT).real univ = mass T :=
  hT.exists_controls_mass_eq.choose_spec.2.2.symm

lemma currentMassMeasure_le (hT : IsMetricCurrent T) {ν : Measure X}
    [IsFiniteMeasure ν] (hν : Controls T ν) : currentMassMeasure hT ≤ ν :=
  measure_le hT (currentMassMeasure_controls hT) hν (currentMassMeasure_total hT).symm

end MassMeasure
end SharpIntegralFillings

end

end OAI
