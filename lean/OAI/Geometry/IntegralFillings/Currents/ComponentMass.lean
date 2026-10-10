import Mathlib
import OAI.Geometry.IntegralFillings.Slicing.CoordinateCoarea

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

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma finite_sum_measure_of_summable_total {X : Type*} [MeasurableSpace X]
    (μ : ℕ → Measure X) [∀ i, IsFiniteMeasure (μ i)]
    (hs : Summable (fun i => (μ i).real univ)) : IsFiniteMeasure (Measure.sum μ) := by
  constructor
  have heq : (Measure.sum μ) univ = ENNReal.ofReal (∑' i, (μ i).real univ) := by
    rw [Measure.sum_apply _ MeasurableSet.univ,
      ENNReal.ofReal_tsum_of_nonneg (fun i => measureReal_nonneg) hs]
    congr 1
    funext i
    exact (ENNReal.ofReal_toReal (measure_ne_top (μ i) univ)).symm
  rw [heq]
  exact ENNReal.ofReal_lt_top

section SumControls
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} {T : Functional X k} {S : ℕ → Functional X k}
  {μ : ℕ → Measure X} [IsFiniteMeasure (Measure.sum μ)]

lemma controls_sum (hμ : ∀ i, Controls (S i) (μ i))
    (hT : ∀ b π, T b π = ∑' i, S i b π) : Controls T (Measure.sum μ) := by
  intro b π hb hπ
  have hbi : Integrable (fun x => |b x|) (Measure.sum μ) :=
    (BorelCoefficients.integrable_boundedLip _ hb).abs
  have hs : Summable (fun i => ∫ x, |b x| ∂μ i) := by
    simpa only [Real.norm_eq_abs,abs_abs] using hbi.summable_integral
  have hsa : Summable (fun i => S i b π) :=
    hs.of_norm_bounded (fun i => by simpa only [Real.norm_eq_abs] using hμ i b π hb hπ)
  rw [hT b π,integral_sum_measure hbi]
  calc
    |∑' i, S i b π| ≤ ∑' i, |S i b π| := by
      simpa only [Real.norm_eq_abs] using
        (norm_tsum_le_tsum_norm (f := fun i => S i b π) hsa.norm)
    _ ≤ ∑' i, ∫ x, |b x| ∂μ i := hsa.abs.tsum_le_tsum (fun i => hμ i b π hb hπ) hs

end SumControls

lemma tendsto_integral_abs_of_l1 {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} (hν : ν ≤ μ) {f : ℕ → X → ℝ} {b : X → ℝ}
    (hf : ∀ j, Integrable (f j) μ) (hb : Integrable b μ)
    (hlim : Tendsto (fun j => ∫ x, |f j x-b x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, |f j x| ∂ν) atTop (𝓝 (∫ x, |b x| ∂ν)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hlim
  rw [Real.dist_eq,←integral_sub ((hf j).mono_measure hν).abs (hb.mono_measure hν).abs]
  calc |∫ x, |f j x|-|b x| ∂ν| ≤ ∫ x, abs (|f j x|-|b x|) ∂ν := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun x => |f j x|-|b x|)
    _ ≤ ∫ x, |f j x-b x| ∂ν :=
        integral_mono_ae (((hf j).mono_measure hν).abs.sub (hb.mono_measure hν).abs).abs
          (((hf j).mono_measure hν).sub (hb.mono_measure hν)).abs
          (Eventually.of_forall fun x => abs_abs_sub_abs_le _ _)
    _ ≤ ∫ x, |f j x-b x| ∂μ :=
        integral_mono_measure hν (Eventually.of_forall fun _ => abs_nonneg _)
          ((hf j).sub hb).abs
end SharpIntegralFillings

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

section ComponentControls
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} {T : Functional X k} {S : ℕ → Functional X k}
  {μ : ℕ → Measure X} [IsFiniteMeasure (Measure.sum μ)]
  {Z : ℕ → Set X}

lemma component_approximation_bound (hS : ∀ i, IsMetricCurrent (S i))
    (hμ : ∀ i, Controls (S i) (μ i))
    (hT : ∀ b π, T b π = ∑' i, S i b π)
    (hZ : ∀ i, MeasurableSet (Z i)) (hd : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    (hc : ∀ i, ∀ᵐ x ∂μ i, x ∈ Z i) (i : ℕ)
    {f b : X → ℝ} (hf : BoundedLip f) (hb : BoundedLip b)
    {π : Fin k → X → ℝ} (hπ : ∀ j, LipschitzWith 1 (π j)) :
    |T f π - S i b π| ≤ ∫ x, |f x - (Z i).indicator b x| ∂Measure.sum μ := by
  classical
  have hfi := BorelCoefficients.integrable_boundedLip (Measure.sum μ) hf
  have hbi := (BorelCoefficients.integrable_boundedLip (Measure.sum μ) hb).indicator (hZ i)
  let d : ℕ → ℝ := fun j => S j f π - if j = i then S i b π else 0
  have hbd (j : ℕ) : |d j| ≤ ∫ x, |f x-(Z i).indicator b x| ∂μ j := by
    by_cases hji : j = i
    · subst j
      have heq : S i (fun x => f x - b x) π = S i f π - S i b π := by
        simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using
          (hS i).linearFirst f b π 1 (-1) hf hb (fun l => ⟨1,hπ l⟩)
      have hbound := hμ i (fun x => f x-b x) π (by simpa only [neg_one_mul, sub_eq_add_neg] using hf.add (hb.const_mul (-1))) hπ
      rw [heq] at hbound
      change |S i f π - if i = i then S i b π else 0| ≤ _
      rw [ite_eq_left rfl]
      apply hbound.trans_eq
      apply integral_congr_ae
      filter_upwards [hc i] with x hx
      rw [indicator_of_mem hx]
    · have hbound := hμ j f π hf hπ
      change |S j f π - if j = i then S i b π else 0| ≤ _
      rw [ite_eq_right hji,sub_zero]
      apply hbound.trans_eq
      apply integral_congr_ae
      filter_upwards [hc j] with x hx
      have hxi : x ∉ Z i := fun hxi => Set.disjoint_left.mp (hd hji) hx hxi
      rw [indicator_of_notMem hxi,sub_zero]
  have heint : Integrable (fun x => |f x-(Z i).indicator b x|) (Measure.sum μ) :=
    (hfi.sub hbi).abs
  have he : Summable (fun j => ∫ x, |f x-(Z i).indicator b x| ∂μ j) := by
    simpa only [Real.norm_eq_abs,abs_abs] using heint.summable_integral
  have hdS : Summable d := he.of_norm_bounded (fun j => by simpa only [Real.norm_eq_abs] using hbd j)
  have hfS : Summable (fun j => S j f π) := by
    have hfs : Summable (fun j => ∫ x, |f x| ∂μ j) := by
      simpa only [Real.norm_eq_abs,abs_abs] using hfi.abs.summable_integral
    exact hfs.of_norm_bounded (fun j => by simpa only [Real.norm_eq_abs] using hμ j f π hf hπ)
  have hsum : ∑' j, d j = T f π - S i b π := by
    rw [hT f π]
    dsimp only [d]
    rw [hfS.tsum_sub (hasSum_ite_eq i (S i b π)).summable,tsum_ite_eq]
  rw [←hsum,integral_sum_measure heint]
  calc |∑' j, d j| ≤ ∑' j, |d j| := by
        simpa only [Real.norm_eq_abs] using (norm_tsum_le_tsum_norm (f := d) hdS.norm)
    _ ≤ ∑' j, ∫ x, |f x-(Z i).indicator b x| ∂μ j := hdS.abs.tsum_le_tsum hbd he

lemma controls_component_restrict (hS : ∀ i, IsMetricCurrent (S i))
    (hμ : ∀ i, Controls (S i) (μ i))
    (hT : ∀ b π, T b π = ∑' i, S i b π)
    (hZ : ∀ i, MeasurableSet (Z i)) (hd : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    (hc : ∀ i, ∀ᵐ x ∂μ i, x ∈ Z i)
    {ν : Measure X} [IsFiniteMeasure ν] (hν : Controls T ν) (i : ℕ) :
    Controls (S i) (ν.restrict (Z i)) := by
  intro b π hb hπ
  let η := ν + Measure.sum μ
  have hbη : Integrable ((Z i).indicator b) η :=
    (BorelCoefficients.integrable_boundedLip η hb).indicator (hZ i)
  obtain ⟨f,hf⟩ := BorelCoefficients.exists_lipschitz_approximation η hbη
  have hfi (j : ℕ) : Integrable (f j).val η :=
    BorelCoefficients.integrable_boundedLip η (f j).property
  have hleμ : Measure.sum μ ≤ η := Measure.le_add_left le_rfl
  have hleν : ν ≤ η := Measure.le_add_right le_rfl
  have hlim : Tendsto (fun j => T (f j).val π) atTop (𝓝 (S i b π)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hf
    rw [Real.dist_eq]
    apply (component_approximation_bound hS hμ hT hZ hd hc i (f j).property hb hπ).trans
    exact integral_mono_measure hleμ (Eventually.of_forall fun _ => abs_nonneg _)
      ((hfi j).sub hbη).abs
  have hlimν := tendsto_integral_abs_of_l1 hleν hfi hbη hf
  have hle := le_of_tendsto_of_tendsto hlim.abs hlimν
    (Eventually.of_forall fun j => hν _ π (f j).property hπ)
  apply hle.trans_eq
  rw [←integral_indicator (hZ i)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ Z i <;> simp [hx]

end ComponentControls
end SharpIntegralFillings

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma sum_measure_le_of_component_minimal
    {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} {T : Functional X k} {S : ℕ → Functional X k}
    {μ : ℕ → Measure X} [IsFiniteMeasure (Measure.sum μ)]
    {Z : ℕ → Set X}
    (hS : ∀ i, IsMetricCurrent (S i)) (hμ : ∀ i, Controls (S i) (μ i))
    (hmin : ∀ i (ν : Measure X), IsFiniteMeasure ν → Controls (S i) ν → μ i ≤ ν)
    (hT : ∀ b π, T b π = ∑' i, S i b π)
    (hZ : ∀ i, MeasurableSet (Z i)) (hd : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    (hc : ∀ i, ∀ᵐ x ∂μ i, x ∈ Z i)
    {ν : Measure X} [IsFiniteMeasure ν] (hν : Controls T ν) : Measure.sum μ ≤ ν := by
  have hle (i) : μ i ≤ ν.restrict (Z i) :=
    hmin i _ inferInstance (controls_component_restrict hS hμ hT hZ hd hc hν i)
  have hsum : Measure.sum μ ≤ Measure.sum (fun i => ν.restrict (Z i)) := by
    apply Measure.le_iff.mpr
    intro B hB
    simp only [Measure.sum_apply _ hB]
    exact ENNReal.tsum_le_tsum (fun i => hle i B)
  rw [←Measure.restrict_iUnion hd hZ] at hsum
  exact hsum.trans Measure.restrict_le_self

end SharpIntegralFillings

end

end OAI
