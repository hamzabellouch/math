import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Restriction
import OAI.Geometry.CAT0Fillings.Currents.ActionLimits

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
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

lemma sum_disjoint_indicators {X : Type*} (Z : ℕ → Set X)
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j))) (b : X → ℝ)
    (s : Finset ℕ) (x : X) :
    ∑ i ∈ s, (Z i).indicator b x = (⋃ i ∈ s, Z i).indicator b x := by
  classical
  by_cases h : ∃ i ∈ s, x ∈ Z i
  · obtain ⟨i,hi,hxi⟩ := h
    rw [indicator_of_mem (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hxi⟩⟩)]
    rw [Finset.sum_eq_single i]
    · exact indicator_of_mem hxi b
    · intro j _ hji
      exact indicator_of_notMem (fun hxj => Set.disjoint_left.mp (hd hji) hxj hxi) b
    · exact fun h => (h hi).elim
  · have hnot : x ∉ ⋃ i ∈ s, Z i := by simpa only [mem_iUnion,exists_prop] using h
    rw [indicator_of_notMem hnot]
    exact Finset.sum_eq_zero fun i hi => indicator_of_notMem (fun hx => h ⟨i,hi,hx⟩) b

namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} {T : Functional X k} (μ : Measure X) [IsFiniteMeasure μ]

lemma borelAction_finset_sum (hT : IsMetricCurrent T) (f : ℕ → X → ℝ)
    (hf : ∀ i, Integrable (f i) μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) (s : Finset ℕ) :
    borelAction μ hT (∑ i ∈ s, f i) π = ∑ i ∈ s, borelAction μ hT (f i) π := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [borelAction_of_integrable μ hT (integrable_zero X ℝ μ) π hπ]
      change l1Action μ hT π hπ 0 = 0
      exact map_zero _
  | @insert i s hi ih =>
      have hs : Integrable (∑ j ∈ s, f j) μ := by
        exact integrable_finsetSum' s (fun j _ => hf j)
      rw [Finset.sum_insert hi,Finset.sum_insert hi,borelAction_add μ hT (hf i) hs π hπ,ih]

lemma borelAction_iUnion (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (Z : ℕ → Set X) (hZ : ∀ i, MeasurableSet (Z i))
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    {b : X → ℝ} (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    HasSum (fun i => borelAction μ hT ((Z i).indicator b) π)
      (borelAction μ hT ((⋃ i, Z i).indicator b) π) := by
  classical
  let g := (⋃ i, Z i).indicator b
  let f (j : ℕ) := (⋃ i ∈ Finset.range j, Z i).indicator b
  have hfi j : Integrable (f j) μ := hb.indicator (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hZ i)
  have hg : Integrable g μ := hb.indicator (MeasurableSet.iUnion hZ)
  have heq j : f j = ∑ i ∈ Finset.range j, (Z i).indicator b := by
    ext x
    simpa only [Finset.sum_apply] using (sum_disjoint_indicators Z hd b (Finset.range j) x).symm
  have hlimx (x : X) : ∀ᶠ j : ℕ in atTop, f j x = g x := by
    by_cases hx : x ∈ ⋃ i, Z i
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      filter_upwards [eventually_ge_atTop (i+1)] with j hj
      change (⋃ i ∈ Finset.range j, Z i).indicator b x = (⋃ i, Z i).indicator b x
      rw [indicator_of_mem hx,indicator_of_mem
        (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),hi⟩⟩)]
    · exact Eventually.of_forall fun j => by
        have hxj : x ∉ ⋃ i ∈ Finset.range j, Z i := by
          intro hj
          obtain ⟨i,hi⟩ := mem_iUnion.mp hj
          obtain ⟨_,hxi⟩ := mem_iUnion.mp hi
          exact hx (mem_iUnion.mpr ⟨i,hxi⟩)
        change (⋃ i ∈ Finset.range j, Z i).indicator b x = (⋃ i, Z i).indicator b x
        rw [indicator_of_notMem hx,indicator_of_notMem hxj]
  have hbound j x : |f j x-g x| ≤ |b x|+|b x| := by
    exact (abs_sub _ _).trans (add_le_add (by simpa only [Real.norm_eq_abs] using norm_indicator_le_norm_self (s := _) b x)
      (by simpa only [Real.norm_eq_abs] using norm_indicator_le_norm_self (s := _) b x))
  have hlim : Tendsto (fun j => ∫ x, |f j x-g x| ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (fun x => |b x|+|b x|)
      (fun j => ((hfi j).sub hg).abs.aestronglyMeasurable) (hb.abs.add hb.abs)
      (fun j => Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs,abs_abs,Pi.sub_apply] using hbound j x)
      (Eventually.of_forall fun x =>
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
          ((hlimx x).mono fun j hj => by change 0 = |f j x-g x|; rw [hj,sub_self,abs_zero]))
    simpa only [integral_zero,Pi.sub_apply] using ht
  have ht := borelAction_tendsto μ hT hμ hg hfi hlim π hπ
  have htsum : Summable (fun i => borelAction μ hT ((Z i).indicator b) π) := by
    choose K hK using hπ
    have hsum : Summable (fun i => ∫ x, |(Z i).indicator b x| ∂μ) := by
      have hmeas : (Measure.sum (fun i => μ.restrict (Z i))) = μ.restrict (⋃ i, Z i) :=
        (Measure.restrict_iUnion hd hZ).symm
      have hI : Integrable (fun x => |b x|) (Measure.sum (fun i => μ.restrict (Z i))) := by
        rw [hmeas]
        exact hb.abs.restrict
      convert hI.summable_integral using 1
      ext i
      rw [←integral_indicator (hZ i)]
      exact integral_congr_ae (Eventually.of_forall fun x => by
        by_cases hx : x ∈ Z i <;> simp [hx])
    apply (hsum.mul_left (∏ i, (K i : ℝ))).of_norm_bounded
    exact fun i => borelAction_bound μ hT hμ (hb.indicator (hZ i)) π K hK
  apply (hasSum_iff_tendsto_nat_of_summable_norm htsum.norm).mpr
  convert ht using 1
  ext j
  rw [heq,borelAction_finset_sum μ hT _ (fun i => hb.indicator (hZ i)) π hπ]

end BorelCoefficients
end CAT0Fillings
namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology

namespace BorelRestriction
open BorelCoefficients MassMeasure

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} {T : Functional X k}

lemma restrictCurrent_iUnion (hT : IsMetricCurrent T)
    (Z : ℕ → Set X) (hZ : ∀ i, MeasurableSet (Z i))
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j))) (b : X → ℝ) (π : Fin k → X → ℝ) :
    restrictCurrent hT (⋃ i, Z i) b π = ∑' i, restrictCurrent hT (Z i) b π := by
  by_cases hab : Admissible b π
  · simp_rw [restrictCurrent_apply hT _ hab]
    exact (borelAction_iUnion (currentMassMeasure hT) hT (currentMassMeasure_controls hT)
      Z hZ hd (integrable_boundedLip _ hab.1) π hab.2).tsum_eq.symm
  · rw [(restrictCurrent_isMetricCurrent hT (MeasurableSet.iUnion hZ)).offDomain b π hab]
    symm
    calc (∑' i, restrictCurrent hT (Z i) b π) = ∑' (_i : ℕ), (0 : ℝ) :=
            tsum_congr fun i => (restrictCurrent_isMetricCurrent hT (hZ i)).offDomain b π hab
      _ = 0 := tsum_zero

lemma summable_restriction_mass (hT : IsMetricCurrent T)
    (Z : ℕ → Set X) (hZ : ∀ i, MeasurableSet (Z i))
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j))) :
    Summable (fun i => mass (restrictCurrent hT (Z i))) := by
  simp_rw [restriction_mass hT (hZ _)]
  exact summable_measure_toReal hZ hd

lemma tsum_restriction_mass_le (hT : IsMetricCurrent T)
    (Z : ℕ → Set X) (hZ : ∀ i, MeasurableSet (Z i))
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j))) :
    (∑' i, mass (restrictCurrent hT (Z i))) ≤ mass T := by
  simp_rw [restriction_mass hT (hZ _),Measure.real]
  rw [← ENNReal.tsum_toReal_eq (fun i => measure_ne_top _ _),←measure_iUnion hd hZ]
  change (currentMassMeasure hT).real (⋃ i, Z i) ≤ mass T
  rw [←currentMassMeasure_total hT]
  exact measureReal_mono (subset_univ _)

end BorelRestriction
end CAT0Fillings

end

end OAI
