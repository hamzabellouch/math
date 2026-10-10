import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.Superlevels

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
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
open Set MeasureTheory Filter Foundations BorelRestriction MassMeasure
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma boundarySucc_sub {k : ℕ} (T U : Functional X (k+1)) :
    boundarySucc (T-U) = boundarySucc T - boundarySucc U := by
  funext b π
  by_cases h : Admissible b π <;> simp [boundarySucc,h]

omit [BorelSpace X] [CompactSpace X] in
lemma IsIntegral.boundarySucc {k : ℕ} {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) :
    IsIntegral k (boundarySucc T) := by
  cases k with
  | zero => exact hT.2.2
  | succ k =>
    refine ⟨hT.2.2.1,hT.2.2.2,?_,?_⟩ <;> rw [Foundations.boundarySucc_boundarySucc hT.1]
    · exact isMetricCurrent_zero k
    · exact integerRectifiable_zero k

lemma IsIntegral.sub [Nonempty X] {k : ℕ} {T U : Functional X k}
    (hT : IsIntegral k T) (hU : IsIntegral k U) : IsIntegral k (T-U) := by
  cases k with
  | zero =>
    change IsMetricCurrent (T-U) ∧ IntegerRectifiable (T-U)
    simpa only [sub_eq_add_neg] using
      And.intro (hT.1.add hU.1.neg) (hT.2.add hT.1 hU.1.neg hU.2.neg)
  | succ k =>
    have hmain : IsMetricCurrent (T-U) ∧ IntegerRectifiable (T-U) := by
      simpa only [sub_eq_add_neg] using
        And.intro (hT.1.add hU.1.neg) (hT.2.1.add hT.1 hU.1.neg hU.2.1.neg)
    refine ⟨hmain.1,hmain.2,?_,?_⟩ <;> rw [boundarySucc_sub,sub_eq_add_neg]
    · exact hT.2.2.1.add hU.2.2.1.neg
    · exact hT.2.2.2.add hT.2.2.1 hU.2.2.1.neg hU.2.2.2.neg

namespace Slicing

lemma restrictCurrent_zero_of_eq_zero {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (hzero : T = 0) {E : Set X} (hE : MeasurableSet E) :
    restrictCurrent hT E = 0 := by
  apply (restrictCurrent_isMetricCurrent hT hE).eq_zero_of_mass_eq_zero
  apply le_antisymm _ (mass_nonneg _)
  rw [restriction_mass hT hE]
  have hm := ENNReal.toReal_mono (measure_ne_top (currentMassMeasure hT) univ)
    (measure_mono (subset_univ E) : currentMassMeasure hT E ≤ currentMassMeasure hT univ)
  change (currentMassMeasure hT).real E ≤ (currentMassMeasure hT).real univ at hm
  rw [currentMassMeasure_total] at hm
  have hz : mass T = 0 := by rw [hzero]; exact mass_zero k
  exact hm.trans_eq hz

lemma boundary_superlevelSlice {k : ℕ} {T : Functional X (k+1+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    (hBB : IsMetricCurrent (boundarySucc (boundarySucc T)))
    {u : X → ℝ} (hu : BoundedLip u) (t : ℝ) :
    boundarySucc (superlevelSlice hT hB u t) = -superlevelSlice hB hBB u t := by
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.continuous.measurable
  have hzero := Foundations.boundarySucc_boundarySucc hT
  have hrzero := restrictCurrent_zero_of_eq_zero hBB hzero hE
  unfold superlevelSlice
  rw [boundarySucc_sub,Foundations.boundarySucc_boundarySucc (restrictCurrent_isMetricCurrent hT hE),hrzero]
  change (boundarySucc (restrictCurrent hB {x | t < u x}) - 0) = -(0 - boundarySucc (restrictCurrent hB {x | t < u x}))
  simp only [sub_zero,zero_sub,neg_neg]

lemma ae_superlevelSlice_integral [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∀ᵐ t : ℝ, IsIntegral k (superlevelSlice hT.1 hT.2.2.1 u t) := by
  obtain ⟨G,_,_,_,hrest⟩ := ae_integral_restrict hT hX hK
  cases k with
  | zero =>
    filter_upwards [hrest] with t ht
    have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hK.continuous.measurable
    have hB : IsIntegral 0 (restrictCurrent hT.2.2.1 {x | t < u x}) :=
      ⟨restrictCurrent_isMetricCurrent hT.2.2.1 hE,integerRectifiable_restrict hT.2.2.1 hT.2.2.2 hE⟩
    exact hB.sub ht.1.boundarySucc
  | succ k =>
    obtain ⟨H,_,_,_,hBr⟩ := ae_integral_restrict hT.boundarySucc hX hK
    filter_upwards [hrest,hBr] with t ht hbt
    exact hbt.1.sub ht.1.boundarySucc

lemma superlevelSlice_normal_coarea_bound [Nonempty X] {k : ℕ} {T : Functional X (k+1+1)}
    (hT : IsIntegral (k+1+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ G H : ℝ → ℝ, Integrable G ∧ Integrable H ∧
      (∀ t, 0 ≤ G t) ∧ (∀ t, 0 ≤ H t) ∧
      (∫ t : ℝ, G t) ≤ K*mass T ∧ (∫ t : ℝ, H t) ≤ K*mass (boundarySucc T) ∧
      ∀ᵐ t : ℝ, IsIntegral (k+1) (superlevelSlice hT.1 hT.2.2.1 u t) ∧
        mass (superlevelSlice hT.1 hT.2.2.1 u t) ≤ G t ∧
        mass (boundarySucc (superlevelSlice hT.1 hT.2.2.1 u t)) ≤ H t := by
  have hu : BoundedLip u := ⟨⟨K,hK⟩,by
    obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuous.continuousOn
    exact ⟨M,fun x => by simpa only [Real.norm_eq_abs] using hM x (mem_univ _)⟩⟩
  obtain ⟨G,hG,hG0,hGI,hS⟩ := superlevelSlice_coarea_bound hT hX hK
  obtain ⟨H,hH,hH0,hHI,hBS⟩ := superlevelSlice_coarea_bound hT.boundarySucc hX hK
  refine ⟨G,H,hG,hH,hG0,hH0,hGI,hHI,?_⟩
  filter_upwards [hS,hBS,ae_superlevelSlice_integral hT hX hK] with t ht hbt hIt
  refine ⟨hIt,ht.2.2,?_⟩
  have hBB : IsMetricCurrent (boundarySucc (boundarySucc T)) := by
    rw [Foundations.boundarySucc_boundarySucc hT.1]
    exact isMetricCurrent_zero k
  rw [boundary_superlevelSlice hT.1 hT.2.2.1 hBB hu t,mass_neg]
  exact hbt.2.2

end Slicing
end CAT0Fillings
end

end OAI
