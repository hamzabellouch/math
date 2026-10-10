import Mathlib
import OAI.Geometry.CAT0Fillings.Swept.Current

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal MatrixOrder

namespace CAT0Fillings
open CurrentOperations BorelCoefficients

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma chart_controls_total (i : ℕ) : Controls (q.chart i).action
    (MassMeasure.currentMassMeasure hT) := by
  have hle : (q.chart i).majorantMeasure (fun z => Real.sqrt (q.gram i z).det) ≤
      MassMeasure.currentMassMeasure hT := by
    rw [q.measure_eq]
    exact Measure.le_sum (fun index => (q.chart index).majorantMeasure
      (fun point => Real.sqrt (q.gram index point).det)) i
  intro b π hab hπ
  apply (q.control i b π hab hπ).trans
  apply integral_mono_measure hle
  · exact Eventually.of_forall fun _ => abs_nonneg _
  · exact (integrable_boundedLip _ hab).abs

lemma exists_positive_integer_region (hM : 0 < mass T) :
    ∃ (i : ℕ) (s : Set (Euc k)), MeasurableSet s ∧ s ⊆ (q.chart i).domain ∧
      volume s ≠ 0 ∧ ∀ᵐ z ∂volume.restrict s, 1 ≤ |((q.chart i).multiplicity z : ℝ)| := by
  have hi : ∃ i, 0 < mass (q.chart i).action := by
    by_contra! hi
    have : (∑' i, mass (q.chart i).action) ≤ 0 := tsum_nonpos hi
    rw [←q.total_mass] at this
    exact (not_le_of_gt hM) this
  obtain ⟨i,hi⟩ := hi
  let C := q.chart i
  let hg := C.integrable.aestronglyMeasurable
  let g : Euc k → ℝ := hg.mk (fun z => (C.multiplicity z : ℝ))
  have hgm : Measurable g := hg.stronglyMeasurable_mk.measurable
  have hge : (fun z => (C.multiplicity z : ℝ)) =ᵐ[volume.restrict C.domain] g := hg.ae_eq_mk
  have hgn : MeasurableSet {z | g z ≠ 0} := (hgm (measurableSet_singleton 0)).compl
  let s := C.domain ∩ {z | g z ≠ 0}
  have hs : MeasurableSet s := C.borel.inter hgn
  have hss : s ⊆ C.domain := inter_subset_left
  have hs0 : volume s ≠ 0 := by
    intro hs0
    have hge0 : g =ᵐ[volume.restrict C.domain] 0 := by
      rw [EventuallyEq,ae_iff]
      change (volume.restrict C.domain) {z | g z ≠ 0} = 0
      rw [Measure.restrict_apply hgn,inter_comm]
      exact hs0
    have hm0 : (fun z => (C.multiplicity z : ℝ)) =ᵐ[volume.restrict C.domain] 0 := hge.trans hge0
    have hm : mass C.action = 0 := by
      rw [q.chart_mass i]
      apply integral_eq_zero_of_ae
      filter_upwards [hm0] with z hz
      change (C.multiplicity z : ℝ) = 0 at hz
      change |(C.multiplicity z : ℝ)| * _ = 0
      rw [hz,abs_zero,zero_mul]
    exact hi.ne' hm
  refine ⟨i,s,hs,hss,hs0,?_⟩
  have hget := hge.filter_mono (ae_mono (Measure.restrict_mono hss le_rfl))
  filter_upwards [hget,ae_restrict_mem hs] with z hz hzs
  have hn : C.multiplicity z ≠ 0 := by
    intro hh
    exact hzs.2 (by rw [←hz,hh,Int.cast_zero])
  exact_mod_cast Int.one_le_abs hn

lemma exists_positive_near_hilbert_piece (hX : IsCAT0 X) (hM : 0 < mass T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (i : ℕ) (s : Set (Euc k)) (p : Seminorm ℝ (Euc k)),
      MeasurableSet s ∧ s ⊆ (q.chart i).domain ∧ volume s ≠ 0 ∧
      (∀ᵐ z ∂volume.restrict s, 1 ≤ |((q.chart i).multiplicity z : ℝ)|) ∧
      (∀ v, p v = 0 ↔ v = 0) ∧
      (∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) ∧
      ∀ y ∈ s, ∀ z ∈ s,
        (1-ε)*p (y-z) ≤ dist ((q.chart i).paramExtended y) ((q.chart i).paramExtended z) ∧
        dist ((q.chart i).paramExtended y) ((q.chart i).paramExtended z) ≤ (1+ε)*p (y-z) := by
  obtain ⟨i,s,hs,hss,hs0,hθ⟩ := q.exists_positive_integer_region hM
  let C := q.chart i
  obtain ⟨A,B,hA,hB⟩ := C.bilipschitz
  obtain ⟨p,t,ht,hts,hdis,hnull,hLip,hp,hnear⟩ :=
    MetricDifferentiation.exists_hilbertian_nearIsometric_chart_partition volume
      C.borel C.bounded.measure_lt_top.ne hA hB
      (fun a b c d => hX.quadrilateral (C.param a) (C.param b) (C.param c) (C.param d)) hε
  have hj : ∃ j, volume (s ∩ t j) ≠ 0 := by
    by_contra! hj
    have hcov : s ⊆ (C.domain \ ⋃ j, t j) ∪ ⋃ j, s ∩ t j := by
      intro z hz
      by_cases hh : z ∈ ⋃ j, t j
      · right
        obtain ⟨j,hj⟩ := mem_iUnion.mp hh
        exact mem_iUnion.mpr ⟨j,hz,hj⟩
      · exact Or.inl ⟨hss hz,hh⟩
    exact hs0 (measure_mono_null hcov (measure_union_null hnull (measure_iUnion_null hj)))
  obtain ⟨j,hj⟩ := hj
  have hne : (t j).Nonempty := (nonempty_of_measure_ne_zero hj).mono inter_subset_right
  refine ⟨i,s ∩ t j,p j,hs.inter (ht j),inter_subset_left.trans hss,hj,
    hθ.filter_mono (ae_mono (Measure.restrict_mono inter_subset_left le_rfl)),?_,(hp j hne).1,?_⟩
  · intro v
    constructor
    · intro hv
      have hh := (hp j hne).2 v
      rw [hv,mul_zero] at hh
      exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg v))
    · rintro rfl
      exact map_zero _
  · intro y hy z hz
    simpa only [IntegerChart.paramExtended,dite_eq_left (hss hy.1),dite_eq_left (hss hz.1)] using
      hnear j ⟨y,hss hy.1⟩ hy.2 ⟨z,hss hz.1⟩ hz.2

end ChartGeometry
end CAT0Fillings
end

end OAI
