import Mathlib
import OAI.Geometry.CAT0Fillings.Reconstruction.Uniqueness
import OAI.Geometry.CAT0Fillings.Reconstruction.GraphCharts

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma IntegralSliceTree.isMetricCurrent {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
    (h : IntegralSliceTree k T) : IsMetricCurrent T := by
  cases k with
  | zero => exact h.1
  | succ k => exact h.choose

lemma ae_superlevelSlice_metric_of_bounded_weak_limit
    {k : ℕ} {Ts : ℕ → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsIntegral (k+1) (Ts j))
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π)))
    (hX : IsCAT0 X) {u : X → ℝ} {Ku : ℝ≥0} (hu : LipschitzWith Ku u) :
    ∀ᵐ t : ℝ, IsMetricCurrent (superlevelSlice hT hB u t) := by
  obtain ⟨hT',hB',hS⟩ := integral_slice_tree_of_bounded_weak_limit hTs M N hM hN hlim hX
  exact (hS u Ku hu).mono fun _ ht => ht.isMetricCurrent

theorem superlevelSlice_borel_integral_of_bounded_weak_limit
    {k : ℕ} {Ts : ℕ → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsIntegral (k+1) (Ts j))
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π)))
    (hX : IsCAT0 X) {u : X → ℝ} {Ku : ℝ≥0} (hu : LipschitzWith Ku u)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    {f : X → ℝ} (hf : Measurable f) (B : ℝ≥0) (hBf : ∀ x, |f x| ≤ B) :
    ActionIntegralAgreement volume T (Matrix.vecCons u π) (superlevelSlice hT hB u) π f := by
  have hρ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (Matrix.vecCons u π i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨Ku,hu⟩
    · exact hπ j
  have hS := ae_superlevelSlice_metric_of_bounded_weak_limit hTs hT hB M N hM hN hlim hX hu
  obtain ⟨g,hg,hg0,hgb,_⟩ :=
    superlevelSlice_mass_bound_of_bounded_weak_limit hTs hT hB M N hM hN hlim hX hu
  refine ActionIntegralAgreement.bounded_measurable hρ hπ hS hg
    (Eventually.of_forall hg0) hgb ?_ hf B hBf
  intro b hb
  have hab : Admissible b π := ⟨hb,hπ⟩
  have ha := superlevelSlice_integral_of_bounded_weak_limit hTs hT hB M N hM hN hlim hX hu hab
  have he : (fun t : ℝ => superlevelSlice hT hB u t b π) =ᵐ[volume]
      (fun t => currentBorelAction (superlevelSlice hT hB u t) b π) :=
    hS.mono fun _ ht => (currentBorelAction_eq_action ht hab).symm
  exact ⟨ha.1.congr he, (currentBorelAction_eq_action hT ⟨hb,hρ⟩).trans
    (ha.2.trans (integral_congr_ae he))⟩

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients BorelRestriction Slicing

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma integral_zero_unitRepresentation {S : Functional X 0} (hS : IsIntegral 0 S) :
    ∃ (m : ℕ) (a : Fin m → ℤ) (x : Fin m → X),
      (∀ i, a i ≠ 0) ∧ Function.Injective x ∧ UnitRepresentation S a x := by
  obtain ⟨m,a,x,ha,hx,he⟩ := integerRectifiable_zero_distinct_representation hS.1 hS.2
  refine ⟨m,a,x,ha,hx,?_⟩
  intro b hb hb1
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  rw [atomCurrent,ite_eq_left ⟨⟨⟨1,hb⟩,1,hb1⟩,fun j => Fin.elim0 j⟩]

lemma graph_atom_mem_iff {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {D : Set ℝ} {m : ℕ}
    (γ : D → Fin m → X)
    {u : X → ℝ} (hbase : ∀ t j, u (γ t j) = t)
    (hinj : ∀ t, Function.Injective (γ t)) (t : D) (i j : Fin m) :
    γ t i ∈ Set.range (fun s => γ s j) ↔ i = j := by
  constructor
  · rintro ⟨s,he⟩
    have ht : s = t := Subtype.ext (by simpa only [hbase] using congrArg u he)
    subst s
    exact (hinj t he).symm
  · rintro rfl
    exact ⟨t,rfl⟩

lemma superlevelSlice_graph_action {T : Functional X 1}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : Continuous u)
    (hI : ∀ᵐ t : ℝ, IsIntegral 0 (superlevelSlice hT hB u t))
    {D : Set ℝ} (hD : IsCompact D) {m : ℕ} (γ : D → Fin m → X)
    (hγ : ∀ j, Continuous (fun t => γ t j)) (a : Fin m → ℤ)
    (hbase : ∀ t j, u (γ t j) = t) (hinj : ∀ t, Function.Injective (γ t))
    (hrep : ∀ t : D, UnitRepresentation (superlevelSlice hT hB u t) a (γ t))
    {b : X → ℝ} (hb : BoundedLip b) (j : Fin m) :
    ∀ᵐ t : ℝ, currentBorelAction (superlevelSlice hT hB u t)
      ((Set.range (fun s => γ s j)).indicator b) (fun z => Fin.elim0 z) =
      if ht : t ∈ D then (a j : ℝ)*b (γ ⟨t,ht⟩ j) else 0 := by
  classical
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let E := Set.range (fun s => γ s j)
  have hE : MeasurableSet E := (isCompact_range (hγ j)).measurableSet
  have hf : Measurable (E.indicator b) := hb.continuous.measurable.indicator hE
  obtain ⟨B,hBb⟩ := hb.2
  let B' : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  have hfB (x : X) : |E.indicator b x| ≤ B' := by
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]
      exact (hBb x).trans (le_max_left _ _)
    · rw [indicator_of_notMem hx,abs_zero]
      exact B'.coe_nonneg
  filter_upwards [hI] with t htI
  by_cases ht : t ∈ D
  · rw [dite_eq_left ht,(hrep ⟨t,ht⟩).borelAction htI.1 hf hfB]
    rw [Finset.sum_eq_single j]
    · rw [indicator_of_mem (show γ ⟨t,ht⟩ j ∈ E from ⟨⟨t,ht⟩,rfl⟩)]
    · intro i _ hij
      rw [indicator_of_notMem ((graph_atom_mem_iff γ hbase hinj ⟨t,ht⟩ i j).not.mpr hij),mul_zero]
    · simp
  · rw [dite_eq_right ht]
    obtain ⟨q,c,x,hc,hx,hrep'⟩ := integral_zero_unitRepresentation htI
    apply hrep'.borelAction_zero htI.1 hf
    intro i
    apply indicator_of_notMem
    rintro ⟨s,he⟩
    have hlevel := unitRepresentation_atoms_on_level hT hB hu t hc hx hrep' i
    rw [←he,hbase] at hlevel
    exact ht (hlevel ▸ s.property)

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients BorelRestriction Slicing

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma joint_graph_atom_mem_iff {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ} {D : Set (Euc k)} {m : ℕ}
    (γ : D → Fin m → X)
    {π : Fin k → X → ℝ} (hbase : ∀ t j, coordinateMap π (γ t j) = t)
    (hinj : ∀ t, Function.Injective (γ t)) (t : D) (i j : Fin m) :
    γ t i ∈ Set.range (fun s => γ s j) ↔ i = j := by
  constructor
  · rintro ⟨s,he⟩
    have ht : s = t := Subtype.ext (by simpa only [hbase] using congrArg (coordinateMap π) he)
    subst s
    exact (hinj t he).symm
  · rintro rfl
    exact ⟨t,rfl⟩

lemma fullSlice_graph_action {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {D : Set (Euc k)} (hD : IsCompact D) {m : ℕ} (γ : D → Fin m → X)
    (hγ : ∀ j, Continuous (fun t => γ t j)) (a : Fin m → ℤ)
    (hbase : ∀ t j, coordinateMap π (γ t j) = t) (hinj : ∀ t, Function.Injective (γ t))
    (hrep : ∀ t : D, UnitRepresentation (fullSlice h π t) a (γ t))
    {b : X → ℝ} (hb : BoundedLip b) (j : Fin m) :
    ∀ᵐ z : Euc k, currentBorelAction (fullSlice h π z)
      ((Set.range (fun s => γ s j)).indicator b) (fun i => Fin.elim0 i) =
      if hz : z ∈ D then (a j : ℝ)*b (γ ⟨z,hz⟩ j) else 0 := by
  classical
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let E := Set.range (fun s => γ s j)
  have hE : MeasurableSet E := (isCompact_range (hγ j)).measurableSet
  have hf : Measurable (E.indicator b) := hb.continuous.measurable.indicator hE
  obtain ⟨B,hBb⟩ := hb.2
  let B' : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  have hfB (x : X) : |E.indicator b x| ≤ B' := by
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]
      exact (hBb x).trans (le_max_left _ _)
    · rw [indicator_of_notMem hx,abs_zero]
      exact B'.coe_nonneg
  have hA : Continuous (coordinateMap π) := by
    exact (parameterEquiv k).continuous.comp (continuous_pi fun i => (hπ i).continuous)
  filter_upwards [ae_fullSlice_mass_fiber h hX π hπ] with z hzM
  have hI := fullSlice_integral h π z
  by_cases hz : z ∈ D
  · rw [dite_eq_left hz,(hrep ⟨z,hz⟩).borelAction hI.1 hf hfB]
    rw [Finset.sum_eq_single j]
    · rw [indicator_of_mem (show γ ⟨z,hz⟩ j ∈ E from ⟨⟨z,hz⟩,rfl⟩)]
    · intro i _ hij
      rw [indicator_of_notMem ((joint_graph_atom_mem_iff γ hbase hinj ⟨z,hz⟩ i j).not.mpr hij),mul_zero]
    · simp
  · rw [dite_eq_right hz]
    obtain ⟨q,c,x,hc,hx,hrep'⟩ := integral_zero_unitRepresentation hI
    apply hrep'.borelAction_zero hI.1 hf
    intro i
    apply indicator_of_notMem
    rintro ⟨s,he⟩
    have hlevel := hrep'.atom_in_carrier hI.1 hc hx
      (measurableSet_eq_fun hA.measurable measurable_const) hzM i
    change coordinateMap π (x i) = z at hlevel
    rw [←he,hbase] at hlevel
    exact hz (hlevel ▸ s.property)

lemma full_graph_restriction_base_action {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {D : Set (Euc k)} (hD : IsCompact D) {m : ℕ} (γ : D → Fin m → X)
    (hγ : ∀ j, ∃ L U : ℝ≥0, LipschitzWith L (fun t => γ t j) ∧
      AntilipschitzWith U (fun t => γ t j)) (a : Fin m → ℤ)
    (hbase : ∀ t j, coordinateMap π (γ t j) = t) (hinj : ∀ t, Function.Injective (γ t))
    (hrep : ∀ t : D, UnitRepresentation (fullSlice h π t) a (γ t))
    (j : Fin m) {b : X → ℝ} (hb : BoundedLip b) :
    restrictCurrent h.metric (Set.range (fun t => γ t j)) b π =
      (jointGraphChart hD (fun t => γ t j) (hγ j) (a j)).action b π := by
  classical
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let E := Set.range (fun t => γ t j)
  have hγc (i : Fin m) : Continuous (fun t => γ t i) := (hγ i).choose_spec.choose_spec.1.continuous
  have hE : MeasurableSet E := (isCompact_range (hγc j)).measurableSet
  let f := E.indicator b
  have hf : Measurable f := hb.continuous.measurable.indicator hE
  obtain ⟨B,hBb⟩ := hb.2
  let B' : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  have hfB (x : X) : |f x| ≤ B' := by
    by_cases hx : x ∈ E
    · exact (by simpa only [f,indicator_of_mem hx] using (show |b x| ≤ B' from (hBb x).trans (le_max_left B 0)))
    · simp only [f,indicator_of_notMem hx,abs_zero]
      exact B'.coe_nonneg
  have ha := fullSlice_borel_integral h hX π hπ hf B' hfB
  have hs := fullSlice_graph_action h hX π hπ hD γ hγc a hbase hinj hrep hb j
  rw [restrictCurrent_apply h.metric E ⟨hb,fun i => (hπ i).1⟩,
    ←currentBorelAction_eq h.metric f π,ha.2]
  rw [jointGraphChart_base_action hD _ (hγ j) (a j) π (fun i => (hπ i).1) (by
    intro t i
    exact congrArg (fun z : Euc k => z i) (hbase t j)) hb]
  rw [←integral_indicator hD.measurableSet]
  apply integral_congr_ae
  filter_upwards [hs] with z hz
  rw [hz]
  by_cases hzD : z ∈ D
  · simp only [dite_eq_left hzD,indicator_of_mem hzD,jointGraphFunction]
  · simp only [dite_eq_right hzD,indicator_of_notMem hzD]

end CAT0Fillings.SliceReconstruction
end

end OAI
