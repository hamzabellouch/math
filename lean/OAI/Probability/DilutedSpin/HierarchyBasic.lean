import OAI.Probability.DilutedSpin.PhysicalOverlapLimit

namespace OAI

section
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal

namespace DilutedSpinGlass

abbrev AtomicWeights (ι : Type*) [Fintype ι] := {w : ι → ℝ≥0 // ∑ i, w i = 1}

noncomputable def atomicProbability {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (x : ι → X) (w : AtomicWeights ι) : ProbabilityMeasure X :=
  ⟨∑ i, (w.val i : ℝ≥0∞) • Measure.dirac (x i), {
    measure_univ := by simp [← ENNReal.ofNNReal_finsetSum, w.property] }⟩

 theorem integral_atomicProbability {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    [MeasurableSingletonClass X] (x : ι → X) (w : AtomicWeights ι) (f : X → ℝ) :
    ∫ t, f t ∂(atomicProbability x w) = ∑ i, (w.val i : ℝ) * f (x i) := by
  change (∫ t, f t ∂(∑ i, (w.val i : ℝ≥0∞) • Measure.dirac (x i))) = _
  rw [integral_finsetSum_measure]
  · simp [NNReal.smul_def]
  · intro i _
    exact (integrable_dirac (by simp : ‖f (x i)‖ₑ < ∞)).smul_measure (by simp)

 theorem continuous_atomicProbability {X ι : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [T1Space X] [Fintype ι] (x : ι → X) :
    Continuous (atomicProbability x) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  simp_rw [integral_atomicProbability]
  exact continuous_finsetSum _ (fun i _ =>
    (NNReal.continuous_coe.comp ((continuous_apply i).comp continuous_subtype_val)).mul
      continuous_const)

end DilutedSpinGlass

namespace DilutedSpinGlass

 theorem simple_map_atomic {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (s : SimpleFunc X X) (μ : ProbabilityMeasure X) :
    μ.map s ∈ Set.range (atomicProbability (fun x : s.range => (x : X))) := by
  classical
  have hmap : μ.toMeasure.map s = ∑ a ∈ s.range, μ.toMeasure (s ⁻¹' {a}) • Measure.dirac a :=
    (Measure.ae_mem_finset_iff_map_eq_sum_dirac s.measurable.aemeasurable).mp
      (Eventually.of_forall s.mem_range_self)
  let w : s.range → ℝ≥0 := fun a => μ (s ⁻¹' {a.val})
  have hw : ∑ a, w a = 1 := by
    apply ENNReal.coe_injective
    have hh : (∑ a ∈ s.range, μ.toMeasure (s ⁻¹' {a})) = 1 := by
      simpa [Measure.map_apply s.measurable MeasurableSet.univ] using
        congrArg (fun ν : Measure X => ν Set.univ) hmap.symm
    calc
      ((∑ a, w a : ℝ≥0) : ℝ≥0∞) = ∑ a : s.range, μ.toMeasure (s ⁻¹' {a.val}) := by
        simp [w]
      _ = ∑ a ∈ s.range, μ.toMeasure (s ⁻¹' {a}) :=
        Finset.sum_coe_sort s.range (fun a => μ.toMeasure (s ⁻¹' {a}))
      _ = 1 := hh
  refine ⟨⟨w, hw⟩, ?_⟩
  apply Subtype.ext
  change (∑ a : s.range, (w a : ℝ≥0∞) • Measure.dirac (a : X)) = μ.toMeasure.map s
  rw [hmap]
  simpa [w] using
    (Finset.sum_coe_sort s.range (fun a => μ.toMeasure (s ⁻¹' {a}) • Measure.dirac a))

end DilutedSpinGlass

namespace DilutedSpinGlass

 theorem probability_map_tendsto {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure X)
    (s : ℕ → SimpleFunc X X) (hs : ∀ x, Tendsto (fun n => s n x) atTop (𝓝 x)) :
    Tendsto (fun n => μ.map (s n)) atTop (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hmap (n : ℕ) : (∫ x, f x ∂(μ.map (s n))) =
      ∫ x, f (s n x) ∂μ := by
    rw [ProbabilityMeasure.toMeasure_map, integral_map (s n).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
  simp_rw [hmap]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro n
    exact (f.continuous.measurable.comp (s n).measurable).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall (fun x => f.norm_coe_le_norm (s n x))
  · exact Eventually.of_forall (fun x => f.continuous.continuousAt.tendsto.comp (hs x))

/-- The missing recursive weak-hierarchy infrastructure: probability laws on
separable metric Borel spaces form a separable space for the actual weak
 topology. The finite approximations are global, not chosen separately by μ. -/
theorem probabilityMeasure_separable {X : Type*} [MetricSpace X]
    [SeparableSpace X] [MeasurableSpace X] [BorelSpace X] :
    SeparableSpace (ProbabilityMeasure X) := by
  classical
  let h : StronglyMeasurable (id : X → X) := stronglyMeasurable_id
  let s := h.approx
  let D : Set (ProbabilityMeasure X) := ⋃ n, Set.range
    (atomicProbability (fun x : (s n).range => (x : X)))
  have hD : IsSeparable D := by
    apply IsSeparable.iUnion
    intro n
    exact isSeparable_range (continuous_atomicProbability _)
  apply (Dense.isSeparable_iff ?_).mp hD
  intro μ
  apply isClosed_closure.mem_of_tendsto (probability_map_tendsto μ s h.tendsto_approx)
  apply Eventually.of_forall
  intro n
  apply subset_closure
  exact Set.mem_iUnion.mpr ⟨n, simple_map_atomic (s n) μ⟩

end DilutedSpinGlass
namespace DilutedSpinGlass
open TopologicalSpace
open scoped BoundedContinuousFunction
local instance hierarchyBasicMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space
local instance hierarchyBasicBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

theorem hierarchy_properties (r : ℕ) : MetrizableSpace (Hierarchy r) ∧
    SeparableSpace (Hierarchy r) := by
  induction r with
  | zero => exact ⟨inferInstanceAs (MetrizableSpace ℝ), inferInstanceAs (SeparableSpace ℝ)⟩
  | succ r ih =>
    let : MetrizableSpace (Hierarchy r) := ih.1
    let : SeparableSpace (Hierarchy r) := ih.2
    let : MetricSpace (Hierarchy r) := metrizableSpaceMetric (Hierarchy r)
    exact ⟨inferInstanceAs (MetrizableSpace (ProbabilityMeasure (Hierarchy r))),
      probabilityMeasure_separable (X := Hierarchy r)⟩

instance hierarchyMetrizable (r : ℕ) : MetrizableSpace (Hierarchy r) :=
  (hierarchy_properties r).1
instance hierarchySeparable (r : ℕ) : SeparableSpace (Hierarchy r) :=
  (hierarchy_properties r).2

instance hierarchySecondCountable (r : ℕ) : SecondCountableTopology (Hierarchy r) := by
  let : MetricSpace (Hierarchy r) := metrizableSpaceMetric (Hierarchy r)
  infer_instance

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance hierarchyBasicDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type

noncomputable def nodes (k : ℕ+) (hk : 2≤(k:ℕ)) (s : Finset ReducedTopology) : Finset ReducedTopology :=
  Finset.univ.image (fun C : Fin k → {T // T∈s} => ReducedTopology.node k hk (fun j => (C j).val))

lemma mem_nodes (k : ℕ+) (hk : 2≤(k:ℕ)) (s : Finset ReducedTopology)
    (C : Fin k → ReducedTopology) (hC : ∀ j, C j∈s) : .node k hk C∈nodes k hk s := by
  exact Finset.mem_image.mpr ⟨fun j => ⟨C j,hC j⟩,Finset.mem_univ _,rfl⟩

noncomputable def boundedTopologies : ℕ → Finset ReducedTopology
  | 0 => {.leaf}
  | n+1 => {.leaf} ∪ (Finset.univ : Finset (Fin (n+2))).biUnion
      (fun j => if h : 2≤j.val then nodes ⟨j.val,by omega⟩ h (boundedTopologies n) else ∅)

lemma node_arity_le_leaf_card (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology) :
    (k:ℕ)≤Fintype.card (ReducedTopology.node k hk C).Leaf := by
  change _≤Fintype.card ((j : Fin k) × (C j).Leaf)
  rw [Fintype.card_sigma]
  have := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin k) _ => Nat.succ_le_iff.mpr (leaf_card_pos (C j)))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.succ_eq_add_one,zero_add,mul_one] using this

lemma mem_boundedTopologies (n : ℕ) (S : ReducedTopology)
    (h : Fintype.card S.Leaf≤n) : S∈boundedTopologies n := by
  induction n generalizing S with
  | zero => have := leaf_card_pos S; omega
  | succ n ih =>
    cases S with
    | leaf => exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    | node k hk C =>
      apply Finset.mem_union_right
      have hk' := (node_arity_le_leaf_card k hk C).trans h
      apply Finset.mem_biUnion.mpr
      refine ⟨⟨k,by omega⟩,Finset.mem_univ _,?_⟩
      simp only [dite_true,hk]
      apply mem_nodes
      intro j
      apply ih
      have := child_leaf_card_lt k hk C j
      omega

end DilutedSpinGlass.ReducedTopology

end

end OAI
