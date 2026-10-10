import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootLeafHopf
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Regular

namespace OAI

/-!
# Compact sets with continuous root-leaf data

The Lusin step in EKL (2006), Section 4.3, is applied to a countable
family of compactly supported tests determining locally finite real
measures. A finer Polish topology and inner regularity provide a compact
set in the original topology, outside any specified null set.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology Classical ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma continuousOn_of_finer_compact {Y Z : Type*}
    {t t' : TopologicalSpace Y} {tZ : TopologicalSpace Z} [@T2Space Y t]
    (hle : t' ≤ t) {K : Set Y} (hK : @IsCompact Y t' K)
    {f : Y → Z} (hf : @Continuous Y Z t' tZ f) :
    @ContinuousOn Y Z t tZ f K := by
  let : TopologicalSpace Y := t
  apply continuousOn_iff_isClosed.mpr
  intro C hC
  have hc : @IsCompact Y t' (f ⁻¹' C ∩ K) := by
    let : TopologicalSpace Y := t'
    exact hK.inter_left (hC.preimage hf)
  have hid : @Continuous Y Y t' t id := continuous_id_of_le hle
  have hcold : @IsCompact Y t (f ⁻¹' C ∩ K) := by
    simpa only [image_id] using @IsCompact.image Y Y t' t _ id hc hid
  exact ⟨f ⁻¹' C ∩ K, hcold.isClosed, by simp only [inter_assoc, inter_self]⟩

/-- A compact Lusin set avoiding a prescribed measurable null set. -/
theorem exists_compact_continuousOn_outside_null
    {Y Z : Type*} [tY : TopologicalSpace Y] [PolishSpace Y]
    [mY : MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (f : Y → Z) (hf : Measurable f)
    (N : Set Y) (hN : MeasurableSet N) (hNzero : μ N = 0)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ K : Set Y, IsCompact K ∧ K ⊆ Nᶜ ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  have hB : mY = @borel Y tY := BorelSpace.measurable_eq
  obtain ⟨t', hle, hf', hp⟩ := hf.exists_continuous
  have hBt : mY = @borel Y t' :=
    hB.trans (borel_eq_borel_of_le hp (inferInstance : @PolishSpace Y tY) hle).symm
  let : TopologicalSpace Y := t'
  let : PolishSpace Y := hp
  let : BorelSpace Y := ⟨hBt⟩
  obtain ⟨K, hKN, hK, hsmall⟩ := hN.compl.exists_isCompact_sdiff_lt
    (measure_ne_top μ Nᶜ) hε
  have hsmall' : μ Kᶜ < ε := by
    have heq : Nᶜ \ K = Kᶜ \ N := by ext x; simp only [Set.mem_sdiff, mem_compl_iff, and_comm]
    rwa [heq, measure_sdiff_null hNzero] at hsmall
  refine ⟨K, ?_, hKN, hsmall', continuousOn_of_finer_compact hle hK hf'⟩
  simpa only [image_id] using @IsCompact.image Y Y t' tY K id hK (continuous_id_of_le hle)

/-- The compact-set version only needs a metrizable source and inner
regularity; the source need not be equipped with a complete metric. -/
theorem exists_compact_continuousOn_metrizable
    {Y Z : Type*} [TopologicalSpace Y] [MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (μ : Measure Y) [IsFiniteMeasure μ] [Measure.InnerRegularCompactLTTop μ]
    (f : Y → Z) (hf : Measurable f)
    (N : Set Y) (hN : MeasurableSet N) (hNzero : μ N = 0)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ K : Set Y, IsCompact K ∧ K ⊆ Nᶜ ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  obtain ⟨δ, hδ, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε (Fin 2)
  have hsum : δ 0 + δ 1 < ε := by simpa only [tsum_fintype, Fin.sum_univ_two] using hδsum
  obtain ⟨C, hCN, hC, hCsmall⟩ := hN.compl.exists_isCompact_sdiff_lt
    (measure_ne_top μ Nᶜ) (hδ 0).ne'
  have hCsmall' : μ Cᶜ < δ 0 := by
    have heq : Nᶜ \ C = Cᶜ \ N := by ext x; simp only [Set.mem_sdiff, mem_compl_iff, and_comm]
    rwa [heq, measure_sdiff_null hNzero] at hCsmall
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let : MetricSpace C := TopologicalSpace.metrizableSpaceMetric C
  let : PolishSpace C := inferInstance
  let ν : Measure C := μ.comap Subtype.val
  have he : MeasurableEmbedding (Subtype.val : C → Y) :=
    (hC.isClosed.isClosedEmbedding_subtypeVal).measurableEmbedding
  let : IsFiniteMeasure ν := ⟨by
    change μ.comap Subtype.val univ < ∞
    rw [he.comap_apply]
    exact measure_lt_top μ _⟩
  obtain ⟨L, hL, _, hLsmall, hLcont⟩ := exists_compact_continuousOn_outside_null
    ν (f ∘ Subtype.val) (hf.comp measurable_subtype_coe) ∅ MeasurableSet.empty
    (by simp) (δ 1) (hδ 1).ne'
  let K : Set Y := Subtype.val '' L
  have hK : IsCompact K := hL.image continuous_subtype_val
  have hKsmall : μ (C \ K) < δ 1 := by
    have heq : Subtype.val '' Lᶜ = C \ K := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.property, fun ⟨z, hz, hez⟩ => hy (Subtype.ext hez ▸ hz)⟩
      · rintro ⟨hxC, hxK⟩
        exact ⟨⟨x, hxC⟩, fun h => hxK ⟨⟨x, hxC⟩, h, rfl⟩, rfl⟩
    change μ.comap Subtype.val Lᶜ < δ 1 at hLsmall
    rw [he.comap_apply, heq] at hLsmall
    exact hLsmall
  refine ⟨K, hK, ?_, ?_, ?_⟩
  · rintro x ⟨y, _, rfl⟩
    exact hCN y.property
  · have hsub : Kᶜ ⊆ Cᶜ ∪ (C \ K) := by intro x hx; by_cases h : x ∈ C <;> tauto
    exact (((measure_mono hsub).trans (measure_union_le _ _)).trans
      (add_le_add hCsmall'.le hKsmall.le)).trans_lt hsum
  · exact Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_image_iff.mpr hLcont

def intrinsicLeafData {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (x : X n) : (ℕ × ℕ) → ℝ := fun q =>
  ∫ t, leafTest q.1 q.2 t ∂intrinsicRootKernel hij μ hfree x

lemma measurable_intrinsicLeafData {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    Measurable (intrinsicLeafData hij μ hfree) := by
  apply Measurable.of_eval
  intro q
  exact (leafTest q.1 q.2).continuous.stronglyMeasurable.integral_kernel.measurable

lemma intrinsicLeafData_eq_iff {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (x y : X n) :
    intrinsicLeafData hij μ hfree x = intrinsicLeafData hij μ hfree y ↔
      intrinsicRootKernel hij μ hfree x = intrinsicRootKernel hij μ hfree y := by
  constructor
  · intro h
    apply (realMeasures_eq_iff_leafTests _ _).mpr
    intro a b
    exact congrFun h (a, b)
  · intro h
    funext q
    exact congrArg (fun ν : Measure ℝ => ∫ t, leafTest q.1 q.2 t ∂ν) h

theorem exists_compact_continuous_rootLeafData
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (N : Set (X n)) (hN : MeasurableSet N) (hNzero : μ N = 0)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ K : Set (X n), IsCompact K ∧ K ⊆ Nᶜ ∧ μ Kᶜ < ε ∧
      ContinuousOn (intrinsicLeafData hij μ hfree) K ∧
      ∀ x ∈ K, intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x := by
  obtain ⟨E, hbad, hE, hEzero⟩ := exists_measurable_superset_of_null
    (ae_iff.mp (ae_intrinsicRootKernel_eq hij μ hfree))
  obtain ⟨K, hK, hKN, hsmall, hcont⟩ := exists_compact_continuousOn_metrizable
    μ (intrinsicLeafData hij μ hfree) (measurable_intrinsicLeafData hij μ hfree)
    (N ∪ E) (hN.union hE) (measure_union_null hNzero hEzero) ε hε
  refine ⟨K, hK, fun x hx => fun h => hKN hx (Or.inl h), hsmall, hcont, ?_⟩
  intro x hx
  by_contra h
  exact hKN hx (Or.inr (hbad h))

end DukePrimeDegree

end

end OAI
