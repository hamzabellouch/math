import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Prod

namespace OAI

/-! # Factoring a measure along Haar fibers

A measure finite on compact subsets of a compact section times a group,
and invariant under translations of the group coordinate, is a product.
The section measure is obtained by averaging over a set of positive finite
Haar measure, never by restricting to a single fiber.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal Pointwise

variable {G X : Type*} [MeasurableSpace G] [MeasurableSpace X]
  (M : Measure (X × G))

/-- The group measure cut out by a measurable subset of the compact section. -/
def haarFiberSlice (E : Set X) : Measure G :=
  (M.restrict (E ×ˢ univ)).map Prod.snd

theorem haarFiberSlice_apply {E : Set X} (_hE : MeasurableSet E)
    {B : Set G} (hB : MeasurableSet B) :
    haarFiberSlice M E B = M (E ×ˢ B) := by
  rw [haarFiberSlice, Measure.map_apply measurable_snd hB,
    Measure.restrict_apply (measurable_snd hB)]
  congr 1
  ext q
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
  exact and_comm

/-- Average the coupling over a fixed finite Haar region to define its
section measure. -/
def haarSectionMeasure (m : Measure G) (B : Set G) : Measure X :=
  (m B)⁻¹ • (M.restrict (univ ×ˢ B)).map Prod.fst

theorem haarSectionMeasure_apply (m : Measure G) {B : Set G} (_hB : MeasurableSet B)
    {E : Set X} (hE : MeasurableSet E) :
    haarSectionMeasure M m B E = M (E ×ˢ B) / m B := by
  rw [haarSectionMeasure, Measure.smul_apply, Measure.map_apply measurable_fst hE,
    Measure.restrict_apply (measurable_fst hE)]
  have hset : Prod.fst ⁻¹' E ∩ univ ×ˢ B = E ×ˢ B := by ext q; simp
  rw [hset, smul_eq_mul, mul_comm, div_eq_mul_inv]


variable [Group G] [MeasurableMul₂ G] [MeasurableInv G]

omit [MeasurableInv G] in
theorem haarFiberSlice_rightInvariant
    (hM : ∀ g : G, MeasurePreserving (fun q : X × G => (q.1, q.2 * g)) M M)
    {E : Set X} (hE : MeasurableSet E) :
    (haarFiberSlice M E).IsMulRightInvariant := by
  constructor
  intro g
  ext B hB
  rw [Measure.map_apply (measurable_mul_const g) hB,
    haarFiberSlice_apply M hE ((measurable_mul_const g) hB),
    haarFiberSlice_apply M hE hB]
  exact (hM g).measure_preimage (hE.prod hB).nullMeasurableSet

/-- Right-invariant uniqueness, deduced from left-invariant uniqueness by
inverting both measures. -/
theorem rightInvariant_eq_div_smul (μ m : Measure G)
    [SigmaFinite μ] [SigmaFinite m] [μ.IsMulRightInvariant] [m.IsMulRightInvariant]
    {B : Set G} (hB0 : m B ≠ 0) (hBtop : m B ≠ ∞) :
    μ = (μ B / m B) • m := by
  have h := MeasureTheory.measure_eq_div_smul μ.inv m.inv
    (s := B⁻¹) (by simpa using hB0) (by simpa using hBtop)
  have hi := congrArg (fun ρ : Measure G => ρ.inv) h
  simp only [Measure.inv_inv, Measure.inv_apply, inv_inv] at hi
  rw [Measure.inv, Measure.map_smul _ measurable_inv.aemeasurable] at hi
  change μ = (μ B / m B) • m.inv.inv at hi
  simpa only [Measure.inv_inv] using hi

/-- A measure-preserving skew translation over a map of the section forces
that section map to preserve the marginal Haar factor. -/
theorem measurePreserving_base_of_left_skew (ν : Measure X) (m : Measure G)
    [SFinite ν] [SFinite m] [m.IsMulLeftInvariant]
    {T : X → X} (hT : Measurable T) {a : X → G} (ha : Measurable a)
    (hskew : MeasurePreserving (fun q : X × G => (T q.1, a q.1 * q.2))
      (ν.prod m) (ν.prod m))
    {B : Set G} (hB : MeasurableSet B) (hB0 : m B ≠ 0) (hBtop : m B ≠ ∞) :
    MeasurePreserving T ν ν := by
  have hinv : MeasurePreserving (fun q : X × G => (q.1, (a q.1)⁻¹ * q.2))
      (ν.prod m) (ν.prod m) := by
    apply (MeasurePreserving.id ν).skew_product (g := fun x z => (a x)⁻¹ * z)
    · exact (ha.comp measurable_fst).inv.mul measurable_snd
    · exact Filter.Eventually.of_forall fun x => map_mul_left_eq_self m (a x)⁻¹
  have hbase : MeasurePreserving (fun q : X × G => (T q.1, q.2))
      (ν.prod m) (ν.prod m) := by
    simpa only [Function.comp_def, mul_inv_cancel_left] using hskew.comp hinv
  refine ⟨hT, ?_⟩
  ext E hE
  rw [Measure.map_apply hT hE]
  have he := hbase.measure_preimage (hE.prod hB).nullMeasurableSet
  change (ν.prod m) ((T ⁻¹' E) ×ˢ B) = (ν.prod m) (E ×ˢ B) at he
  simp only [Measure.prod_prod] at he
  exact (ENNReal.mul_left_inj hB0 hBtop).mp he

variable [TopologicalSpace G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G]
  [TopologicalSpace X] [CompactSpace X]
  [IsFiniteMeasureOnCompacts M]

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G]
  [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem haarFiberSlice_finiteOnCompacts {E : Set X} (hE : MeasurableSet E) :
    IsFiniteMeasureOnCompacts (haarFiberSlice M E) := ⟨by
    intro B hB
    rw [haarFiberSlice_apply M hE hB.measurableSet]
    exact (measure_mono (prod_mono (subset_univ E) Subset.rfl)).trans_lt
      (isCompact_univ.prod hB).measure_lt_top⟩

/-- Translation invariance forces all measurable rectangles to have the
product measure predicted by a single Haar normalization. -/
theorem haarProduct_rectangle (m : Measure G) [SigmaFinite m] [m.IsMulRightInvariant]
    (hM : ∀ g : G, MeasurePreserving (fun q : X × G => (q.1, q.2 * g)) M M)
    {B : Set G} (hB : MeasurableSet B) (hB0 : m B ≠ 0) (hBtop : m B ≠ ∞)
    {E : Set X} (hE : MeasurableSet E) {C : Set G} (hC : MeasurableSet C) :
    M (E ×ˢ C) = haarSectionMeasure M m B E * m C := by
  let := haarFiberSlice_rightInvariant M hM hE
  let := haarFiberSlice_finiteOnCompacts M hE
  have h := rightInvariant_eq_div_smul (haarFiberSlice M E) m hB0 hBtop
  have hc := congrArg (fun ρ : Measure G => ρ C) h
  simpa only [haarFiberSlice_apply M hE hC, Measure.smul_apply, smul_eq_mul,
    haarFiberSlice_apply M hE hB, haarSectionMeasure_apply M m hB hE] using hc

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G]
  [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- The section measure has finite mass if the averaging region is compact. -/
theorem haarSectionMeasure_finite (m : Measure G) {B : Set G}
    (hB : IsCompact B) (hB0 : m B ≠ 0) :
    IsFiniteMeasure (haarSectionMeasure M m B) := by
  constructor
  rw [haarSectionMeasure_apply M m hB.measurableSet MeasurableSet.univ]
  exact ENNReal.div_lt_top (isCompact_univ.prod hB).measure_ne_top hB0

/-- Haar uniqueness on each section slice yields equality on the whole
product sigma algebra. -/
theorem haarProduct_factorization (m : Measure G) [SigmaFinite m] [m.IsMulRightInvariant]
    (hM : ∀ g : G, MeasurePreserving (fun q : X × G => (q.1, q.2 * g)) M M)
    {B : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0) (hBtop : m B ≠ ∞) :
    M = (haarSectionMeasure M m B).prod m := by
  let := haarSectionMeasure_finite M m hB hB0
  symm
  apply Measure.prod_eq
  intro E C hE hC
  exact haarProduct_rectangle M m hM hB.measurableSet hB0 hBtop hE hC

/-- A nonzero invariant coupling has a finite nonzero section measure. -/
theorem haarSectionMeasure_ne_zero (m : Measure G) [SigmaFinite m] [m.IsMulRightInvariant]
    (hM : ∀ g : G, MeasurePreserving (fun q : X × G => (q.1, q.2 * g)) M M)
    (hM0 : M ≠ 0) {B : Set G} (hB : IsCompact B)
    (hB0 : m B ≠ 0) (hBtop : m B ≠ ∞) :
    haarSectionMeasure M m B ≠ 0 := by
  intro hν
  apply hM0
  rw [haarProduct_factorization M m hM hB hB0 hBtop, hν, Measure.zero_prod]

end PolycyclicRecognition

end

end OAI
