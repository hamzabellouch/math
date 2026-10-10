import OAI.Analysis.KadisonKastler.ScalarBoundaryMean
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace OAI

/-! # Locality and countable gluing for the scalar boundary mean

Indicator sections turn the module identity into equality on a measurable
cell. Countable cells can then be glued without interchanging any infinite
sum with the mean.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {D : Type*} [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]

/-- The scalar characteristic function of a measurable set. -/
def scalarInfinityIndicator (s : Set D) (hs : MeasurableSet s) : ScalarLInfinity μ :=
  indicatorConstLp ⊤ hs (measure_ne_top μ s) (1 : ℂ)

theorem scalarInfinityIndicator_ae (s : Set D) (hs : MeasurableSet s) :
    scalarInfinityIndicator (μ := μ) s hs =ᵐ[μ] s.indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

/-- Multiplication by an indicator detects exactly equality on its cell. -/
theorem scalarInfinity_indicator_mul_eq_iff (s : Set D) (hs : MeasurableSet s)
    (f g : ScalarLInfinity μ) :
    scalarInfinityMul (scalarInfinityIndicator s hs) f =
        scalarInfinityMul (scalarInfinityIndicator s hs) g ↔
      f =ᵐ[μ.restrict s] g := by
  constructor
  · intro h
    apply (ae_restrict_iff' hs).mpr
    filter_upwards [scalarInfinityMul_ae (scalarInfinityIndicator s hs) f,
      scalarInfinityMul_ae (scalarInfinityIndicator s hs) g,
      scalarInfinityIndicator_ae (μ := μ) s hs] with x hf hg hi
    intro hx
    have he := congrArg (fun b : ScalarLInfinity μ => b x) h
    rw [hf, hg, hi, Set.indicator_of_mem hx, one_mul, one_mul] at he
    exact he
  · intro h
    apply Lp.ext
    have hfg := (ae_restrict_iff' hs).mp h
    filter_upwards [scalarInfinityMul_ae (scalarInfinityIndicator s hs) f,
      scalarInfinityMul_ae (scalarInfinityIndicator s hs) g,
      scalarInfinityIndicator_ae (μ := μ) s hs, hfg] with x hf hg hi he
    rw [hf, hg, hi]
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, one_mul, one_mul, he hx]
    · rw [Set.indicator_of_notMem hx, zero_mul, zero_mul]

section CountableGlue

variable {ι : Type*} [Countable ι]

omit [IsFiniteMeasure μ] in
/-- A scalar field selected from countably many L-infinity sections is
measurable when every selection fiber is measurable. -/
theorem aestronglyMeasurable_scalarInfinity_glue (a : D → ι)
    (ha : ∀ i, MeasurableSet {x | a x = i}) (f : ι → ScalarLInfinity μ) :
    AEStronglyMeasurable (fun x => f (a x) x) μ := by
  have hcover : (⋃ i, {x | a x = i}) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨a x, rfl⟩
  have hm : ∀ i, AEStronglyMeasurable (fun x => f (a x) x)
      (μ.restrict {x | a x = i}) := by
    intro i
    apply ((Lp.aestronglyMeasurable (f i)).mono_measure Measure.restrict_le_self).congr
    filter_upwards [ae_restrict_mem (ha i)] with x hx
    change a x = i at hx
    rw [hx]
  have h := AEStronglyMeasurable.iUnion hm
  simpa only [hcover, Measure.restrict_univ] using h

omit [IsFiniteMeasure μ] in
theorem scalarInfinity_glue_ae_bound (a : D → ι) (f : ι → ScalarLInfinity μ)
    {C : ℝ} (hC : ∀ i, ‖f i‖ ≤ C) :
    ∀ᵐ x ∂μ, ‖f (a x) x‖ ≤ C := by
  have h : ∀ᵐ x ∂μ, ∀ i, ‖f i x‖ ≤ C :=
    ae_all_iff.mpr fun i => (scalarInfinity_ae_norm_le (f i)).mono fun _ hx =>
      hx.trans (hC i)
  exact h.mono fun x hx => hx (a x)

/-- An actual L-infinity section obtained by bounded countable gluing. -/
def scalarInfinityGlue (a : D → ι) (ha : ∀ i, MeasurableSet {x | a x = i})
    (f : ι → ScalarLInfinity μ) (C : ℝ) (hC : ∀ i, ‖f i‖ ≤ C) : ScalarLInfinity μ :=
  (memLp_top_of_bound (aestronglyMeasurable_scalarInfinity_glue a ha f) C
    (scalarInfinity_glue_ae_bound a f hC)).toLp (fun x => f (a x) x)

omit [IsFiniteMeasure μ] in
theorem scalarInfinityGlue_ae (a : D → ι) (ha : ∀ i, MeasurableSet {x | a x = i})
    (f : ι → ScalarLInfinity μ) (C : ℝ) (hC : ∀ i, ‖f i‖ ≤ C) :
    scalarInfinityGlue a ha f C hC =ᵐ[μ] fun x => f (a x) x := MemLp.coeFn_toLp _

omit [IsFiniteMeasure μ] in
theorem scalarInfinityGlue_restrict (a : D → ι)
    (ha : ∀ i, MeasurableSet {x | a x = i}) (f : ι → ScalarLInfinity μ)
    (C : ℝ) (hC : ∀ i, ‖f i‖ ≤ C) (i : ι) :
    scalarInfinityGlue a ha f C hC =ᵐ[μ.restrict {x | a x = i}] f i := by
  apply (ae_restrict_iff' (ha i)).mpr
  filter_upwards [scalarInfinityGlue_ae a ha f C hC] with x hx
  intro hi
  rw [hx, hi]

theorem norm_scalarInfinityGlue_le (a : D → ι)
    (ha : ∀ i, MeasurableSet {x | a x = i}) (f : ι → ScalarLInfinity μ)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ i, ‖f i‖ ≤ C) :
    ‖scalarInfinityGlue a ha f C hC‖ ≤ C := by
  have hb : ∀ᵐ x ∂μ, ‖scalarInfinityGlue a ha f C hC x‖ ≤ C := by
    filter_upwards [scalarInfinityGlue_ae a ha f C hC,
      scalarInfinity_glue_ae_bound a f hC] with x hx hb
    rwa [hx]
  simpa using Lp.norm_le_of_ae_bound hC0 hb

end CountableGlue

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  {α : NonsingularAction G D μ}

namespace ScalarBoundaryMean

variable (m : ScalarBoundaryMean α)

/-- The scalar mean is local on every measurable boundary cell. -/
theorem locality (s : Set D) (hs : MeasurableSet s)
    (F K : G →ᵇ ScalarLInfinity μ) (hFK : ∀ g, F g =ᵐ[μ.restrict s] K g) :
    m.toCLM F =ᵐ[μ.restrict s] m.toCLM K := by
  apply (scalarInfinity_indicator_mul_eq_iff s hs _ _).mp
  rw [← m.module_map, ← m.module_map]
  congr 1
  apply BoundedContinuousFunction.ext
  intro g
  exact (scalarInfinity_indicator_mul_eq_iff s hs _ _).mpr (hFK g)

/-- Equality of local models for the input transfers to every output cell. -/
theorem local_models {ι : Type*} (s : ι → Set D) (hs : ∀ i, MeasurableSet (s i))
    (F : G →ᵇ ScalarLInfinity μ) (K : ι → G →ᵇ ScalarLInfinity μ)
    (hFK : ∀ i g, F g =ᵐ[μ.restrict (s i)] K i g) :
    ∀ i, m.toCLM F =ᵐ[μ.restrict (s i)] m.toCLM (K i) :=
  fun i => m.locality (s i) (hs i) F (K i) (hFK i)

/-- A countable measurable cover determines the mean from its local models. -/
theorem eq_of_countable_local_models {ι : Type*} [Countable ι]
    (s : ι → Set D) (hs : ∀ i, MeasurableSet (s i))
    (hcover : ∀ᵐ x ∂μ, ∃ i, x ∈ s i)
    (F : G →ᵇ ScalarLInfinity μ) (K : ι → G →ᵇ ScalarLInfinity μ)
    (hFK : ∀ i g, F g =ᵐ[μ.restrict (s i)] K i g)
    (b : ScalarLInfinity μ) (hb : ∀ i, b =ᵐ[μ.restrict (s i)] m.toCLM (K i)) :
    m.toCLM F = b := by
  have hloc : ∀ᵐ x ∂μ, ∀ i, x ∈ s i → m.toCLM F x = b x :=
    ae_all_iff.mpr fun i => (ae_restrict_iff' (hs i)).mp
      ((m.locality (s i) (hs i) F (K i) (hFK i)).trans (hb i).symm)
  apply Lp.ext
  filter_upwards [hcover, hloc] with x hx he
  obtain ⟨i, hi⟩ := hx
  exact he i hi

/-- The mean commutes with selecting uniformly bounded local models on
the fibers of a countably valued measurable boundary function. -/
theorem map_countable_glue {ι : Type*} [Countable ι]
    (a : D → ι) (ha : ∀ i, MeasurableSet {x | a x = i})
    (F : G →ᵇ ScalarLInfinity μ) (K : ι → G →ᵇ ScalarLInfinity μ)
    (hFK : ∀ i g, F g =ᵐ[μ.restrict {x | a x = i}] K i g)
    (C : ℝ) (hC : ∀ i, ‖K i‖ ≤ C) :
    m.toCLM F = scalarInfinityGlue a ha (fun i => m.toCLM (K i)) C
      (fun i => (m.norm_le (K i)).trans (hC i)) := by
  apply m.eq_of_countable_local_models (fun i => {x | a x = i}) ha
    (Eventually.of_forall fun x => ⟨a x, rfl⟩) F K hFK
  intro i
  exact scalarInfinityGlue_restrict a ha _ C _ i

end ScalarBoundaryMean

end

end KadisonKastler

end OAI
