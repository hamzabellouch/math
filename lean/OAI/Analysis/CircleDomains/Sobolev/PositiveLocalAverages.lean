import OAI.Analysis.CircleDomains.Rigidity.BoundaryTrace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace OAI

/-! Positive local averaging preserves every topological boundary band.
The statement allows arbitrary probability kernels; no regularity or
exceptional boundary set is assumed for the kernel. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MeasurableSpace X]

/-- A probability average respects almost-everywhere interval bounds. -/
theorem integral_mem_Icc_of_ae
    (μ : Measure X) [IsProbabilityMeasure μ] (u : X → ℝ)
    (hu : Integrable u μ) {a b : ℝ} (hab : ∀ᵐ y ∂μ, u y ∈ Icc a b) :
    (∫y, u y ∂μ) ∈ Icc a b := by
  constructor
  · have h := integral_mono_ae (integrable_const a) hu (hab.mono fun _ h => h.1)
    simpa only [integral_const, probReal_univ, one_smul] using h
  · have h := integral_mono_ae hu (integrable_const b) (hab.mono fun _ h => h.2)
    simpa only [integral_const, probReal_univ, one_smul] using h

variable [TopologicalSpace X]

/-- All averaging samples eventually lie in each relative neighborhood of
this particular boundary point. This is an almost-everywhere support
condition, so it also applies after choosing Borel representatives. -/
def LocalAverageSupport (G : Set X) (μ : X → Measure X) (s : X) : Prop :=
  ∀V ∈ 𝓝 s, ∀ᶠ x in 𝓝[G] s, ∀ᵐ y ∂μ x, y ∈ G ∩ V

theorem local_average_eventual_bounds
    (G : Set X) (μ : X → Measure X) [∀x, IsProbabilityMeasure (μ x)]
    (u : X → ℝ) (hu : ∀x, Integrable u (μ x)) {s : X}
    (hs : LocalAverageSupport G μ s) {a b : ℝ}
    (hab : ∀ᶠ y in 𝓝[G] s, u y ∈ Icc a b) :
    ∀ᶠ x in 𝓝[G] s, (∫y, u y ∂μ x) ∈ Icc a b := by
  obtain ⟨V, hV, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hab
  filter_upwards [hs V hV] with x hx
  exact integral_mem_Icc_of_ae (μ x) u (hu x) (hx.mono fun y hy => hsub ⟨hy.2, hy.1⟩)

/-- The value of each existing limiting trace is retained by averaging. -/
theorem local_average_tendsto
    (G : Set X) (μ : X → Measure X) [∀x, IsProbabilityMeasure (μ x)]
    (u : X → ℝ) (hu : ∀x, Integrable u (μ x)) {s : X} {c : ℝ}
    (hs : LocalAverageSupport G μ s) (hc : Tendsto u (𝓝[G] s) (𝓝 c)) :
    Tendsto (fun x => ∫y, u y ∂μ x) (𝓝[G] s) (𝓝 c) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : ∀ᶠ y in 𝓝[G] s, u y ∈ Icc (c - ε / 2) (c + ε / 2) := by
    filter_upwards [(Metric.tendsto_nhds.mp hc) (ε / 2) (half_pos hε)] with y hy
    rw [Real.dist_eq] at hy
    have ha := abs_lt.mp hy
    constructor <;> linarith
  filter_upwards [local_average_eventual_bounds G μ u hu hs he] with x hx
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hx.1, hx.2]

/-- Positive averages with shrinking support can only contract the original
pointwise band. No almost-everywhere qualification on `s` is needed. -/
theorem local_average_band_inclusion
    (G : Set X) (μ : X → Measure X) [∀x, IsProbabilityMeasure (μ x)]
    (u : X → ℝ) (hu : ∀x, Integrable u (μ x))
    (hb : ∀x, u x ∈ Icc 0 1) {s : X} (hGs : s ∈ closure G)
    (hs : LocalAverageSupport G μ s) :
    liminf u (𝓝[G] s) ≤ liminf (fun x => ∫y, u y ∂μ x) (𝓝[G] s) ∧
    limsup (fun x => ∫y, u y ∂μ x) (𝓝[G] s) ≤ limsup u (𝓝[G] s) := by
  let : NeBot (𝓝[G] s) := mem_closure_iff_nhdsWithin_neBot.mp hGs
  let v : X → ℝ := fun x => ∫y, u y ∂μ x
  have hv (x : X) : v x ∈ Icc 0 1 :=
    integral_mem_Icc_of_ae (μ x) u (hu x) (Eventually.of_forall hb)
  have hul : IsBoundedUnder (· ≥ ·) (𝓝[G] s) u :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun x => (hb x).1)
  have huu : IsBoundedUnder (· ≤ ·) (𝓝[G] s) u :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun x => (hb x).2)
  have hvl : IsBoundedUnder (· ≥ ·) (𝓝[G] s) v :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun x => (hv x).1)
  have hvu : IsBoundedUnder (· ≤ ·) (𝓝[G] s) v :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun x => (hv x).2)
  constructor
  · apply (le_liminf_iff' hvu.isCoboundedUnder_ge hvl).2
    intro a ha
    have he : ∀ᶠ y in 𝓝[G] s, u y ∈ Icc a 1 := by
      filter_upwards [eventually_lt_of_lt_liminf ha hul] with y hy
      exact ⟨hy.le, (hb y).2⟩
    exact (local_average_eventual_bounds G μ u hu hs he).mono fun _ h => h.1
  · apply (limsup_le_iff' hvl.isCoboundedUnder_le hvu).2
    intro b hb'
    have he : ∀ᶠ y in 𝓝[G] s, u y ∈ Icc 0 b := by
      filter_upwards [eventually_lt_of_limsup_lt hb' huu] with y hy
      exact ⟨(hb y).1, hy.le⟩
    exact (local_average_eventual_bounds G μ u hu hs he).mono fun _ h => h.2

theorem local_average_band_bound
    (G : Set X) (μ : X → Measure X) [∀x, IsProbabilityMeasure (μ x)]
    (u : X → ℝ) (hu : ∀x, Integrable u (μ x))
    (hb : ∀x, u x ∈ Icc 0 1) {s : X} (hGs : s ∈ closure G)
    (hs : LocalAverageSupport G μ s) (a : ℝ≥0∞)
    (ha : ENNReal.ofReal (limsup u (𝓝[G] s) - liminf u (𝓝[G] s)) ≤ a) :
    ENNReal.ofReal (limsup (fun x => ∫y, u y ∂μ x) (𝓝[G] s) -
      liminf (fun x => ∫y, u y ∂μ x) (𝓝[G] s)) ≤ a := by
  obtain ⟨hl, hr⟩ := local_average_band_inclusion G μ u hu hb hGs hs
  exact (ENNReal.ofReal_le_ofReal (sub_le_sub hr hl)).trans ha

end CircleDomainRigidity

end

end OAI
