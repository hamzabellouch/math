import OAI.NumberTheory.DukePrimeDegree.Entropy.SummablePartitionBoundaries

namespace OAI

/-! # Neighborhoods inside cut-itinerary atoms

Summable boundary avoidance and uniform contraction leave an entire
parameter neighborhood in the same infinite itinerary atom. The
contraction estimate is explicit, so it can be supplied by root dynamics.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree

lemma cut_agrees_of_abs_sub_le {u v r ε : ℝ}
    (hnear : |u-v| ≤ ε) (haway : ε < |v-r|) :
    (u < r ↔ v < r) := by
  have hn := abs_le.mp hnear
  by_cases hvr : v < r
  · rw [abs_of_neg (sub_neg.mpr hvr)] at haway
    have hur : u < r := by linarith
    exact iff_of_true hur hvr
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hvr))] at haway
    have hur : ¬ u < r := by linarith
    exact iff_of_false hur hvr

theorem eventually_cut_itinerary_eq
    {Y V : Type*} [TopologicalSpace Y] [TopologicalSpace V]
    {T : Y → Y} (hT : Continuous T) {f : Y → ℝ} (hf : Continuous f)
    {F : V → Y} {v₀ : V} (hF : ContinuousAt F v₀)
    (ε : ℕ → ℝ) (r : ℝ)
    (hboundary : ∀ n : ℕ, f (T^[n] (F v₀)) ≠ r)
    (havoid : ∀ᶠ n : ℕ in atTop, ε n < |f (T^[n] (F v₀))-r|)
    (U : Set V) (hU : U ∈ 𝓝 v₀)
    (hcontract : ∀ n : ℕ, ∀ v ∈ U,
      |f (T^[n] (F v))-f (T^[n] (F v₀))| ≤ ε n) :
    ∀ᶠ v in 𝓝 v₀, ∀ n : ℕ, f (T^[n] (F v)) < r ↔ f (T^[n] (F v₀)) < r := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp havoid
  have hfinite (n : Fin N) : ∀ᶠ v in 𝓝 v₀,
      f (T^[n.val] (F v)) < r ↔ f (T^[n.val] (F v₀)) < r := by
    have hc : ContinuousAt (fun v => f (T^[n.val] (F v))) v₀ :=
      (hf.comp (hT.iterate n.val)).continuousAt.comp hF
    rcases lt_or_gt_of_ne (hboundary n.val) with hlt | hgt
    · exact (hc.eventually (gt_mem_nhds hlt)).mono fun _ hv => iff_of_true hv hlt
    · exact (hc.eventually (lt_mem_nhds hgt)).mono fun _ hv =>
        iff_of_false (not_lt.mpr hv.le) (not_lt.mpr hgt.le)
  filter_upwards [Filter.eventually_all.mpr hfinite,hU] with v hv hvU
  intro n
  by_cases hn : n < N
  · exact hv ⟨n,hn⟩
  · exact cut_agrees_of_abs_sub_le (hcontract n v hvU) (hN n (le_of_not_gt hn))

theorem ae_avoid_cut_boundary_at_all_times
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    {T : Y → Y} (hT : MeasurePreserving T μ μ) {f : Y → ℝ} (r : ℝ)
    (hr : μ {x | f x=r}=0) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, f (T^[n] x) ≠ r := by
  apply ae_all_iff.mpr
  intro n
  rw [ae_iff]
  simp only [not_not]
  change μ ((T^[n]) ⁻¹' {x | f x=r})=0
  exact (hT.iterate n).preimage_null hr

/-- A cut can be chosen in every open interval so that its infinite
itinerary is locally constant along every uniformly contracting
continuous parameter family, at almost every base point. -/
theorem exists_cut_with_contracting_itinerary_neighborhoods
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hTc : Continuous T)
    {f : Y → ℝ} (hf : Continuous f)
    (ε : ℕ → ℝ) (hε : Summable ε) (hεpos : ∀ n, 0 ≤ ε n)
    {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Ioo a b, ∀ᵐ x ∂μ,
      ∀ {V : Type} [TopologicalSpace V] (F : V → Y) (v₀ : V),
        F v₀=x → ContinuousAt F v₀ →
        ∀ U ∈ 𝓝 v₀,
          (∀ n : ℕ, ∀ v ∈ U, |f (T^[n] (F v))-f (T^[n] x)| ≤ ε n) →
          ∀ᶠ v in 𝓝 v₀, ∀ n : ℕ, f (T^[n] (F v)) < r ↔ f (T^[n] x) < r := by
  obtain ⟨r,hr,hnull,havoid⟩ := exists_cut_with_summable_boundary_returns
    μ hT hf.measurable ε hε hεpos hab
  refine ⟨r,hr,?_⟩
  filter_upwards [havoid,ae_avoid_cut_boundary_at_all_times μ hT r hnull] with x hx hxb
  intro V _ F v₀ hbase hF U hU hcontract
  subst x
  exact eventually_cut_itinerary_eq hTc hf hF ε r hxb hx U hU hcontract

end DukePrimeDegree

end

end OAI
