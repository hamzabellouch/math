import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineProfileConcentration
import Mathlib.MeasureTheory.Measure.Prod
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportedGoodSetSelection

namespace OAI

/-! # Uniform concentration and independent suffix sampling -/

noncomputable section
namespace PolycyclicRecognition

open Filter MeasureTheory Set
open scoped Topology ENNReal

/-- If every deterministic choice has vanishing bad probability, the
bound is uniform over all permitted choices at each scale. -/
theorem eventually_uniform_lt_of_all_selections
    {A : ℕ → Type*} [∀ n, Nonempty (A n)] (p : ∀ n, A n → ℝ≥0∞)
    (hp : ∀ a : ∀ n, A n, Tendsto (fun n => p n (a n)) atTop (𝓝 0))
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ a, p n a < η := by
  classical
  let a : ∀ n, A n := fun n => if h : ∃ a, η ≤ p n a then h.choose else Classical.arbitrary _
  have ha := (hp a).eventually (gt_mem_nhds hη)
  filter_upwards [ha] with n hn b
  by_contra h
  have hex : ∃ b, η ≤ p n b := ⟨b, le_of_not_gt h⟩
  have hb : η ≤ p n (a n) := by
    dsimp only [a]
    rw [dite_eq_left hex]
    exact hex.choose_spec
  exact (not_le_of_gt hn) hb

/-- Averaging an independent suffix preserves a bound that holds for each
of its deterministic values. The suffix law may vary arbitrarily. -/
theorem product_bad_probability_le
    {A K : Type*} [MeasurableSpace A] [MeasurableSpace K]
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure K)
    (B : Set (A × K)) (hB : MeasurableSet B) (δ : ℝ≥0∞)
    (hδ : ∀ k, (μ : Measure A) ((fun a => (a, k)) ⁻¹' B) ≤ δ) :
    (μ : Measure A).prod (ν : Measure K) B ≤ δ := by
  rw [Measure.prod_apply_symm hB]
  calc
    (∫⁻ k, (μ : Measure A) ((fun a => (a, k)) ⁻¹' B) ∂(ν : Measure K)) ≤
        ∫⁻ _, δ ∂(ν : Measure K) := lintegral_mono hδ
    _ = δ := by simp

/-- The uniform deterministic concentration conclusion survives arbitrary
independent suffix distributions at each scale. -/
theorem independent_bad_probability_tendsto_zero
    {A K : ℕ → Type*} [∀ n, MeasurableSpace (A n)] [∀ n, MeasurableSpace (K n)]
    [∀ n, Nonempty (K n)]
    (μ : ∀ n, ProbabilityMeasure (A n)) (ν : ∀ n, ProbabilityMeasure (K n))
    (B : ∀ n, Set (A n × K n)) (hB : ∀ n, MeasurableSet (B n))
    (hp : ∀ k : ∀ n, K n,
      Tendsto (fun n => (μ n : Measure (A n)) ((fun a => (a, k n)) ⁻¹' B n))
        atTop (𝓝 0)) :
    Tendsto (fun n => (μ n : Measure (A n)).prod (ν n : Measure (K n)) (B n))
      atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact False.elim ((not_lt_of_ge bot_le) hc)
  · intro c hc
    obtain ⟨d, hd0, hdc⟩ := exists_between hc
    have hbound' := eventually_uniform_lt_of_all_selections
      (fun n k => (μ n : Measure (A n)) ((fun a => (a, k)) ⁻¹' B n)) hp hd0
    filter_upwards [hbound'] with n hn
    exact lt_of_le_of_lt (product_bad_probability_le (μ n) (ν n) (B n) (hB n) d
      (fun k => (hn k).le)) hdc

/-- A joint failure probability smaller than the selected event's mass
forces a starting sample inside that event with a good probe fiber. -/
theorem exists_probe_fiber_in_event
    {A K : Type*} [MeasurableSpace A] [MeasurableSpace K]
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure K)
    (E : Set A) (hE : MeasurableSet E) (B : Set (A × K)) (hB : MeasurableSet B)
    (η : ℝ≥0∞) (hsmall : (μ : Measure A).prod (ν : Measure K) B < η * (μ : Measure A) E) :
    ∃ a ∈ E, (ν : Measure K) (Prod.mk a ⁻¹' B) < η := by
  classical
  by_contra h
  push Not at h
  have hle : E.indicator (fun _ => η) ≤
      fun a => (ν : Measure K) (Prod.mk a ⁻¹' B) := by
    intro a
    by_cases ha : a ∈ E
    · simpa only [indicator_of_mem ha] using h a ha
    · simp only [indicator_of_notMem ha]
      exact bot_le
  have hi := lintegral_mono (μ := (μ : Measure A)) hle
  rw [lintegral_indicator_const hE, ← Measure.prod_apply hB] at hi
  exact (not_le_of_gt hsmall) hi

/-- Vanishing bad probabilities force every supported limiting profile
into the zero set of the continuous error observable. -/
theorem eq_zero_on_support_of_probability_tendsto_zero
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [HasOuterApproxClosed S]
    (μn : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (hμ : Tendsto μn atTop (𝓝 μ)) (err : S → ℝ) (he : Continuous err)
    (hne : ∀ f, 0 ≤ err f)
    (hprob : ∀ η : ℝ, 0 < η →
      Tendsto (fun n => (μn n : Measure S) {f | η ≤ err f}) atTop (𝓝 0))
    {f : S} (hf : f ∈ (μ : Measure S).support) : err f = 0 := by
  apply le_antisymm _ (hne f)
  by_contra h
  have hp : 0 < err f := lt_of_not_ge h
  let η := err f / 2
  have hη : 0 < η := half_pos hp
  have hU : IsOpen {g | η < err g} := isOpen_lt continuous_const he
  have hfU : f ∈ {g | η < err g} := half_lt_self hp
  obtain ⟨c, hc, hmass⟩ := eventual_positive_mass_of_supported_weak_limit hμ hf hU hfU
  have hlim : Tendsto (fun n => ((μn n : Measure S) {g | η ≤ err g}).toReal)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hprob η hη)
  obtain ⟨n, hn, hbad⟩ := (hmass.and (hlim.eventually (gt_mem_nhds hc))).exists
  have hle : ((μn n : Measure S) {g | η < err g}).toReal ≤
      ((μn n : Measure S) {g | η ≤ err g}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun g (hg : η < err g) => (show η ≤ err g from hg.le)))
  exact (not_lt_of_ge (hn.trans hle)) hbad

/-- Affine restrictions on every finite set have one compatible label and
offset on the entire domain. This also glues a compact exhaustion. -/
theorem affineProfileClass_of_finite_restrictions
    {V W L : Type*} [TopologicalSpace V] [TopologicalSpace W]
    [AddCommGroup W] [Finite L] (A : L → C(V, W)) (f : C(V, W)) (z₀ : V)
    (h : ∀ Z : Set V, Z.Finite → ∃ a b, ∀ z ∈ Z, f z = A a z + b) :
    f ∈ affineProfileClass A := by
  classical
  by_contra hn
  have hbad (a : L) : ∃ z, f z ≠ A a z + (f z₀ - A a z₀) := by
    by_contra ha
    push Not at ha
    exact hn ⟨a, f z₀ - A a z₀, ha⟩
  choose z hz using hbad
  let Z := insert z₀ (range z)
  obtain ⟨a, b, hab⟩ := h Z ((finite_range z).insert z₀)
  have hbase := hab z₀ (mem_insert _ _)
  have hoff : b = f z₀ - A a z₀ := by rw [hbase]; simp
  exact hz a ((hab (z a) (mem_insert_of_mem _ (mem_range_self a))).trans (by rw [hoff]))

end PolycyclicRecognition

end

end OAI
