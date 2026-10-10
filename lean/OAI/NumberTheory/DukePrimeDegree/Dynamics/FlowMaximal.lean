import OAI.NumberTheory.DukePrimeDegree.Dynamics.FlowOccupation

namespace OAI

/-!
# Maximal occupation control for long flow intervals

The discrete Hopf inequality, applied to one-unit occupation, controls
every real interval of length at least one. This is sufficient for the
large logarithmic time windows in EKL (2006), Lemmas 4.5 and 4.6.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree

theorem exists_flow_average_good_set
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    {E : Set Y} (hE : MeasurableSet E) (c : ℝ) (hc : 0 < c) :
    ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal (2 * μ.real E / c) ∧
      ∀ x ∈ G, ∀ T : ℝ, 1 ≤ T →
        (∫ t in (0 : ℝ)..T, E.indicator (fun _ => (1 : ℝ)) (Φ t x)) ≤ c * T := by
  obtain ⟨G, hG, hmass, hgood⟩ := exists_discrete_average_good_set μ (hpres 1)
    (integrable_unitFlowOccupation μ hΦ hE) (measurable_unitFlowOccupation hΦ hE)
    (unitFlowOccupation_nonneg Φ E) (c / 2) (by linarith)
  refine ⟨G, hG, ?_, ?_⟩
  · rw [integral_unitFlowOccupation μ hΦ hpres hE] at hmass
    convert hmass using 2
    ring
  · intro x hx T hT
    let n := Nat.ceil T
    have hTn : T ≤ (n : ℝ) := Nat.le_ceil T
    have hn : (n : ℝ) ≤ 2 * T := by
      have hnlt : (n : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
      linarith
    have hmono := intervalIntegral.integral_mono_interval
      (f := fun t => E.indicator (fun _ => (1 : ℝ)) (Φ t x))
      (le_refl (0 : ℝ)) (by linarith : (0 : ℝ) ≤ T) hTn
      (Eventually.of_forall fun t => indicator_nonneg (fun _ _ => zero_le_one) (Φ t x))
      (intervalIntegrable_flow_indicator hΦ hE x 0 n)
    rw [← birkhoffSum_unitFlowOccupation hΦ hzero hadd hE n x] at hmono
    have hdiscrete := hgood x hx n
    have hfinal : c / 2 * (n : ℝ) ≤ c * T := by nlinarith
    exact hmono.trans (hdiscrete.trans hfinal)

lemma flow_occupation_eq_time_measure
    {Y : Type*} [MeasurableSpace Y] {Φ : ℝ → Y → Y}
    (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    {E : Set Y} (hE : MeasurableSet E) (x : Y) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, E.indicator (fun _ => (1 : ℝ)) (Φ t x)) =
      volume.real (Ioc 0 T ∩ {t | Φ t x ∈ E}) := by
  let S := {t | Φ t x ∈ E}
  have hS : MeasurableSet S := hE.preimage (hΦ.comp (measurable_const.prodMk measurable_id))
  have heq : (fun t => E.indicator (fun _ => (1 : ℝ)) (Φ t x)) =
      S.indicator (fun _ => (1 : ℝ)) := by
    funext t
    by_cases ht : Φ t x ∈ E <;> simp [S, ht]
  rw [intervalIntegral.integral_of_le hT, heq, integral_indicator_const (1 : ℝ) hS,
    measureReal_restrict_apply hS, inter_comm]
  simp only [smul_eq_mul, mul_one]
  rfl

/-- Every long interval has a uniformly small fraction of bad visits
outside one set with the explicit maximal-inequality bound. -/
theorem exists_flow_return_good_set
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    {E : Set Y} (hE : MeasurableSet E) (c : ℝ) (hc : 0 < c) :
    ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal (2 * μ.real E / c) ∧
      ∀ x ∈ G, ∀ T : ℝ, 1 ≤ T →
        volume.real (Ioc 0 T ∩ {t | Φ t x ∈ E}) ≤ c * T := by
  obtain ⟨G, hG, hmass, hgood⟩ :=
    exists_flow_average_good_set μ hΦ hzero hadd hpres hE c hc
  refine ⟨G, hG, hmass, ?_⟩
  intro x hx T hT
  rw [← flow_occupation_eq_time_measure hΦ hE x T (by linarith)]
  exact hgood x hx T hT

end DukePrimeDegree

end

end OAI
