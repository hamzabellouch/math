import OAI.Probability.SLE.Gauge.RibbonMiddleMass
import OAI.Probability.SLE.Gauge.RandomPassageBounds

namespace OAI

/-! The dense experiment concatenates full passage-and-mass events only
on histories where every previous passage has succeeded. Their spatial
middle strips are then charged to one actual sausage. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates

lemma adapted_successes_lower_bound_on_previous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℕ mΩ) (init : Set Ω) (hinit : MeasurableSet[ℱ 0] init)
    (success : ℕ → Set Ω) (hmeas : ∀ n, MeasurableSet[ℱ (n + 1)] (success n))
    (q : ℝ≥0∞)
    (hstep : ∀ n (A : Set Ω), MeasurableSet[ℱ n] A →
      A ⊆ init ∩ ⋂ j ∈ Finset.range n, success j → q * P A ≤ P (A ∩ success n)) :
    ∀ N : ℕ, q ^ N * P init ≤ P (init ∩ ⋂ n ∈ Finset.range N, success n) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    let A := init ∩ ⋂ n ∈ Finset.range N, success n
    have hA : MeasurableSet[ℱ N] A := by
      apply ((ℱ.mono (Nat.zero_le N)) _ hinit).inter
      apply MeasurableSet.iInter
      intro n
      apply MeasurableSet.iInter
      intro hn
      exact (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hn))) _ (hmeas n)
    have he : (init ∩ ⋂ n ∈ Finset.range (N + 1), success n) = A ∩ success N := by
      ext ω
      simp only [A, mem_inter_iff, mem_iInter, Finset.mem_range]
      constructor
      · rintro ⟨hi, h⟩
        exact ⟨⟨hi, fun n hn => h n (Nat.lt_succ_of_lt hn)⟩, h N (Nat.lt_succ_self N)⟩
      · rintro ⟨⟨hi, h⟩, hN⟩
        refine ⟨hi, fun n hn => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
        · exact h n hn
        · exact hN
    rw [he, pow_succ]
    calc
      q ^ N * q * P init = q * (q ^ N * P init) := by ac_rfl
      _ ≤ q * P A := mul_le_mul' le_rfl ih
      _ ≤ P (A ∩ success N) := hstep N A hA Subset.rfl

lemma ribbon_probability_of_quadratic_completion
    {q D : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m N : ℕ), (N : ℝ) ≤ D * (m : ℝ) ^ 2 →
      Real.exp (-C * (m : ℝ) ^ 2) ≤ q ^ N := by
  have hlog : Real.log q ≤ 0 := Real.log_nonpos hq.le hq1
  refine ⟨1 - D * Real.log q, by nlinarith, ?_⟩
  intro m N hN
  calc
    _ ≤ Real.exp ((N : ℝ) * Real.log q) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonpos_right hN hlog
      nlinarith [sq_nonneg (m : ℝ)]
    _ = q ^ N := by rw [Real.exp_nat_mul, Real.exp_log hq]

/-- The genuine adapted successes force the desired whole-trace mass at
one prescribed mesh, using only retained disjoint middle strips. -/
theorem ribbon_experiment_mass_event_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (ℱ : Filtration ℕ mΩ) (init : Set Ω) (hinit : MeasurableSet[ℱ 0] init)
    (success : ℕ → Set Ω) (hmeas : ∀ n, MeasurableSet[ℱ (n + 1)] (success n))
    (q : ℝ≥0∞)
    (hstep : ∀ n (A : Set Ω), MeasurableSet[ℱ n] A →
      A ⊆ init ∩ ⋂ j ∈ Finset.range n, success j → q * μ A ≤ μ (A ∩ success n))
    (hpublished : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hiP : InjOn P closedRibbon)
    {ε : ℝ} (hε : ε ≤ 1) (I : Finset ℕ) (N : ℕ)
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (s t : ℕ → Ω → ℝ≥0) (v c ell : ℝ)
    (hell : 0 < ell) (m : ℕ) (hm : 0 < m) (hcard : I.card = m ^ 2) (D : Set ℂ)
    (hregions : ∀ i ∈ I, physicalMiddleRegion P closedRibbon i ε ⊆ D)
    (hmass : ∀ ω ∈ init ∩ ⋂ n ∈ Finset.range N, success n, ∀ i ∈ I,
      ENNReal.ofReal (c * (ell / (m : ℝ)) ^ dimension κ) ≤
        segmentSausageCharge κ (γ ω) (s i ω) (t i ω) v
          (physicalMiddleRegion P closedRibbon i ε)) :
    q ^ N * μ init ≤ μ {ω |
      ENNReal.ofReal (c * ell ^ dimension κ * (m : ℝ) ^ codimension κ) ≤
        wholeSausageCharge κ (γ ω) v D} := by
  refine (adapted_successes_lower_bound_on_previous μ ℱ init hinit success hmeas q hstep N).trans
    (measure_mono ?_)
  intro ω hω
  exact dense_ribbon_mass_from_steps hpublished P hP hiP hε I κ (γ ω)
    (fun i => s i ω) (fun i => t i ω) v c ell hell m hm hcard D hregions (hmass ω hω)

end SLEExactGauge

end

end OAI
