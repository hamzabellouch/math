import OAI.Probability.SLE.Geometry.FrontSuccessStopped
import OAI.Probability.SLE.Gauge.UniformPassageThreshold

namespace OAI

/-! The uniform quantifier step for actual front passages.  A compactness
argument need only produce an eventual positive success probability along
one strictly increasing subsequence of each vanishing-mesh sequence. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

/-- The diagonal obstruction to a uniform passage estimate persists along
all subsequences, so compactness need only control one of them. -/
theorem uniform_passage_threshold_of_subsequences
    {A : Type*} (p : A → ℝ → ℝ → ℝ≥0∞)
    (hmono : ∀ a v, Antitone (p a v))
    (hsequence : ∀ (a : ℕ → A) (v : ℕ → ℝ), (∀ n, 0 < v n) →
      Tendsto v atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c : ℝ, 0 < c ∧ ∃ q : ℝ≥0∞, 0 < q ∧
        ∀ᶠ n in atTop, q ≤ p (a (φ n)) (v (φ n)) c) :
    ∃ q c v₀ : ℝ, 0 < q ∧ 0 < c ∧ 0 < v₀ ∧
      ∀ a : A, ∀ v : ℝ, 0 < v → v < v₀ → ENNReal.ofReal q ≤ p a v c := by
  classical
  by_contra h
  push Not at h
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hfail (n : ℕ) : ∃ a : A, ∃ v : ℝ,
      0 < v ∧ v < ε n ∧ p a v (ε n) < ENNReal.ofReal (ε n) := by
    obtain ⟨a, v, hv, hvs, hp⟩ := h (ε n) (ε n) (ε n) (hε n) (hε n) (hε n)
    exact ⟨a, v, hv, hvs, hp⟩
  choose a v hv hvs hbad using hfail
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hvlim : Tendsto v atTop (𝓝 0) :=
    squeeze_zero (fun n => (hv n).le) (fun n => (hvs n).le) hεlim
  obtain ⟨φ, hφ, c, hc, q, hq, hlower⟩ := hsequence a v hv hvlim
  have hεsub : Tendsto (fun n => ε (φ n)) atTop (𝓝 0) := hεlim.comp hφ.tendsto_atTop
  have hsmall : ∀ᶠ n in atTop, ε (φ n) ≤ c :=
    (hεsub.eventually (gt_mem_nhds hc)).mono fun _ hn => hn.le
  have hupper : ∀ᶠ n in atTop, q ≤ ENNReal.ofReal (ε (φ n)) := by
    filter_upwards [hlower, hsmall] with n hn hs
    exact (hn.trans (hmono (a (φ n)) (v (φ n)) hs)).trans (hbad (φ n)).le
  have hlim : Tendsto (fun n => ENNReal.ofReal (ε (φ n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hεsub
  exact (not_le_of_gt hq) (ge_of_tendsto hlim hupper)

namespace FirstFrontPassage

/-- Before an attained first hit, a continuous coordinate that started
below the front remains strictly below it. -/
theorem lt_before_firstFrontTime
    (x : ℝ≥0 → ℝ) (q : ℝ) (τ : ℝ≥0)
    (hτ : firstFrontTime x q = (τ : WithTop ℝ≥0))
    (hc : ContinuousOn x (Icc 0 τ)) (hstart : x 0 < q)
    (t : ℝ≥0) (ht : t < τ) : x t < q := by
  by_contra hn
  obtain ⟨u, hu, hue⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ t from bot_le)
    (hc.mono (Icc_subset_Icc_right ht.le)) ⟨hstart.le, le_of_not_gt hn⟩
  have hh := hittingAfter_le_of_mem (u := fun s (_ : Unit) => x s - q)
    (ω := ()) hu.1 (show x u - q ∈ ({0} : Set ℝ) by simp only [hue, sub_self, mem_singleton_iff])
  change firstFrontTime x q ≤ (u : WithTop ℝ≥0) at hh
  rw [hτ, WithTop.coe_le_coe] at hh
  exact (not_le_of_gt ht) (hh.trans hu.2)

end FirstFrontPassage

namespace PassageSuccess
open FirstFrontPassage

/-- The open-envelope success event gives exactly the strict pre-front
containment used by the manuscript. The front point itself is specified
separately by its attained coordinate and terminal offset. -/
theorem frontSuccess_source_prefix
    {Ω : Type*} (η : ℕ → Ω → ℝ≥0 → ℂ) (p : ℕ → ℂ → ℝ)
    (σ : Ω → ℝ≥0) (V : ℕ → Set ℂ) (a : ℕ → ℂ) (ε : ℝ) (n : ℕ)
    (ω : Ω) (hω : ω ∈ FrontSuccess η p σ V a ε n)
    (hc : ContinuousOn (fun t => p n (η n ω t))
      (Icc 0 (frontTime (fun t => p n (η n ω t)) 1)))
    (hstart : p n (η n ω 0) < 1) :
    MapsTo (η n ω) (Ico 0 (frontTime (fun t => p n (η n ω t)) 1))
      (V n ∩ {z | p n z < 1}) ∧
    p n (η n ω (frontTime (fun t => p n (η n ω t)) 1)) = 1 ∧
    ‖η n ω (frontTime (fun t => p n (η n ω t)) 1) - a n‖ < ε / 4 := by
  obtain ⟨htime, hhit, _, hpath, hterminal⟩ := hω
  refine ⟨?_, hhit, hterminal⟩
  intro t ht
  exact ⟨hpath ⟨ht.1, ht.2.le⟩,
    lt_before_firstFrontTime _ 1 _ htime hc hstart t ht.2⟩

/-- Probability of the concrete full-prefix front success and its physical
sausage mass.  The index records an admissible physical configuration. -/
def frontPassageProbability
    {A Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (η : A → Ω → ℝ≥0 → ℂ) (p : A → ℂ → ℝ) (σ : A → Ω → ℝ≥0)
    (V : A → Set ℂ) (a : A → ℂ) (ε : A → ℝ) (κ : ℝ) (R : A → Set ℂ)
    (d : A) (v c : ℝ) : ℝ≥0∞ :=
  P {ω | ω ∈ FrontSuccess (fun _ => η d) (fun _ => p d) (σ d)
        (fun _ => V d) (fun _ => a d) (ε d) 0 ∧ ENNReal.ofReal c ≤
      segmentSausageCharge κ (η d ω) (σ d ω)
        (frontTime (fun t => p d (η d ω t)) 1) v (R d)}

/-- Increasing the required mass only decreases the concrete passage
probability; no probability or measurability assumption is needed here. -/
theorem frontPassageProbability_antitone
    {A Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (η : A → Ω → ℝ≥0 → ℂ) (p : A → ℂ → ℝ) (σ : A → Ω → ℝ≥0)
    (V : A → Set ℂ) (a : A → ℂ) (ε : A → ℝ) (κ : ℝ) (R : A → Set ℂ)
    (d : A) (v : ℝ) : Antitone (frontPassageProbability P η p σ V a ε κ R d v) := by
  intro c₁ c₂ hc
  apply measure_mono
  intro ω hω
  exact ⟨hω.1, (ENNReal.ofReal_le_ofReal hc).trans hω.2⟩

/-- A later retained starting point gives a subset of the full passage
success-and-mass event. This removes the auxiliary first-height stop from
the final one-step conclusion. -/
theorem frontPassageProbability_mono_start
    {A Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (η : A → Ω → ℝ≥0 → ℂ) (p : A → ℂ → ℝ) (σ₁ σ₂ : A → Ω → ℝ≥0)
    (V : A → Set ℂ) (a : A → ℂ) (ε : A → ℝ) (κ : ℝ) (R : A → Set ℂ)
    (d : A) (v c : ℝ) (hσ : ∀ ω, σ₁ d ω ≤ σ₂ d ω) :
    frontPassageProbability P η p σ₂ V a ε κ R d v c ≤
      frontPassageProbability P η p σ₁ V a ε κ R d v c := by
  apply measure_mono
  rintro ω ⟨hfront, hmass⟩
  obtain ⟨hfinite, hhit, hbefore, hpath, hterminal⟩ := hfront
  refine ⟨⟨hfinite, hhit, (hσ ω).trans_lt hbefore, hpath, hterminal⟩, ?_⟩
  exact hmass.trans (segmentSausageCharge_mono κ (η d ω) (hσ ω) le_rfl v Subset.rfl)

theorem frontPassageProbability_le_from_zero
    {A Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (η : A → Ω → ℝ≥0 → ℂ) (p : A → ℂ → ℝ) (σ : A → Ω → ℝ≥0)
    (V : A → Set ℂ) (a : A → ℂ) (ε : A → ℝ) (κ : ℝ) (R : A → Set ℂ)
    (d : A) (v c : ℝ) :
    frontPassageProbability P η p σ V a ε κ R d v c ≤
      frontPassageProbability P η p (fun _ _ => 0) V a ε κ R d v c :=
  frontPassageProbability_mono_start P η p (fun _ _ => 0) σ V a ε κ R d v c (fun _ => bot_le)

/-- Once actual conformal compactness and the sequence passage theorem
supply the subsequential estimate, the full uniform passage constants
follow for the original concrete success-and-mass event. -/
theorem uniform_frontPassage_probability_of_subsequences
    {A Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (η : A → Ω → ℝ≥0 → ℂ) (p : A → ℂ → ℝ) (σ : A → Ω → ℝ≥0)
    (V : A → Set ℂ) (a : A → ℂ) (ε : A → ℝ) (κ : ℝ) (R : A → Set ℂ)
    (hsequence : ∀ (d : ℕ → A) (v : ℕ → ℝ), (∀ n, 0 < v n) →
      Tendsto v atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c q : ℝ, 0 < c ∧ 0 < q ∧
        ∀ᶠ n in atTop, ENNReal.ofReal q ≤
          frontPassageProbability P η p σ V a ε κ R (d (φ n)) (v (φ n)) c) :
    ∃ q c v₀ : ℝ, 0 < q ∧ 0 < c ∧ 0 < v₀ ∧
      ∀ d : A, ∀ v : ℝ, 0 < v → v < v₀ → ENNReal.ofReal q ≤
        frontPassageProbability P η p σ V a ε κ R d v c := by
  apply uniform_passage_threshold_of_subsequences
    (frontPassageProbability P η p σ V a ε κ R)
    (frontPassageProbability_antitone P η p σ V a ε κ R)
  intro d v hv hlim
  obtain ⟨φ, hφ, c, q, hc, hq, hlower⟩ := hsequence d v hv hlim
  exact ⟨φ, hφ, c, hc, ENNReal.ofReal q, ENNReal.ofReal_pos.mpr hq, hlower⟩

end PassageSuccess
end SLEExactGauge

end

end OAI
