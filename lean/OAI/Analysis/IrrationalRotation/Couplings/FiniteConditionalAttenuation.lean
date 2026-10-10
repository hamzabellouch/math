import OAI.Analysis.IrrationalRotation.Couplings.ConditionalCrossingAvoidance

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace Invariant233.CrossingAvoidance

variable {ι Ω : Type*}

theorem measurable_card_filter [MeasurableSpace Ω] (s : Finset ι)
    (p : Ω → ι → Prop)
    (hp : ∀ i ∈ s, MeasurableSet {ω | p ω i}) :
    Measurable (fun ω => (s.filter (fun i => p ω i)).card) := by
  classical
  have hsum : Measurable (fun ω => ∑ i ∈ s, if p ω i then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hp i hi) measurable_const measurable_const
  simpa only [Finset.sum_boole, Nat.cast_id] using hsum

theorem majority_split_for_ordered_pair (s : Finset ι) (x y u : ι → ℝ)
    (horder : ∀ i ∈ s, x i ≤ y i)
    (hno : ∀ i ∈ s, ¬ (x i < u i ∧ u i ≤ y i)) :
    (¬ s.card ≤ 2 * (s.filter (fun i => x i < u i)).card) ↔
      s.card < 2 * (s.filter (fun i => u i ≤ y i)).card := by
  have hsum := below_card_add_above_card s x y u horder hno
  omega

theorem finite_conditional_attenuation [Countable ι]
    (mx my : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (hmx : mx ≤ mΩ) (hmy : my ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (I : Finset ι) (u : ι → ℝ) (x y : Ω → ι → ℝ)
    (hx : Measurable[mx] x) (hy : Measurable[my] y)
    (top bottom : ι → Set Ω)
    (htop : ∀ i, MeasurableSet (top i)) (hbottom : ∀ i, MeasurableSet (bottom i))
    (hindTop : iCondIndepSet mx hmx top μ) (hindBottom : iCondIndepSet my hmy bottom μ)
    (m ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ m * ρ)
    (hI : m / 20 ≤ (I.card : ℝ))
    (horder : ∀ᵐ ω ∂μ, ∀ i ∈ I, x ω i ≤ y ω i)
    (hforceTop : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      x ω i < u i → ω ∈ top i → u i ≤ y ω i)
    (hforceBottom : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      u i ≤ y ω i → ω ∈ bottom i → x ω i < u i)
    (hprobTop : ∀ᵐ ω ∂μ, ∀ i ∈ I, x ω i < u i →
      ρ / 10 ≤ (μ[(top i).indicator (fun _ => (1 : ℝ)) | mx]) ω)
    (hprobBottom : ∀ᵐ ω ∂μ, ∀ i ∈ I, u i ≤ y ω i →
      ρ / 10 ≤ (μ[(bottom i).indicator (fun _ => (1 : ℝ)) | my]) ω)
    (R : Ω → ℝ) (hR : ∀ᵐ ω ∂μ, R ω ≤ 1)
    (hcross : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      (x ω i < u i ∧ u i ≤ y ω i) → R ω ≤ Real.exp (-L)) :
    ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂μ, R ω ≤ Real.exp (-L) + H₁.indicator (fun _ => (1 : ℝ)) ω +
        H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  classical
  let B : Set Ω := {ω | ∀ i ∈ I, ¬ (x ω i < u i ∧ u i ≤ y ω i)}
  let low : (ι → ℝ) → Finset ι := fun a => I.filter (fun i => a i < u i)
  let high : (ι → ℝ) → Finset ι := fun a => I.filter (fun i => u i ≤ a i)
  let activeLow : (ι → ℝ) → Prop := fun a => I.card ≤ 2 * (low a).card
  let activeHigh : (ι → ℝ) → Prop := fun a => I.card ≤ 2 * (high a).card
  let H₁ : Set Ω := B ∩ {ω | activeLow (x ω)}
  let H₂ : Set Ω := B \ {ω | activeLow (x ω)}
  have hxi (i : ι) : Measurable (fun ω => x ω i) :=
    (measurable_pi_apply i).comp (hx.mono hmx le_rfl)
  have hyi (i : ι) : Measurable (fun ω => y ω i) :=
    (measurable_pi_apply i).comp (hy.mono hmy le_rfl)
  have hB : MeasurableSet B := by
    have hh : MeasurableSet (⋂ i ∈ I, {ω | ¬ (x ω i < u i ∧ u i ≤ y ω i)}) :=
      MeasurableSet.biInter I.countable_toSet (fun i _ =>
        ((measurableSet_lt (hxi i) measurable_const).inter
          (measurableSet_le measurable_const (hyi i))).compl)
    simpa only [B, Set.ofPred_forall] using hh
  have hcount : Measurable (fun ω => (low (x ω)).card) := by
    apply measurable_card_filter I (fun ω i => x ω i < u i)
    intro i _
    exact measurableSet_lt (hxi i) measurable_const
  have hactive : MeasurableSet {ω | activeLow (x ω)} :=
    measurableSet_le measurable_const (measurable_const.mul hcount)
  have hH₁ : MeasurableSet H₁ := hB.inter hactive
  have hH₂ : MeasurableSet H₂ := hB.diff hactive
  have hbound₁ : ∀ᵐ ω ∂μ,
      (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-L / 400) := by
    apply conditional_bad_le_exp_of_endpoint mx hmx μ top htop hindTop x hx
      low activeLow m ρ L hρ hL
    · intro a ha
      exact eligible_card_lower_bound I (low a) m hI ha
    · filter_upwards [hprobTop] with ω hω
      intro _ i hi
      have hi' := Finset.mem_filter.mp hi
      exact hω i hi'.1 hi'.2
    · exact hH₁
    · filter_upwards [hforceTop] with ω hω
      intro hmem
      refine ⟨hmem.2, ?_⟩
      intro i hi hlabel
      have hi' := Finset.mem_filter.mp hi
      exact hmem.1 i hi'.1 ⟨hi'.2, hω i hi'.1 hi'.2 hlabel⟩
  have hbound₂ : ∀ᵐ ω ∂μ,
      (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-L / 400) := by
    apply conditional_bad_le_exp_of_endpoint my hmy μ bottom hbottom hindBottom y hy
      high activeHigh m ρ L hρ hL
    · intro a ha
      exact eligible_card_lower_bound I (high a) m hI ha
    · filter_upwards [hprobBottom] with ω hω
      intro _ i hi
      have hi' := Finset.mem_filter.mp hi
      exact hω i hi'.1 hi'.2
    · exact hH₂
    · filter_upwards [horder, hforceBottom] with ω horder hω
      intro hmem
      have hhalf : activeHigh (y ω) :=
        above_half_of_below_not_half I (x ω) (y ω) u horder hmem.1 hmem.2
      refine ⟨hhalf, ?_⟩
      intro i hi hlabel
      have hi' := Finset.mem_filter.mp hi
      exact hmem.1 i hi'.1 ⟨hω i hi'.1 hi'.2 hlabel, hi'.2⟩
  refine ⟨H₁, H₂, hH₁, hH₂, hbound₁, hbound₂, ?_⟩
  filter_upwards [hR, hcross] with ω hR hcross
  by_cases hb : ω ∈ B
  · by_cases ha : activeLow (x ω)
    · have h1 : ω ∈ H₁ := ⟨hb, ha⟩
      have h2 : ω ∉ H₂ := fun h => h.2 ha
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
      linarith [Real.exp_pos (-L)]
    · have h1 : ω ∉ H₁ := fun h => ha h.2
      have h2 : ω ∈ H₂ := ⟨hb, ha⟩
      rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2]
      linarith [Real.exp_pos (-L)]
  · have hb' : ¬ ∀ i ∈ I, ¬ (x ω i < u i ∧ u i ≤ y ω i) := hb
    push Not at hb'
    obtain ⟨i, hi, hci⟩ := hb'
    have h1 : ω ∉ H₁ := fun h => hb h.1
    have h2 : ω ∉ H₂ := fun h => hb h.1
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    simpa using hcross i hi hci

theorem empty_exceptional_events (mx my : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} (μ : Measure Ω) (E : Set Ω) (R : Ω → ℝ)
    (η δ : ℝ) (hδ : 0 ≤ δ)
    (hR : ∀ᵐ ω ∂μ, ω ∈ E → R ω ≤ η) :
    ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ δ) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ δ) ∧
      (∀ᵐ ω ∂μ, ω ∈ E → R ω ≤ η + H₁.indicator (fun _ => (1 : ℝ)) ω +
        H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  refine ⟨∅, ∅, MeasurableSet.empty, MeasurableSet.empty, ?_, ?_, ?_⟩
  · simp only [Set.indicator_empty, condExp_fun_zero]
    exact Filter.Eventually.of_forall (fun _ => hδ)
  · simp only [Set.indicator_empty, condExp_fun_zero]
    exact Filter.Eventually.of_forall (fun _ => hδ)
  · simpa only [Set.indicator_empty, Pi.zero_apply, add_zero] using hR

theorem simultaneous_exceptional_families {κ : Type*} [Countable κ]
    (mx my : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (E : Set Ω) (R : κ → Ω → ℝ) (η δ : κ → ℝ)
    (h : ∀ k, ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ δ k) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ δ k) ∧
      (∀ᵐ ω ∂μ, ω ∈ E → R k ω ≤ η k + H₁.indicator (fun _ => (1 : ℝ)) ω +
        H₂.indicator (fun _ => (1 : ℝ)) ω)) :
    ∃ H₁ H₂ : κ → Set Ω, (∀ k, MeasurableSet (H₁ k)) ∧ (∀ k, MeasurableSet (H₂ k)) ∧
      (∀ᵐ ω ∂μ, ∀ k,
        (μ[(H₁ k).indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ δ k ∧
        (μ[(H₂ k).indicator (fun _ => (1 : ℝ)) | my]) ω ≤ δ k ∧
        (ω ∈ E → R k ω ≤ η k + (H₁ k).indicator (fun _ => (1 : ℝ)) ω +
          (H₂ k).indicator (fun _ => (1 : ℝ)) ω)) := by
  classical
  choose H₁ H₂ hmeas₁ hmeas₂ hbound₁ hbound₂ hratio using h
  refine ⟨H₁, H₂, hmeas₁, hmeas₂, ae_all_iff.mpr ?_⟩
  intro k
  filter_upwards [hbound₁ k, hbound₂ k, hratio k] with ω h₁ h₂ hr
  exact ⟨h₁, h₂, hr⟩

end Invariant233.CrossingAvoidance

end OAI
