import OAI.Probability.SLE.Geometry.FiniteStopSorting
import OAI.Probability.SLE.Multipoint.MultipointDiscountClock
import OAI.Probability.SLE.Multipoint.MultipointSwitchPatterns
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

namespace OAI

/-! Bounded discount rates selected at finitely many stopping-time switches.
The rate may jump at the switches; its accumulated clock is adapted and
Lipschitz, and its derivative agrees with the rate almost everywhere. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators

namespace SLEExactGauge.Multipoint

/-- Sorting all raw switches leaves no original switch strictly between
successive entries, including when some entries coincide. -/
lemma sortedStopAt_no_intermediate {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (hl : ∀ σ ∈ l, ∀ ω, σ ω ≤ H) (σ : Ω → ℝ≥0) (hσ : σ ∈ l)
    (n : ℕ) (ω : Ω) (hn : sortedStopAt l H n ω < σ ω) :
    sortedStopAt l H (n+1) ω ≤ σ ω := by
  obtain ⟨k, _, hk⟩ := sortedStopAt_covers l H σ hσ ω
  have hnk : n+1 ≤ k := by
    by_contra h
    have hkn : k ≤ n := by omega
    have hc := sortedStopAt_monotone l H hl ω hkn
    change sortedStopAt l H k ω ≤ sortedStopAt l H n ω at hc
    rw [hk] at hc
    exact (not_le_of_gt hn) hc
  exact (sortedStopAt_monotone l H hl ω hnk).trans_eq hk

lemma sortedStopAt_reached_iff {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (hl : ∀ σ ∈ l, ∀ ω, σ ω ≤ H) (σ : Ω → ℝ≥0) (hσ : σ ∈ l)
    (n : ℕ) (ω : Ω) (t : ℝ≥0) (hnt : sortedStopAt l H n ω ≤ t)
    (ht : t < sortedStopAt l H (n+1) ω) :
    σ ω ≤ t ↔ σ ω ≤ sortedStopAt l H n ω := by
  constructor
  · intro hσt
    by_contra h
    have hnext := sortedStopAt_no_intermediate l H hl σ hσ n ω (lt_of_not_ge h)
    exact (not_le_of_gt ht) (hnext.trans hσt)
  · exact fun h => h.trans hnt

def stoppedBranchRate {Ω : Type*} (σ τ : Ω → ℝ≥0) (A : Set Ω)
    (g : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := by
  classical
  exact if ω ∈ A ∧ σ ω ≤ t ∧ t < τ ω then g t ω else 0

lemma stoppedBranchRate_measurable {Ω : Type*} [MeasurableSpace Ω]
    (σ τ : Ω → ℝ≥0) (hσ : Measurable σ) (hτ : Measurable τ)
    (A : Set Ω) (hA : MeasurableSet A) (g : ℝ≥0 → Ω → ℝ)
    (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (stoppedBranchRate σ τ A g)) := by
  have hstart : MeasurableSet {p : ℝ≥0 × Ω | σ p.2 ≤ p.1} :=
    measurableSet_le (hσ.comp measurable_snd) measurable_fst
  have hend : MeasurableSet {p : ℝ≥0 × Ω | p.1 < τ p.2} :=
    measurableSet_lt measurable_fst (hτ.comp measurable_snd)
  exact Measurable.ite ((hA.preimage measurable_snd).inter (hstart.inter hend))
    hg measurable_const

/-- A branch known at its starting stop gives a measurable stochastic
interval on every finite deterministic horizon. -/
lemma stoppedBranch_start_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0)))
    (A : Set Ω) (hA : MeasurableSet[hσ.measurableSpace] A) (T : ℝ≥0) :
    MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ T)]
      {p : Iic T × Ω | p.2 ∈ A ∧ σ p.2 ≤ p.1} := by
  let : MeasurableSpace Ω := ℱ T
  have hAT : MeasurableSet (A ∩ {ω | σ ω ≤ T}) := by
    simpa only [WithTop.coe_le_coe] using hA.2 T
  have hσT : Measurable (fun ω => min (σ ω) T) := by
    have hm := ((hσ.min_const T).measurable_of_le
      (fun ω => min_le_right (σ ω : WithTop ℝ≥0) T)).untopD 0
    simpa only [← WithTop.coe_min, WithTop.untopD_coe] using hm
  have he : {p : Iic T × Ω | p.2 ∈ A ∧ σ p.2 ≤ p.1} =
      {p : Iic T × Ω | p.2 ∈ A ∩ {ω | σ ω ≤ T}} ∩
        {p : Iic T × Ω | min (σ p.2) T ≤ p.1} := by
    ext p
    constructor
    · rintro ⟨hA, hs⟩
      exact ⟨⟨hA, hs.trans p.1.prop⟩, (min_le_left _ _).trans hs⟩
    · rintro ⟨⟨hA, hsT⟩, hs⟩
      change σ p.2 ≤ T at hsT
      change min (σ p.2) T ≤ (p.1 : ℝ≥0) at hs
      exact ⟨hA, by simpa only [min_eq_left hsT] using hs⟩
  rw [he]
  exact (hAT.preimage measurable_snd).inter
    (measurableSet_le (hσT.comp measurable_snd)
      (measurable_subtype_coe.comp measurable_fst))

lemma stoppedBranchRate_progressive {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (σ τ : Ω → ℝ≥0)
    (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω) (hA : MeasurableSet[hσ.measurableSpace] A)
    (g : ℝ≥0 → Ω → ℝ) (hg : IsProgressive ℱ g) :
    IsProgressive ℱ (stoppedBranchRate σ τ A g) := by
  intro T
  have hs := stoppedBranch_start_measurable ℱ σ hσ A hA T
  have ht := stoppedBranch_start_measurable ℱ τ hτ univ MeasurableSet.univ T
  have ht' : MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ T)]
      {p : Iic T × Ω | (p.1 : ℝ≥0) < τ p.2} := by
    convert ht.compl using 1
    ext p
    simp only [mem_compl_iff, mem_ofPred_eq, mem_univ, true_and, not_le]
  have he : {p : Iic T × Ω | p.2 ∈ A ∧ σ p.2 ≤ p.1 ∧ (p.1 : ℝ≥0) < τ p.2} =
      {p : Iic T × Ω | p.2 ∈ A ∧ σ p.2 ≤ p.1} ∩
        {p : Iic T × Ω | (p.1 : ℝ≥0) < τ p.2} := by
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, and_assoc]
  apply Measurable.ite _ (hg T) measurable_const
  rw [he]
  exact hs.inter ht'

lemma stoppedBranchRate_norm_le {Ω : Type*} (σ τ : Ω → ℝ≥0) (A : Set Ω)
    (g : ℝ≥0 → Ω → ℝ) (C : ℝ≥0) (hC : ∀ t ω, |g t ω| ≤ C) (t : ℝ≥0) (ω : Ω) :
    |stoppedBranchRate σ τ A g t ω| ≤ C := by
  unfold stoppedBranchRate
  split_ifs
  · exact hC t ω
  · simpa only [abs_zero] using C.coe_nonneg

lemma stoppedBranchRate_nonneg {Ω : Type*} (σ τ : Ω → ℝ≥0) (A : Set Ω)
    (g : ℝ≥0 → Ω → ℝ) (hg : ∀ t ω, 0 ≤ g t ω) (t : ℝ≥0) (ω : Ω) :
    0 ≤ stoppedBranchRate σ τ A g t ω := by
  unfold stoppedBranchRate
  split_ifs
  · exact hg t ω
  · exact le_rfl

/-- Local integrability of a bounded measurable rate, without continuity. -/
lemma bounded_rate_locallyIntegrable {Ω : Type*}
    (g : ℝ≥0 → Ω → ℝ) (hg : ∀ ω, Measurable (fun t => g t ω))
    (C : ℝ≥0) (hC : ∀ t ω, |g t ω| ≤ C) (ω : Ω) :
    LocallyIntegrable (fun u : ℝ => g u.toNNReal ω) volume := by
  have hc : LocallyIntegrable (fun _ : ℝ => (C : ℝ)) volume :=
    continuous_const.locallyIntegrable
  apply hc.mono ((hg ω).comp continuous_real_toNNReal.measurable).aestronglyMeasurable
  filter_upwards [] with u
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg C.coe_nonneg]
    using hC u.toNNReal ω

lemma discountClock_lipschitz_of_measurable {Ω : Type*}
    (g : ℝ≥0 → Ω → ℝ) (hg : ∀ ω, Measurable (fun t => g t ω))
    (C : ℝ≥0) (hC : ∀ t ω, |g t ω| ≤ C) (ω : Ω) :
    LipschitzWith C (fun t => discountClock g t ω) := by
  have hi (a b : ℝ) : IntervalIntegrable (fun u : ℝ => g u.toNNReal ω) volume a b :=
    ((bounded_rate_locallyIntegrable g hg C hC ω).integrableOn_isCompact
      isCompact_uIcc).intervalIntegrable
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq, ← Real.norm_eq_abs]
  unfold discountClock
  rw [intervalIntegral.integral_interval_sub_left (hi _ _) (hi _ _)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (t.toNNReal : ℝ)) (b := (s.toNNReal : ℝ)) (C := (C : ℝ))
    (f := fun u : ℝ => g u.toNNReal ω)
    (fun u _ => by simpa only [Real.norm_eq_abs] using hC u.toNNReal ω)
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  have ht := Real.lipschitzWith_toNNReal.dist_le_mul s t
  simpa only [NNReal.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] using ht

lemma discountClock_increment_of_measurable {Ω : Type*}
    (g : ℝ≥0 → Ω → ℝ) (hg : ∀ ω, Measurable (fun t => g t ω))
    (C : ℝ≥0) (hC : ∀ t ω, |g t ω| ≤ C) (s t : ℝ≥0) (ω : Ω) :
    discountClock g t ω - discountClock g s ω =
      ∫ u in (s : ℝ)..(t : ℝ), g u.toNNReal ω := by
  have hi (a b : ℝ) : IntervalIntegrable (fun u : ℝ => g u.toNNReal ω) volume a b :=
    ((bounded_rate_locallyIntegrable g hg C hC ω).integrableOn_isCompact
      isCompact_uIcc).intervalIntegrable
  simp only [discountClock, Real.toNNReal_coe]
  exact intervalIntegral.integral_interval_sub_left (hi _ _) (hi _ _)

lemma discountClock_ae_derivative {Ω : Type*}
    (g : ℝ≥0 → Ω → ℝ) (hg : ∀ ω, Measurable (fun t => g t ω))
    (C : ℝ≥0) (hC : ∀ t ω, |g t ω| ≤ C) (ω : Ω) :
    ∀ᵐ t : ℝ, 0 < t → HasDerivAt (fun u => discountClock g u ω) (g t.toNNReal ω) t := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral (bounded_rate_locallyIntegrable g hg C hC ω)]
    with t ht
  intro ht0
  apply (ht 0).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht0] with u hu
  simp only [discountClock, Real.coe_toNNReal u hu.le]

lemma discountClock_adapted_of_progressive {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (g : ℝ≥0 → Ω → ℝ) (hg : IsProgressive ℱ g) :
    Adapted ℱ (fun t : ℝ≥0 => discountClock g t) := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  have htime : Measurable (fun u : ℝ =>
      (⟨min u.toNNReal t, by change min u.toNNReal t ≤ t; exact min_le_right _ _⟩ : Iic t)) :=
    ((continuous_real_toNNReal.min continuous_const).measurable).subtype_mk
  have hgm : Measurable (fun p : ℝ × Ω => g (min p.1.toNNReal t) p.2) :=
    (hg t).comp ((htime.comp measurable_fst).prodMk measurable_snd)
  have hm := (cumulative_integral_measurable (fun u ω => g (min u.toNNReal t) ω) hgm).comp
    (measurable_const.prodMk measurable_id : Measurable (fun ω : Ω => (t, ω)))
  convert hm using 1
  funext ω
  simp only [discountClock, Real.toNNReal_coe, Function.comp_def]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le t.coe_nonneg] at hu
  have hut : u.toNNReal ≤ t := by
    simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hu.2
  change g u.toNNReal ω = g (min u.toNNReal t) ω
  rw [min_eq_left hut]

/-- The finite index may comprise a stage and its finite past-measurable
pattern. Empty or simultaneous stages contribute zero. -/
def finiteSwitchRate {Ω ι : Type*} (s : Finset ι) (σ τ : ι → Ω → ℝ≥0)
    (A : ι → Set Ω) (g : ι → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ s, stoppedBranchRate (σ i) (τ i) (A i) (g i) t ω

lemma finiteSwitchRate_measurable {Ω ι : Type*} [MeasurableSpace Ω]
    (s : Finset ι) (σ τ : ι → Ω → ℝ≥0)
    (hσ : ∀ i ∈ s, Measurable (σ i)) (hτ : ∀ i ∈ s, Measurable (τ i))
    (A : ι → Set Ω) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (g : ι → ℝ≥0 → Ω → ℝ) (hg : ∀ i ∈ s, Measurable (Function.uncurry (g i))) :
    Measurable (Function.uncurry (finiteSwitchRate s σ τ A g)) := by
  exact Finset.measurable_sum s (fun i hi =>
    stoppedBranchRate_measurable (σ i) (τ i) (hσ i hi) (hτ i hi) (A i) (hA i hi)
      (g i) (hg i hi))

lemma finiteSwitchRate_progressive {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (s : Finset ι) (σ τ : ι → Ω → ℝ≥0)
    (hσ : ∀ i ∈ s, IsStoppingTime ℱ (fun ω => (σ i ω : WithTop ℝ≥0)))
    (hτ : ∀ i ∈ s, IsStoppingTime ℱ (fun ω => (τ i ω : WithTop ℝ≥0)))
    (A : ι → Set Ω) (hA : ∀ (i) (hi : i ∈ s), MeasurableSet[(hσ i hi).measurableSpace] (A i))
    (g : ι → ℝ≥0 → Ω → ℝ) (hg : ∀ i ∈ s, IsProgressive ℱ (g i)) :
    IsProgressive ℱ (finiteSwitchRate s σ τ A g) := by
  intro T
  exact Finset.measurable_sum s (fun i hi =>
    stoppedBranchRate_progressive ℱ (σ i) (τ i) (hσ i hi) (hτ i hi)
      (A i) (hA i hi) (g i) (hg i hi) T)

lemma finiteSwitchRate_norm_le {Ω ι : Type*} (s : Finset ι) (σ τ : ι → Ω → ℝ≥0)
    (A : ι → Set Ω) (g : ι → ℝ≥0 → Ω → ℝ) (C : ι → ℝ≥0)
    (hC : ∀ i ∈ s, ∀ t ω, |g i t ω| ≤ C i) (t : ℝ≥0) (ω : Ω) :
    |finiteSwitchRate s σ τ A g t ω| ≤ (∑ i ∈ s, C i : ℝ≥0) := by
  unfold finiteSwitchRate
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simpa only [NNReal.coe_sum] using Finset.sum_le_sum (fun i hi =>
    stoppedBranchRate_norm_le (σ i) (τ i) (A i) (g i) (C i) (hC i hi) t ω)

lemma finiteSwitchRate_nonneg {Ω ι : Type*} (s : Finset ι) (σ τ : ι → Ω → ℝ≥0)
    (A : ι → Set Ω) (g : ι → ℝ≥0 → Ω → ℝ)
    (hg : ∀ i ∈ s, ∀ t ω, 0 ≤ g i t ω) (t : ℝ≥0) (ω : Ω) :
    0 ≤ finiteSwitchRate s σ τ A g t ω := by
  exact Finset.sum_nonneg (fun i hi =>
    stoppedBranchRate_nonneg (σ i) (τ i) (A i) (g i) (hg i hi) t ω)

/-- The state used by the smooth-field adapter. No differentiability of
rates at switching times is required. -/
theorem finiteSwitchClock_regular {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (s : Finset ι) (σ τ : ι → Ω → ℝ≥0)
    (hσ : ∀ i ∈ s, IsStoppingTime ℱ (fun ω => (σ i ω : WithTop ℝ≥0)))
    (hτ : ∀ i ∈ s, IsStoppingTime ℱ (fun ω => (τ i ω : WithTop ℝ≥0)))
    (A : ι → Set Ω) (hA : ∀ (i) (hi : i ∈ s), MeasurableSet[(hσ i hi).measurableSpace] (A i))
    (g : ι → ℝ≥0 → Ω → ℝ)
    (hgm : ∀ i ∈ s, Measurable (Function.uncurry (g i)))
    (hgp : ∀ i ∈ s, IsProgressive ℱ (g i))
    (C : ι → ℝ≥0) (hC : ∀ i ∈ s, ∀ t ω, |g i t ω| ≤ C i) :
    let R := finiteSwitchRate s σ τ A g
    Measurable (fun p : ℝ × Ω => discountClock R p.1 p.2) ∧
    Adapted ℱ (fun t : ℝ≥0 => discountClock R t) ∧
    (∀ ω, LipschitzWith (∑ i ∈ s, C i) (fun t => discountClock R t ω)) ∧
    (∀ ω, ∀ᵐ t : ℝ, 0 < t →
      HasDerivAt (fun u => discountClock R u ω) (R t.toNNReal ω) t) ∧
    ∀ ω, discountClock R 0 ω = 0 := by
  let R := finiteSwitchRate s σ τ A g
  have hAm (i : ι) (hi : i ∈ s) : MeasurableSet (A i) :=
    (hσ i hi).measurableSpace_le _ (hA i hi)
  have hRm : Measurable (Function.uncurry R) := finiteSwitchRate_measurable s σ τ
    (fun i hi => stopping_time_measurable_nnreal (hσ i hi))
    (fun i hi => stopping_time_measurable_nnreal (hτ i hi)) A hAm g hgm
  have hRt : ∀ ω, Measurable (fun t => R t ω) := fun ω =>
    hRm.comp (measurable_id.prodMk measurable_const)
  have hbound := finiteSwitchRate_norm_le s σ τ A g C hC
  exact ⟨discountClock_measurable R hRm,
    discountClock_adapted_of_progressive ℱ R
      (finiteSwitchRate_progressive ℱ s σ τ hσ hτ A hA g hgp),
    discountClock_lipschitz_of_measurable R hRt _ hbound,
    discountClock_ae_derivative R hRt _ hbound,
    discountClock_initial R⟩

end SLEExactGauge.Multipoint

end

end OAI
