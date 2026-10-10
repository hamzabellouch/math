import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceProfileSampling

namespace OAI

/-! # A diagonal of supported laws with subexponential retained mass

Each outer parameter has its own limiting law and supported profile. The
inner scale is chosen after the outer parameter, with arbitrary eventual
side conditions. This preserves positive mass at every selected scale.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology

theorem exists_diagonal_supported_neighborhoods
    {X A : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] [MeasurableSpace A]
    (scale : ℕ → ℕ → ℝ) (hs : ∀ j, Tendsto (scale j) atTop atTop)
    (samples : ℕ → ℕ → ProbabilityMeasure A) (profile : ℕ → ℕ → A → X)
    (hp : ∀ j n, Measurable (profile j n)) (ν : ℕ → ProbabilityMeasure X)
    (hν : ∀ j, Tendsto (fun n => ProbabilityMeasure.map (samples j n) (profile j n))
      atTop (𝓝 (ν j)))
    (f : ℕ → X) (hf : ∀ j, f j ∈ (ν j : Measure X).support)
    (U : ℕ → Set X) (hU : ∀ j, IsOpen (U j)) (hfU : ∀ j, f j ∈ U j)
    (P : ℕ → ℕ → Prop) (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ (n : ℕ → ℕ) (B : ℕ → Set A),
      (∀ j, P j (n j)) ∧ Tendsto (fun j => scale j (n j)) atTop atTop ∧
      (∀ j, MeasurableSet (B j)) ∧ (∀ j, 0 < ((samples j (n j) : Measure A) (B j)).toReal) ∧
      HasSubexponentialLowerBoundSeq (fun j => scale j (n j))
        (fun j => ((samples j (n j) : Measure A) (B j)).toReal) ∧
      ∀ j a, a ∈ B j → profile j (n j) a ∈ U j := by
  let e : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have he j : 0 < e j := by dsimp [e]; positivity
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose c hc hmass using fun j =>
    eventual_positive_mass_of_supported_weak_limit (hν j) (hf j) (hU j) (hfU j)
  have hchoose j : ∃ n, P j n ∧ (j : ℝ) + 1 ≤ scale j n ∧
      Real.exp (-e j * scale j n) ≤
        ((ProbabilityMeasure.map (samples j n) (profile j n) : Measure X) (U j)).toReal := by
    have hexp := ((subexponential_lower_const (hc j)).along_sequence (hs j)) (e j) (he j)
    obtain ⟨n, hn, hr, hm, he'⟩ := ((hP j).and
      (((hs j).eventually (eventually_ge_atTop ((j : ℝ) + 1))).and
        ((hmass j).and hexp))).exists
    exact ⟨n, hn, hr, he'.trans hm⟩
  choose n hn hr hm using hchoose
  let B : ℕ → Set A := fun j => profile j (n j) ⁻¹' U j
  have hmap j : ((ProbabilityMeasure.map (samples j (n j)) (profile j (n j)) : Measure X)
      (U j)).toReal = ((samples j (n j) : Measure A) (B j)).toReal := by
    rw [show (ProbabilityMeasure.map (samples j (n j)) (profile j (n j)) : Measure X) =
      Measure.map (profile j (n j)) (samples j (n j) : Measure A) from rfl,
      Measure.map_apply (hp j (n j)) (hU j).measurableSet]
  have hm' j : Real.exp (-e j * scale j (n j)) ≤
      ((samples j (n j) : Measure A) (B j)).toReal := by simpa only [hmap] using hm j
  have hr0 j : 0 ≤ scale j (n j) := le_trans (by positivity) (hr j)
  have hscale : Tendsto (fun j => scale j (n j)) atTop atTop :=
    tendsto_atTop_mono (fun j => (le_add_of_nonneg_right zero_le_one).trans (hr j))
      tendsto_natCast_atTop_atTop
  refine ⟨n, B, hn, hscale, fun j => (hp j (n j)) (hU j).measurableSet,
    fun j => (Real.exp_pos _).trans_le (hm' j), ?_, ?_⟩
  · intro δ hδ
    filter_upwards [helim.eventually (gt_mem_nhds hδ)] with j hj
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hj.le) (hr0 j))).trans
      (hm' j)
  · intro j a ha
    exact ha

theorem exists_diagonal_good_observations
    {X A E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] [MeasurableSpace A] [NormedAddCommGroup E]
    (scale : ℕ → ℕ → ℝ) (hs : ∀ j, Tendsto (scale j) atTop atTop)
    (samples : ℕ → ℕ → ProbabilityMeasure A) (profile : ℕ → ℕ → A → X)
    (hp : ∀ j n, Measurable (profile j n)) (ν : ℕ → ProbabilityMeasure X)
    (hν : ∀ j, Tendsto (fun n => ProbabilityMeasure.map (samples j n) (profile j n))
      atTop (𝓝 (ν j)))
    (f : ℕ → X) (g : X) (hf : ∀ j, f j ∈ (ν j : Measure X).support)
    (hfg : Tendsto f atTop (𝓝 g)) (observe : C(X, E))
    (P : ℕ → ℕ → Prop) (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ (n : ℕ → ℕ) (B : ℕ → Set A) (ε : ℕ → ℝ),
      (∀ j, P j (n j)) ∧ Tendsto (fun j => scale j (n j)) atTop atTop ∧
      (∀ j, MeasurableSet (B j)) ∧ (∀ j, 0 < ((samples j (n j) : Measure A) (B j)).toReal) ∧
      (∀ j, 0 < ε j) ∧ Tendsto ε atTop (𝓝 0) ∧
      HasSubexponentialLowerBoundSeq (fun j => scale j (n j))
        (fun j => ((samples j (n j) : Measure A) (B j)).toReal) ∧
      ∀ j a, a ∈ B j → ‖observe (profile j (n j) a) - observe g‖ < ε j := by
  let e : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have he j : 0 < e j := by dsimp [e]; positivity
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let U : ℕ → Set X := fun j => observe ⁻¹' Metric.ball (observe (f j)) (e j)
  have hU j : IsOpen (U j) := Metric.isOpen_ball.preimage observe.continuous
  have hfU j : f j ∈ U j := by
    change dist (observe (f j)) (observe (f j)) < e j
    simpa only [dist_self] using he j
  choose c hc hmass using fun j =>
    eventual_positive_mass_of_supported_weak_limit (hν j) (hf j) (hU j) (hfU j)
  have hchoose j : ∃ n, P j n ∧ (j : ℝ) + 1 ≤ scale j n ∧
      Real.exp (-e j * scale j n) ≤
        ((ProbabilityMeasure.map (samples j n) (profile j n) : Measure X) (U j)).toReal := by
    have hexp := ((subexponential_lower_const (hc j)).along_sequence (hs j)) (e j) (he j)
    obtain ⟨n, hn, hr, hm, he'⟩ := ((hP j).and
      (((hs j).eventually (eventually_ge_atTop ((j : ℝ) + 1))).and
        ((hmass j).and hexp))).exists
    exact ⟨n, hn, hr, he'.trans hm⟩
  choose n hn hr hm using hchoose
  let B : ℕ → Set A := fun j => profile j (n j) ⁻¹' U j
  have hmap j : ((ProbabilityMeasure.map (samples j (n j)) (profile j (n j)) : Measure X)
      (U j)).toReal = ((samples j (n j) : Measure A) (B j)).toReal := by
    rw [show (ProbabilityMeasure.map (samples j (n j)) (profile j (n j)) : Measure X) =
      Measure.map (profile j (n j)) (samples j (n j) : Measure A) from rfl,
      Measure.map_apply (hp j (n j)) (hU j).measurableSet]
  have hm' j : Real.exp (-e j * scale j (n j)) ≤
      ((samples j (n j) : Measure A) (B j)).toReal := by simpa only [hmap] using hm j
  let ε := fun j => e j + ‖observe (f j) - observe g‖
  have herr : Tendsto (fun j => ‖observe (f j) - observe g‖) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self, norm_zero] using
      (((observe.continuous.tendsto g).comp hfg).sub (tendsto_const_nhds (x := observe g))).norm
  have hr0 j : 0 ≤ scale j (n j) := le_trans (by positivity) (hr j)
  have hscale : Tendsto (fun j => scale j (n j)) atTop atTop :=
    tendsto_atTop_mono (fun j => (le_add_of_nonneg_right zero_le_one).trans (hr j))
      tendsto_natCast_atTop_atTop
  refine ⟨n, B, ε, hn, hscale, fun j => (hp j (n j)) (hU j).measurableSet,
    fun j => (Real.exp_pos _).trans_le (hm' j),
    fun j => add_pos_of_pos_of_nonneg (he j) (norm_nonneg _), ?_, ?_, ?_⟩
  · simpa only [add_zero] using helim.add herr
  · intro δ hδ
    filter_upwards [helim.eventually (gt_mem_nhds hδ)] with j hj
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hj.le) (hr0 j))).trans
      (hm' j)
  · intro j a ha
    have hclose : ‖observe (profile j (n j) a) - observe (f j)‖ < e j := by
      simpa only [B, U, mem_preimage, Metric.mem_ball, dist_eq_norm] using ha
    have htri := norm_add_le (observe (profile j (n j) a) - observe (f j))
      (observe (f j) - observe g)
    rw [sub_add_sub_cancel] at htri
    exact htri.trans_lt (by dsimp only [ε]; linarith)

/-- Choose the outer parameter and then its scale so that one diagonal is
uniform on each successive compact set. Later path compacts can be absorbed
by an exhaustion without making the scale depend on a particular path. -/
theorem exists_diagonal_good_profiles_on_compacts
    {V W A : Type*} [TopologicalSpace V] [NormedAddCommGroup W] [MeasurableSpace A]
    (S : Set C(V, W)) [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (K : ℕ → Set V) (hK : ∀ j, IsCompact (K j))
    (scale : ℕ → ℕ → ℝ) (hs : ∀ j, Tendsto (scale j) atTop atTop)
    (samples : ℕ → ℕ → ProbabilityMeasure A) (profile : ℕ → ℕ → A → S)
    (hp : ∀ j n, Measurable (profile j n)) (ν : ℕ → ProbabilityMeasure S)
    (hν : ∀ j, Tendsto (fun n => ProbabilityMeasure.map (samples j n) (profile j n))
      atTop (𝓝 (ν j)))
    (f : ℕ → S) (g : S) (hf : ∀ j, f j ∈ (ν j : Measure S).support)
    (hfg : Tendsto f atTop (𝓝 g))
    (P : ℕ → ℕ → Prop) (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ (u n : ℕ → ℕ) (B : ℕ → Set A),
      Tendsto u atTop atTop ∧ (∀ j, P (u j) (n j)) ∧
      Tendsto (fun j => scale (u j) (n j)) atTop atTop ∧
      (∀ j, MeasurableSet (B j)) ∧
      (∀ j, 0 < ((samples (u j) (n j) : Measure A) (B j)).toReal) ∧
      HasSubexponentialLowerBoundSeq (fun j => scale (u j) (n j))
        (fun j => ((samples (u j) (n j) : Measure A) (B j)).toReal) ∧
      ∀ j a, a ∈ B j → ∀ z ∈ K j,
        ‖(profile (u j) (n j) a).val z - g.val z‖ < 2 / ((j : ℝ) + 1) := by
  let : ∀ j, CompactSpace (K j) := fun j => isCompact_iff_compactSpace.mp (hK j)
  let observe : ∀ j, C(S, C(K j, W)) := fun j =>
    ⟨fun g => g.val.comp ⟨Subtype.val, continuous_subtype_val⟩,
      (ContinuousMap.continuous_precomp ⟨Subtype.val, continuous_subtype_val⟩).comp
        continuous_subtype_val⟩
  let e : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have he j : 0 < e j := by dsimp [e]; positivity
  have hclose j : ∀ᶠ m in atTop, ‖observe j (f m) - observe j g‖ < e j := by
    have ht := (((observe j).continuous.tendsto g).comp hfg).sub
      (tendsto_const_nhds (x := observe j g))
    have htn : Tendsto (fun m => ‖observe j (f m) - observe j g‖) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, sub_self, norm_zero] using ht.norm
    exact htn.eventually (gt_mem_nhds (he j))
  have hu j : ∃ m, j ≤ m ∧ ‖observe j (f m) - observe j g‖ < e j :=
    ((eventually_ge_atTop j).and (hclose j)).exists
  choose u hule huc using hu
  have hut : Tendsto u atTop atTop := tendsto_atTop_mono hule tendsto_id
  let U : ℕ → Set S := fun j =>
    (observe j) ⁻¹' Metric.ball (observe j (f (u j))) (e j)
  have hU j : IsOpen (U j) := Metric.isOpen_ball.preimage (observe j).continuous
  have hfU j : f (u j) ∈ U j := by
    change dist (observe j (f (u j))) (observe j (f (u j))) < e j
    simpa only [dist_self] using he j
  obtain ⟨n, B, hn, hr, hB, hBpos, hmass, happ⟩ := exists_diagonal_supported_neighborhoods
    (fun j => scale (u j)) (fun j => hs (u j))
    (fun j => samples (u j)) (fun j => profile (u j)) (fun j => hp (u j))
    (fun j => ν (u j)) (fun j => hν (u j)) (fun j => f (u j)) (fun j => hf (u j))
    U hU hfU (fun j => P (u j)) (fun j => hP (u j))
  refine ⟨u, n, B, hut, hn, hr, hB, hBpos, hmass, ?_⟩
  intro j a ha z hz
  have hab : ‖observe j (profile (u j) (n j) a) - observe j (f (u j))‖ < e j := by
    simpa only [U, mem_preimage, Metric.mem_ball, dist_eq_norm] using happ j a ha
  have htriangle := norm_add_le
    (observe j (profile (u j) (n j) a) - observe j (f (u j)))
    (observe j (f (u j)) - observe j g)
  rw [sub_add_sub_cancel] at htriangle
  have hbound := (observe j (profile (u j) (n j) a) - observe j g).norm_coe_le_norm ⟨z, hz⟩
  change ‖(profile (u j) (n j) a).val z - g.val z‖ ≤ _ at hbound
  apply hbound.trans_lt (htriangle.trans_lt _)
  dsimp only [e] at hab huc
  rw [show (2 : ℝ) / ((j : ℝ) + 1) =
    1 / ((j : ℝ) + 1) + 1 / ((j : ℝ) + 1) by ring]
  exact add_lt_add hab (huc j)

end PolycyclicRecognition

end

end OAI
