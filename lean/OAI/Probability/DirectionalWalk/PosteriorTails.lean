import OAI.Probability.DirectionalWalk.PosteriorMax

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def posteriorSup {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ)
    (ω : Ω) : ℝ := ⨆ n : ℕ, posteriorMax w n ω

lemma posteriorSup_bounds {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1) (ω : Ω) :
    0 ≤ posteriorSup w ω ∧ posteriorSup w ω ≤ Fintype.card ι := by
  have hb : BddAbove (Set.range (fun n => posteriorMax w n ω)) :=
    ⟨Fintype.card ι,by rintro _ ⟨n,rfl⟩; exact posteriorMax_le_card w hpos hsum n ω⟩
  exact ⟨(posteriorMax_nonneg w hpos 0 ω).trans (le_ciSup hb 0),
    ciSup_le (fun n => posteriorMax_le_card w hpos hsum n ω)⟩

lemma posteriorMax_tendsto {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1) (ω : Ω) :
    Tendsto (fun n => posteriorMax w n ω) atTop (𝓝 (posteriorSup w ω)) := by
  exact tendsto_atTop_ciSup (posteriorMax_mono w ω)
    ⟨Fintype.card ι,by rintro _ ⟨n,rfl⟩; exact posteriorMax_le_card w hpos hsum n ω⟩

lemma measurable_posteriorSup {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (ℱ : Filtration ℕ m) (w : ι → ℕ → Ω → ℝ)
    (hw : ∀ e, Martingale (w e) ℱ μ) : Measurable (posteriorSup w) :=
  Measurable.iSup (fun n => (posteriorMax_adapted μ ℱ w hw n).mono (ℱ.le n) le_rfl)

lemma posteriorSup_exponential {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1)
    (L : ℕ) (hL : (Fintype.card ι : ℝ)*(1/2 : ℝ)^L ≤ 1) :
    (∫ ω, Real.exp (Real.log (3/2) / (2*(L+1)+1) * posteriorSup w ω) ∂μ) ≤ 12 := by
  let c : ℝ := Real.log (3/2) / (2*(L+1)+1)
  have hc : 0 ≤ c := div_nonneg (Real.log_nonneg (by norm_num)) (by positivity)
  have hM (n : ℕ) : Measurable (posteriorMax w n) := (posteriorMax_adapted μ ℱ w hw n).mono (ℱ.le n) le_rfl
  have hI (n : ℕ) : Integrable (fun ω => Real.exp (c*posteriorMax w n ω)) μ :=
    integrable_exp_of_bound μ _ (hM n) (Fintype.card ι) c (posteriorMax_le_card w hpos hsum n) hc
  have hS : Integrable (fun ω => Real.exp (c*posteriorSup w ω)) μ :=
    integrable_exp_of_bound μ _ (measurable_posteriorSup μ ℱ w hw) (Fintype.card ι) c
      (fun ω => (posteriorSup_bounds w hpos hsum ω).2) hc
  have ht := integral_tendsto_of_tendsto_of_monotone hI hS
    (Filter.Eventually.of_forall (fun ω n N hnN => Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (posteriorMax_mono w ω hnN) hc)))
    (Filter.Eventually.of_forall (fun ω => Real.continuous_exp.continuousAt.tendsto.comp
      ((posteriorMax_tendsto w hpos hsum ω).const_mul c)))
  apply le_of_tendsto ht
  filter_upwards [] with n
  exact geometric_tail_exponential μ (posteriorMax w n) (hM n) (Fintype.card ι)
    (posteriorMax_le_card w hpos hsum n) (2*(L+1)+1) (by have := Nat.cast_nonneg (α := ℝ) L; linarith)
    (posteriorMax_geometric_tail μ ℱ w hw hpos hsum L hL n)

noncomputable def goodPosteriorSet {Ω ι : Type*} [Fintype ι]
    (w : ι → ℕ → Ω → ℝ) (n : ℕ) : Set Ω := {ω | (∀ e, 0 ≤ w e n ω) ∧ ∑ e, w e n ω ≤ 1}

noncomputable def clippedPosterior {Ω ι : Type*} [Fintype ι]
    (w : ι → ℕ → Ω → ℝ) (e : ι) (n : ℕ) : Ω → ℝ := (goodPosteriorSet w n).indicator (w e n)

lemma measurableSet_goodPosterior {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (ℱ : Filtration ℕ m) (w : ι → ℕ → Ω → ℝ)
    (hw : ∀ e, Martingale (w e) ℱ μ) (n : ℕ) : MeasurableSet[ℱ n] (goodPosteriorSet w n) := by
  let : MeasurableSpace Ω := ℱ n
  unfold goodPosteriorSet
  rw [Set.ofPred_and,Set.ofPred_forall]
  apply MeasurableSet.inter
  ·
    exact MeasurableSet.iInter (fun e => measurableSet_le measurable_const ((hw e).stronglyMeasurable n).measurable)
  · exact measurableSet_le (Finset.measurable_sum _ (fun e _ => ((hw e).stronglyMeasurable n).measurable)) measurable_const

lemma clippedPosterior_bounds {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ) :
    (∀ e n ω, 0 ≤ clippedPosterior w e n ω) ∧ (∀ n ω, ∑ e, clippedPosterior w e n ω ≤ 1) := by
  constructor
  · intro e n ω
    by_cases hω : ω ∈ goodPosteriorSet w n
    · simpa only [clippedPosterior,Set.indicator_of_mem hω] using hω.1 e
    · simp only [clippedPosterior,Set.indicator_of_notMem hω,le_refl]
  · intro n ω
    by_cases hω : ω ∈ goodPosteriorSet w n
    · simpa only [clippedPosterior,Set.indicator_of_mem hω] using hω.2
    · simp only [clippedPosterior,Set.indicator_of_notMem hω,Finset.sum_const_zero]; norm_num

lemma clippedPosterior_ae_eq {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (w : ι → ℕ → Ω → ℝ)
    (hpos : ∀ e n, ∀ᵐ ω ∂μ, 0 ≤ w e n ω) (hsum : ∀ n, ∀ᵐ ω ∂μ, ∑ e, w e n ω ≤ 1)
    (e : ι) (n : ℕ) : w e n =ᵐ[μ] clippedPosterior w e n := by
  filter_upwards [(ae_all_iff.mpr (fun e => hpos e n)),hsum n] with ω hω hsumω
  exact (Set.indicator_of_mem (show ω ∈ goodPosteriorSet w n from ⟨hω,hsumω⟩) _).symm

lemma clippedPosterior_martingale {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (ℱ : Filtration ℕ m) (w : ι → ℕ → Ω → ℝ)
    (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e n, ∀ᵐ ω ∂μ, 0 ≤ w e n ω) (hsum : ∀ n, ∀ᵐ ω ∂μ, ∑ e, w e n ω ≤ 1) (e : ι) :
    Martingale (clippedPosterior w e) ℱ μ := by
  apply (hw e).congr
  · intro n
    exact ((hw e).stronglyMeasurable n).indicator (measurableSet_goodPosterior μ ℱ w hw n)
  · exact clippedPosterior_ae_eq μ w hpos hsum e

lemma posteriorSup_congr_ae {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (w v : ι → ℕ → Ω → ℝ) (h : ∀ e n, w e n =ᵐ[μ] v e n) :
    posteriorSup w =ᵐ[μ] posteriorSup v := by
  filter_upwards [ae_all_iff.mpr (fun e => ae_all_iff.mpr (h e))] with ω hω
  unfold posteriorSup
  congr 1
  funext n
  apply Finset.sum_congr rfl
  intro e _
  unfold runningMax
  congr 1
  funext i
  exact hω e i

noncomputable def posteriorLevel (m : ℕ) : ℕ := ⌈Real.log (m+1) / Real.log 2⌉₊

lemma posteriorLevel_dyadic (m : ℕ) : (m : ℝ) * (1/2 : ℝ)^(posteriorLevel m) ≤ 1 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil := Nat.le_ceil (Real.log (m+1) / Real.log 2)
  have hlog : Real.log (m+1) ≤ (posteriorLevel m : ℝ) * Real.log 2 :=
    (div_le_iff₀ h2).mp hceil
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by positivity),Real.exp_nat_mul,Real.exp_log (by norm_num)] at he
  have hpow : (2 : ℝ)^posteriorLevel m * (1/2 : ℝ)^posteriorLevel m = 1 := by
    rw [← mul_pow]; norm_num
  have hh := mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ (1/2 : ℝ)^posteriorLevel m)
  rw [hpow] at hh
  have hp : 0 ≤ (1/2 : ℝ)^posteriorLevel m := by positivity
  nlinarith

lemma posteriorLevel_scale (m : ℕ) (hm : 1 ≤ m) :
    2*((posteriorLevel m : ℝ)+1)+1 ≤ 7 * Real.log (m+1) / Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : Real.log 2 ≤ Real.log (m+1) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ m+1 by omega))
  have hq : 0 ≤ Real.log (m+1) / Real.log 2 := div_nonneg (h2.le.trans hB) h2.le
  have hceil : (posteriorLevel m : ℝ) < Real.log (m+1)/Real.log 2 + 1 := Nat.ceil_lt_add_one hq
  have hh : 1 ≤ Real.log (m+1)/Real.log 2 := (le_div_iff₀ h2).mpr (by simpa using hB)
  have he : 7*Real.log (m+1)/Real.log 2 = 7*(Real.log (m+1)/Real.log 2) := by ring
  rw [he]
  linarith

noncomputable def posteriorExponent : ℝ := Real.log (3/2) * Real.log 2 / 7

lemma posteriorExponent_pos : 0 < posteriorExponent := by
  exact div_pos (mul_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))) (by norm_num)

lemma posteriorExponent_le (m : ℕ) (hm : 1 ≤ m) :
    posteriorExponent / Real.log (m+1) ≤ Real.log (3/2) / (2*((posteriorLevel m : ℝ)+1)+1) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 < Real.log (m+1) := Real.log_pos (by exact_mod_cast (show 1 < m+1 by omega))
  have hb : 0 < 2*((posteriorLevel m : ℝ)+1)+1 := by positivity
  have hscale := (le_div_iff₀ h2).mp (posteriorLevel_scale m hm)
  apply (div_le_div_iff₀ hB hb).mpr
  unfold posteriorExponent
  have hl : 0 ≤ Real.log (3/2) := Real.log_nonneg (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hscale hl
  nlinarith

lemma setIntegral_entropy_of_exp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Integrable X μ) (c : ℝ) (hc : 0 < c)
    (hE : Integrable (fun ω => Real.exp (c*X ω)) μ)
    (hbound : (∫ ω, Real.exp (c*X ω) ∂μ) ≤ 12) (V : Set Ω) :
    (∫ ω in V, X ω ∂μ) ≤ (12/c) * μ.real V * (1-Real.log (μ.real V)) := by
  let p := μ.real V
  by_cases hp : p = 0
  · change μ.real V = 0 at hp
    have hz : μ V = 0 := (measureReal_eq_zero_iff (by finiteness)).mp hp
    simp only [Measure.restrict_eq_zero.mpr hz,integral_zero_measure,hp,mul_zero,zero_mul,le_refl]
  · have hp0 : 0 < p := lt_of_le_of_ne measureReal_nonneg (Ne.symm hp)
    have hp1 : p ≤ 1 := measureReal_le_one
    have hlog : Real.log p ≤ 0 := Real.log_nonpos hp0.le hp1
    have hpoint (ω : Ω) : c*X ω ≤ p*Real.exp (c*X ω) - Real.log p := by
      have h := Real.add_one_le_exp (c*X ω + Real.log p)
      rw [Real.exp_add,Real.exp_log hp0] at h
      nlinarith
    have hi : (∫ ω in V, c*X ω ∂μ) ≤ ∫ ω in V, (p*Real.exp (c*X ω)-Real.log p) ∂μ :=
      integral_mono (hX.restrict.const_mul c)
      ((hE.restrict.const_mul p).sub (integrable_const (Real.log p))) hpoint
    rw [integral_const_mul,integral_sub (hE.restrict.const_mul p) (integrable_const _),
      integral_const_mul,integral_const,measureReal_restrict_apply_univ,smul_eq_mul] at hi
    have he : (∫ ω in V, Real.exp (c*X ω) ∂μ) ≤ 12 :=
      (setIntegral_le_integral hE (Filter.Eventually.of_forall (fun ω => Real.exp_nonneg _))).trans hbound
    have hcore : c * (∫ ω in V, X ω ∂μ) ≤ 12*p*(1-Real.log p) := by
      change c * (∫ ω in V, X ω ∂μ) ≤ _ at hi
      have hh := mul_le_mul_of_nonneg_left he hp0.le
      have hl := mul_nonpos_of_nonneg_of_nonpos hp0.le hlog
      dsimp [p] at hi ⊢
      dsimp [p] at hh hl
      nlinarith
    calc
      _ ≤ 12*p*(1-Real.log p)/c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hcore)
      _ = _ := by dsimp [p]; ring

lemma posteriorSup_exponential_log {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1) :
    (∫ ω, Real.exp (posteriorExponent / Real.log (Fintype.card ι+1) * posteriorSup w ω) ∂μ) ≤ 12 := by
  have hm : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ‹Nonempty ι›
  have hB : 0 < Real.log (Fintype.card ι+1) := Real.log_pos (by exact_mod_cast (show 1 < Fintype.card ι+1 by omega))
  let c := posteriorExponent / Real.log (Fintype.card ι+1)
  let c' := Real.log (3/2) / (2*((posteriorLevel (Fintype.card ι) : ℝ)+1)+1)
  have hle : c ≤ c' := posteriorExponent_le _ hm
  have hc : 0 ≤ c := (div_pos posteriorExponent_pos hB).le
  have hc' : 0 ≤ c' := hc.trans hle
  have hmeas := measurable_posteriorSup μ ℱ w hw
  have hb := fun ω => (posteriorSup_bounds w hpos hsum ω).2
  have hi := integral_mono (integrable_exp_of_bound μ _ hmeas _ c hb hc)
    (integrable_exp_of_bound μ _ hmeas _ c' hb hc') (show ∀ ω, Real.exp (c*posteriorSup w ω) ≤ Real.exp (c'*posteriorSup w ω) from by
      intro ω
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hle (posteriorSup_bounds w hpos hsum ω).1))
  exact hi.trans (posteriorSup_exponential μ ℱ w hw hpos hsum _ (posteriorLevel_dyadic _))

lemma posteriorSup_exponential_log_ae {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i, ∀ᵐ ω ∂μ, 0 ≤ w e i ω) (hsum : ∀ i, ∀ᵐ ω ∂μ, ∑ e, w e i ω ≤ 1) :
    (∫ ω, Real.exp (posteriorExponent / Real.log (Fintype.card ι+1) * posteriorSup w ω) ∂μ) ≤ 12 := by
  have he := posteriorSup_congr_ae μ w (clippedPosterior w) (clippedPosterior_ae_eq μ w hpos hsum)
  have hi : (∫ ω, Real.exp (posteriorExponent / Real.log (Fintype.card ι+1) * posteriorSup w ω) ∂μ) =
      ∫ ω, Real.exp (posteriorExponent / Real.log (Fintype.card ι+1) * posteriorSup (clippedPosterior w) ω) ∂μ := by
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    rw [hω]
  rw [hi]
  exact posteriorSup_exponential_log μ ℱ (clippedPosterior w)
    (clippedPosterior_martingale μ ℱ w hw hpos hsum)
    (clippedPosterior_bounds w).1 (clippedPosterior_bounds w).2

lemma integrable_posteriorSup_ae {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m)
    (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i, ∀ᵐ ω ∂μ, 0 ≤ w e i ω) (hsum : ∀ i, ∀ᵐ ω ∂μ, ∑ e, w e i ω ≤ 1) :
    Integrable (posteriorSup w) μ := by
  have he := posteriorSup_congr_ae μ w (clippedPosterior w) (clippedPosterior_ae_eq μ w hpos hsum)
  apply (integrable_const (Fintype.card ι : ℝ)).mono' (measurable_posteriorSup μ ℱ w hw).aestronglyMeasurable
  filter_upwards [he] with ω hω
  rw [hω,Real.norm_eq_abs,abs_of_nonneg (posteriorSup_bounds _ (clippedPosterior_bounds w).1 (clippedPosterior_bounds w).2 ω).1]
  exact (posteriorSup_bounds _ (clippedPosterior_bounds w).1 (clippedPosterior_bounds w).2 ω).2

lemma integrable_posteriorSup_exp_ae {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m)
    (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i, ∀ᵐ ω ∂μ, 0 ≤ w e i ω) (hsum : ∀ i, ∀ᵐ ω ∂μ, ∑ e, w e i ω ≤ 1)
    (c : ℝ) (hc : 0 ≤ c) : Integrable (fun ω => Real.exp (c * posteriorSup w ω)) μ := by
  have he := posteriorSup_congr_ae μ w (clippedPosterior w) (clippedPosterior_ae_eq μ w hpos hsum)
  have hm := measurable_posteriorSup μ ℱ w hw
  apply (integrable_const (Real.exp (c*Fintype.card ι))).mono' (hm.const_mul c).exp.aestronglyMeasurable
  filter_upwards [he] with ω hω
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),hω]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (posteriorSup_bounds _ (clippedPosterior_bounds w).1 (clippedPosterior_bounds w).2 ω).2 hc)

lemma posteriorSup_joint_event_weight {Ω Ξ ι : Type*} [m : MeasurableSpace Ω] [MeasurableSpace Ξ]
    [Fintype ι] [Nonempty ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (π : Ξ → Ω) (hπ : MeasurePreserving π ν μ)
    (ℱ : Filtration ℕ m) (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i, ∀ᵐ ω ∂μ, 0 ≤ w e i ω) (hsum : ∀ i, ∀ᵐ ω ∂μ, ∑ e, w e i ω ≤ 1)
    (V : Set Ξ) :
    (∫ ξ in V, posteriorSup w (π ξ) ∂ν) ≤
      (12/posteriorExponent) * Real.log (Fintype.card ι+1) * ν.real V * (1-Real.log (ν.real V)) := by
  let c := posteriorExponent / Real.log (Fintype.card ι+1)
  have hm : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ‹Nonempty ι›
  have hB : 0 < Real.log (Fintype.card ι+1) := Real.log_pos (by exact_mod_cast (show 1 < Fintype.card ι+1 by omega))
  have hc : 0 < c := div_pos posteriorExponent_pos hB
  have hXe := integrable_posteriorSup_exp_ae μ ℱ w hw hpos hsum c hc.le
  have hXI := integrable_posteriorSup_ae μ ℱ w hw hpos hsum
  have hExp : (∫ ξ, Real.exp (c * posteriorSup w (π ξ)) ∂ν) ≤ 12 := by
    have hi : (∫ ξ, Real.exp (c * posteriorSup w (π ξ)) ∂ν) =
        ∫ ω, Real.exp (c * posteriorSup w ω) ∂μ := by
      rw [← hπ.map_eq]
      exact (integral_map_of_stronglyMeasurable hπ.measurable
        (((measurable_posteriorSup μ ℱ w hw).const_mul c).exp.stronglyMeasurable)).symm
    rw [hi]
    exact posteriorSup_exponential_log_ae μ ℱ w hw hpos hsum
  have hi := setIntegral_entropy_of_exp ν (fun ξ => posteriorSup w (π ξ))
    (hπ.integrable_comp_of_integrable hXI) c hc (hπ.integrable_comp_of_integrable hXe) hExp V
  have hscale : 12/c = (12/posteriorExponent) * Real.log (Fintype.card ι+1) := by
    dsimp [c]
    field_simp
  simpa only [hscale] using hi

lemma ae_atom_pos {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) : ∀ᵐ x ∂μ, μ {x} ≠ 0 := by
  simp only [ae_iff]
  have h : {x | ¬ μ {x} ≠ 0} = ⋃ x : {x // μ {x} = 0}, ({x.val} : Set α) := by
    ext x
    simp
  rw [h]
  exact measure_iUnion_null fun x => x.property

end DirectionalZeroOne

end OAI
