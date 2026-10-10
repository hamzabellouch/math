import OAI.Dynamics.StandardMap.FineMoments

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace StandardMapEntropy
lemma single_shortfall_max_integral (k:ℝ) (hk:0≤k) (p:ℕ) (ε:ℝ) (hε:0<ε) :
    (∫d,max (arrayShortfall 0 (dyadicInt 1) d) 0 ∂scaleLaw k hk p 1 ε)=meanDeficit k (2^p)/ε := by
  rw [integral_scaleLaw _ _ _ _ _ hε _ ((continuous_arrayShortfall _ _).max continuous_const)]
  simp only [Finset.range_one,Finset.sum_singleton,Nat.add_zero]
  let n:ℕ:=2^p
  have hn : 0<n := by dsimp [n]; positivity
  have hs : (n:ℝ)*(0:DyadicTime)=((0:ℤ):ℝ) := by simp
  have ht : (n:ℝ)*(dyadicInt 1:ℝ)=((0:ℤ):ℝ)+(n:ℝ) := by simp
  have he : (∫d,max (arrayShortfall 0 (dyadicInt 1) d) 0 ∂sampleLaw k hk (2^p) hn)=
      ∫d,arrayShortfall 0 (dyadicInt 1) d ∂sampleLaw k hk (2^p) hn := by
    rw [integral_sampleLaw _ _ _ _ _ ((continuous_arrayShortfall _ _).max continuous_const),
      integral_sampleLaw _ _ _ _ _ (continuous_arrayShortfall _ _)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    dsimp only
    rw [shortfall_sample_aligned k hk z n hn 0 (dyadicInt 1) 0 (2^p) hn hs ht]
    exact max_eq_left (torusShortfall_mem k hk z 0 (2^p) hn).1
  rw [he,integral_shortfall_sample k hk n hn 0 (dyadicInt 1) 0 (2^p) hn hs ht]
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma initial_cap_tendsto {α:ℝ} (hα:0≤α) (hα1:α≤1) :
    Tendsto (fun i => ∫d,capF α d ∂S.initialLaw i) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := entropyCap_upper hα hα1
  have he (i:ℕ) : (∫d,capF α d ∂S.initialLaw i)=(∫d,capFpos α d ∂S.initialLaw i) :=
    capF_scale_integral _ _ _ _ _ (S.epsilon_pos i) α
  simp_rw [he]
  apply squeeze_zero (fun i => integral_nonneg (capFpos_nonneg hα hα1))
    (fun i => ?_) (by simpa only [mul_zero,Nat.add_zero] using (S.initial_ratio_tendsto 0).const_mul C)
  have hi := (continuous_capFpos α).integrable_of_hasCompactSupport (μ := S.initialLaw i) (HasCompactSupport.of_compactSpace _)
  have hh : Integrable (fun d => max (arrayShortfall 0 (dyadicInt 1) d) 0) (S.initialLaw i) :=
    ((continuous_arrayShortfall _ _).max continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hx := integral_mono hi (hh.const_mul C) (fun d => hb _ (shortfall_one_max_mem d))
  rw [integral_const_mul,initialLaw,single_shortfall_max_integral _ _ _ _ (S.epsilon_pos i)] at hx
  exact hx
lemma multiLaw_translate_one (i:ℕ) : (S.multiLaw i).map (arrayTranslate (dyadicInt 1))=S.multiLaw i := by
  apply scaleLaw_translate _ _ _ _ _ _ ((2:ℤ)^(criticalLowerExponent S.offset i))
  simp
lemma integral_F_dilation_balance (i:ℕ) (F:DistanceArray→ℝ) (hF:Continuous F) :
    (∫d,F (arrayDilate d) ∂S.multiLaw i)+(∫d,F d ∂S.initialLaw i)=
      (∫d,F d ∂S.multiLaw i)+(∫d,F d ∂S.terminalLaw i) := by
  rw [←integral_map continuous_arrayDilate.measurable.aemeasurable hF.aestronglyMeasurable]
  have hi (μ:Measure DistanceArray) [IsFiniteMeasure μ] : Integrable F μ :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [←integral_add_measure (hi _) (hi _),←integral_add_measure (hi _) (hi _),S.law_dilation_balance i]
lemma capG_prelimit_balance (i:ℕ) (α:ℝ) :
    (∫d,capG α d ∂S.multiLaw i)=(∫d,capF α d ∂S.terminalLaw i)-(∫d,capF α d ∂S.initialLaw i) := by
  have h1 := (continuous_capF α).integrable_of_hasCompactSupport (μ := S.multiLaw i) (HasCompactSupport.of_compactSpace _)
  have hd := ((continuous_capF α).comp continuous_arrayDilate).integrable_of_hasCompactSupport (μ := S.multiLaw i) (HasCompactSupport.of_compactSpace _)
  have ht := ((continuous_capF α).comp (continuous_arrayTranslate (dyadicInt 1))).integrable_of_hasCompactSupport (μ := S.multiLaw i) (HasCompactSupport.of_compactSpace _)
  simp_rw [capG_coboundary]
  have he := integral_sub hd ((h1.add ht).div_const 2)
  simp only [Pi.add_apply,Function.comp_apply] at he
  rw [he,integral_div]
  have hea := integral_add h1 ht
  simp only [Function.comp_apply] at hea
  rw [hea]
  rw [←integral_map (continuous_arrayTranslate (dyadicInt 1)).measurable.aemeasurable (continuous_capF α).aestronglyMeasurable,S.multiLaw_translate_one i]
  linarith [S.integral_F_dilation_balance i (capF α) (continuous_capF α)]
lemma capG_prelimit_tendsto {α H:ℝ} (hα:0≤α) (hα1:α≤1)
    (hH:Tendsto (fun i => ∫d,capF α d ∂S.terminalLaw i) (L.filter:Filter ℕ) (𝓝 H)) :
    Tendsto (fun i => ∫d,capG α d ∂S.multiLaw i) (L.filter:Filter ℕ) (𝓝 H) := by
  simp_rw [S.capG_prelimit_balance]
  simpa only [sub_zero] using hH.sub ((S.initial_cap_tendsto hα hα1).mono_left L.refines)
end CriticalScaleSequence
end StandardMapEntropy

end OAI
