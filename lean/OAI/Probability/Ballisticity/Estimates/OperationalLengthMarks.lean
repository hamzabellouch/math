import Mathlib
import OAI.Probability.Ballisticity.Estimates.BadStageMoment
import OAI.Probability.Ballisticity.Estimates.RawDropBounds
import OAI.Probability.Ballisticity.Stationary.EpisodeLogLength

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

noncomputable def logLengthMark {d : ℕ} (e : Direction d) : C(ActualEpisodeArray e,ℝ≥0∞) :=
  ⟨fun Y => (ENNReal.log (1+(Y.1 0).1.toENNReal)).toENNReal,
    EReal.continuous_toENNReal.comp (ENNReal.continuous_log.comp
      (continuous_const.add (ENat.continuous_toENNReal.comp (by fun_prop))))⟩

noncomputable def logLengthCut {d : ℕ} (e : Direction d) (B : ℝ≥0) : C(ActualEpisodeArray e,ℝ) :=
  (cutENNReal B).comp (logLengthMark e)

lemma raw_actual_test_mono {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M)
    (F G : C(ActualEpisodeArray e,ℝ))
    (hFG : ∀ i X, F (StationaryCompact.shift^[i] (actualArrayMap e t J X)) ≤
      G (StationaryCompact.shift^[i] (actualArrayMap e t J X))) :
    (∫ Y, F Y ∂actualOccupationRaw e ν Q t J ht N M) ≤
      ∫ Y, G Y ∂actualOccupationRaw e ν Q t J ht N M := by
  rw [actualOccupationRaw_integral e ν Q t J ht hJ N M hM F,
    actualOccupationRaw_integral e ν Q t J ht hJ N M hM G]
  apply Finset.sum_le_sum
  intro i _
  have hm : Measurable (fun X => StationaryCompact.shift^[i] (actualArrayMap e t J X)) :=
    (StationaryCompact.shift_continuous.measurable.iterate i).comp (actualArrayMap_measurable e t J ht hJ)
  apply integral_mono
    ((F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).comp_measurable hm)
    ((G.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).comp_measurable hm)
  exact hFG i

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)}
  {e f : Direction d} {D : ℝ}

noncomputable def lengthCost (C : OperationalConstants ν e f D) : ℝ :=
  Real.log 2+Real.log (1+C.sfloor*Real.exp (C.χ*C.b))+1+C.g*C.b

lemma lengthCost_nonneg (C : OperationalConstants ν e f D) : 0≤C.lengthCost := by
  have hs : 0≤C.sfloor := le_trans (by norm_num) C.hs
  have hl := Real.log_nonneg (show 1≤1+C.sfloor*Real.exp (C.χ*C.b) by linarith [mul_nonneg hs (Real.exp_pos (C.χ*C.b)).le])
  have ht := Real.log_nonneg (by norm_num : (1:ℝ)≤2)
  have hg := mul_nonneg C.hg.le C.hb.le
  unfold lengthCost
  linarith

lemma actual_lengthMark (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (X : EpisodeInput e) :
    ((StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
      (C.paddedStages hef N) X)).1 0).1 =
      ((episodeBoundary (k:=C.k) e f hef (episodeScaleRadius ν e f) C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N X.1.1 (i+1)-
        episodeBoundary (k:=C.k) e f hef (episodeScaleRadius ν e f) C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N X.1.1 i:ℕ):ℕ∞) := by
  rw [arrayMark_iterate]
  simp only [zero_add,actualArrayMap,paddedTimes,EpisodeChainLedger.arrayTime,Int.toNat_natCast,
    show (i:ℤ)+1=((i+1:ℕ):ℤ) by omega]

lemma logLengthCut_actual_le (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (B : ℝ≥0) (X : EpisodeInput e) :
    logLengthCut e B (StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
      (C.paddedStages hef N) X)) ≤ C.lengthCost*(1+(C.stagesAt hef N X.1.1 i:ℝ)) := by
  let T := episodeBoundary (k:=C.k) e f hef (episodeScaleRadius ν e f) C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N X.1.1
  have hlog : 0≤Real.log (1+(T (i+1)-T i:ℕ)) := Real.log_nonneg (by exact le_add_of_nonneg_right (Nat.cast_nonneg _))
  change (min (ENNReal.log (1+((StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
      (C.paddedStages hef N) X)).1 0).1.toENNReal)).toENNReal (B:ℝ≥0∞)).toReal ≤ _
  rw [C.actual_lengthMark]
  change (min (ENNReal.log (1+(T (i+1)-T i:ℕ))).toENNReal (B:ℝ≥0∞)).toReal ≤ _
  have he : (ENNReal.log (1+(T (i+1)-T i:ℕ))).toENNReal =
      ENNReal.ofReal (Real.log (1+(T (i+1)-T i:ℕ))) := by
    generalize T (i+1)-T i = n
    rw [ENNReal.log_pos_real (by positivity) (by finiteness), EReal.real_coe_toENNReal,
      ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.natCast_ne_top n)]
    simp
  rw [he,ENNReal.toReal_min ENNReal.ofReal_ne_top ENNReal.coe_ne_top,
    ENNReal.toReal_ofReal hlog]
  apply (min_le_left _ _).trans
  by_cases ha : T i<N
  · have hh := episode_log_length_bound (k:=C.k) e f hef (episodeScaleRadius ν e f)
      C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N (T i) X.1.1
      C.hf.le C.hg.le C.hb.le (lt_of_lt_of_le zero_lt_one C.hs)
    simpa only [T,episodeBoundary,ite_eq_left ha,lengthCost,stagesAt,EpisodeChainLedger.stepMark,episodeStageCount] using hh
  · have heq : T (i+1)=T i := by simp only [T,episodeBoundary,ite_eq_right ha]
    rw [heq,Nat.sub_self,Nat.cast_zero,add_zero,Real.log_one]
    exact mul_nonneg C.lengthCost_nonneg (by positivity)

end OperationalConstants
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma bad_logLengthCut_bound (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (N : ℕ) (hN : C.sfloor ≤ (N:ℝ))
    (hlarge : 32*C.b ≤ (1/2:ℝ)*Real.log (N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2)))
    (B : ℝ≥0) :
    (∫ Y, logLengthCut e B Y ∂(C.occupation hef N
      ((environmentLaw ν)[|badCrossingEvent e N (1/2)]) : Measure (ActualEpisodeArray e))) ≤
      C.lengthCost*(1+C.injectionCost/(6*C.b)) := by
  let Q := (environmentLaw ν)[|badCrossingEvent e N (1/2)]
  let μ : ProbabilityMeasure (ActualEpisodeArray e) := C.occupation hef N Q
  let G : C(ActualEpisodeArray e,ℝ) := (ContinuousMap.const _ C.lengthCost)*(1+stageMarkCut e (N:ℝ≥0) 0)
  have hh := raw_actual_test_mono e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) (C.paddedStages_measurable hef N) N (C.activeCount hef N)
    (C.activeCount_measurable hef N) (logLengthCut e B) G (fun i X => by
      change _ ≤ C.lengthCost*(1+stageMarkCut e (N:ℝ≥0) 0
        (StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N) (C.paddedStages hef N) X)))
      rw [C.stageMarkCut_actual hef N i]
      have hj : (C.stagesAt hef N X.1.1 i:ℝ)≤(N:ℝ) := by
        exact_mod_cast EpisodeChainLedger.stepMark_le (k:=C.k) e f hef (episodeScaleRadius ν e f)
          C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N X.1.1 i
      rw [show ((N:ℝ≥0):ℝ)=(N:ℝ) by simp,min_eq_left hj]
      exact C.logLengthCut_actual_le hef N i B X)
  have hm : (∫ Y, logLengthCut e B Y ∂(μ : Measure (ActualEpisodeArray e)))≤
      ∫ Y, G Y ∂(μ : Measure (ActualEpisodeArray e)) := by
    change (∫ Y, logLengthCut e B Y ∂(actualOccupation e ν Q
      (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N) N (C.activeCount hef N):Measure _)) ≤
      ∫ Y, G Y ∂(actualOccupation e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
      (C.paddedTimes_measurable hef N) N (C.activeCount hef N):Measure _)
    rw [actualOccupation_integral e ν Q _ _ _ _ _ (C.bad_raw_mass_pos hef N hN hmass),
      actualOccupation_integral e ν Q _ _ _ _ _ (C.bad_raw_mass_pos hef N hN hmass)]
    exact mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr ENNReal.toReal_nonneg)
  apply hm.trans
  change (∫ Y, C.lengthCost*(1+stageMarkCut e (N:ℝ≥0) 0 Y) ∂(μ:Measure _))≤_
  rw [integral_const_mul,integral_add (integrable_const _)
    ((stageMarkCut e (N:ℝ≥0) 0).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    integral_const,probReal_univ,one_smul]
  exact mul_le_mul_of_nonneg_left (add_le_add_right (C.bad_stageMark_bound hef hD N hN hlarge hmass (N:ℝ≥0)) 1)
    C.lengthCost_nonneg

lemma bad_limit_length_moment (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), (Y.1 0).1<⊤) ∧
      Integrable (fun Y => (logLengthMark e Y).toReal) (ρ : Measure (ActualEpisodeArray e)) := by
  have hh := mark_lintegral_bound_of_weak_limit _ ρ hlim (logLengthMark e)
    (C.lengthCost*(1+C.injectionCost/(6*C.b)))
    (fun n B => C.bad_logLengthCut_bound hef hD (Ns n) (hN n) (hlarge n) (hmass n) B)
  have hf := mark_integrable_of_lintegral_bound (ρ : Measure (ActualEpisodeArray e)) (logLengthMark e)
    (logLengthMark e).continuous.measurable _ hh
  refine ⟨hf.1.mono (fun Y h => ?_),hf.2⟩
  by_contra hn
  have he : (Y.1 0).1=⊤ := top_le_iff.mp (le_of_not_gt hn)
  have ht : logLengthMark e Y=∞ := by simp [logLengthMark,he]
  rw [ht] at h
  exact (lt_irrefl _ h)

end OperationalConstants
end DirectionalTransience

end

end OAI
