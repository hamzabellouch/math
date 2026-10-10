import Mathlib
import OAI.Probability.Ballisticity.Estimates.RawDropBounds
import OAI.Probability.Ballisticity.Stationary.BadArraySampling

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma bad_stageMark_bound (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (N : ℕ) (hN : C.sfloor ≤ (N:ℝ))
    (hlarge : 32*C.b ≤ (1/2:ℝ)*Real.log (N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2)))
    (B : ℝ≥0) :
    (∫ Y, stageMarkCut e B 0 Y ∂(C.occupation hef N
      ((environmentLaw ν)[|badCrossingEvent e N (1/2)]) : Measure (ActualEpisodeArray e))) ≤
      C.injectionCost/(6*C.b) := by
  let Q := (environmentLaw ν)[|badCrossingEvent e N (1/2)]
  have hN0 : 0<N := by exact_mod_cast lt_of_lt_of_le zero_lt_one (C.hs.trans hN)
  have : IsProbabilityMeasure Q := cond_isProbabilityMeasure
    (badCrossingEvent_pos e N (1/2) D (environmentLaw ν) hN0 hmass)
  let M : ℝ := ∫ ω, (C.activeCount hef N ω:ℝ) ∂Q
  let J : ℝ := ∫ ω, (EpisodeChainLedger.steps (k:=C.k) e f hef (episodeScaleRadius ν e f)
        C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω N:ℝ) ∂Q
  have hM : 0<M := EpisodeChainLedger.operational_mass_positive (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N Q hN0
  have he := EpisodeChainLedger.operational_raw_mass (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ν Q
  have hkl := badCrossing_cond_entropy e N (1/2) D (environmentLaw ν) hN0 hmass
  have hj := actual_expected_stages (k:=C.k) ν e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.K D (1/2) C.radius_nonneg N C.hs hN
    C.hf.le C.hg C.hb C.hK hD C.height C.stages Q hkl C.coeff C.small hlarge
  change 2*C.b*J ≤ (1/2:ℝ)/4*Real.log (N:ℝ) at hj
  obtain ⟨L,hL,hcharge⟩ := C.finite_charge
  have hm := (C.conditional_episode_drops hef hD N hN hlarge hmass L hL hcharge).1
  change 3/8*Real.log (N:ℝ) ≤ C.injectionCost*M at hm
  have hJM : 6*C.b*J ≤ C.injectionCost*M := by nlinarith only [hj,hm]
  have hraw := C.raw_stageMark_bound hef N Q B
  have hmean : M⁻¹*J ≤ C.injectionCost/(6*C.b) := by
    apply (le_div_iff₀ (show 0<6*C.b by nlinarith [C.hb])).mpr
    have hh := mul_le_mul_of_nonneg_left hJM (inv_nonneg.mpr hM.le)
    have hid : M⁻¹*(C.injectionCost*M)=C.injectionCost := by field_simp
    rw [hid] at hh
    nlinarith only [hh]
  change (∫ Y, stageMarkCut e B 0 Y ∂(actualOccupation e ν Q
    (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N)
    N (C.activeCount hef N) : Measure (ActualEpisodeArray e))) ≤ _
  rw [actualOccupation_integral e ν Q _ _ _ _ _ (C.bad_raw_mass_pos hef N hN hmass)]
  have he' : (actualOccupationRaw e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) N (C.activeCount hef N)).real Set.univ=M := he
  rw [he']
  exact (mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hM.le)).trans hmean

lemma bad_limit_finite_stages (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), (Y.1 0).2.1<⊤) ∧
      Integrable (fun Y => ((Y.1 0).2.1).toENNReal.toReal) (ρ : Measure (ActualEpisodeArray e)) := by
  let F : C(ActualEpisodeArray e,ℝ≥0∞) := ⟨fun Y => ((Y.1 0).2.1).toENNReal,
    ENat.continuous_toENNReal.comp (by fun_prop)⟩
  have hh := mark_lintegral_bound_of_weak_limit _ ρ hlim F (C.injectionCost/(6*C.b))
    (fun n B => C.bad_stageMark_bound hef hD (Ns n) (hN n) (hlarge n) (hmass n) B)
  have hf := mark_integrable_of_lintegral_bound (ρ : Measure (ActualEpisodeArray e)) F
    F.continuous.measurable _ hh
  refine ⟨hf.1.mono (fun Y h => ?_),hf.2⟩
  change ((Y.1 0).2.1).toENNReal<∞ at h
  simpa using h

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

lemma bad_dropMarkCut_lower (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (N : ℕ) (hN : C.sfloor ≤ (N:ℝ))
    (hlarge : 32*C.b ≤ (1/2:ℝ)*Real.log (N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2)))
    (L : ℕ) (hL : 0<L) (hcharge : C.injectionCost ≤ 2*C.b*L)
    (B : ℝ≥0) (hB : C.injectionCost+2*C.b*L ≤ B) :
    C.b ≤ ∫ Y, dropMarkCut e B 0 Y ∂(C.occupation hef N
      ((environmentLaw ν)[|badCrossingEvent e N (1/2)]) : Measure (ActualEpisodeArray e)) := by
  let Q := (environmentLaw ν)[|badCrossingEvent e N (1/2)]
  have hN0 : 0<N := by exact_mod_cast lt_of_lt_of_le zero_lt_one (C.hs.trans hN)
  have : IsProbabilityMeasure Q := cond_isProbabilityMeasure
    (badCrossingEvent_pos e N (1/2) D (environmentLaw ν) hN0 hmass)
  have hκQ : ∀ᵐ ω ∂Q, ∀ y u, C.κ ≤ (ω y).1 u :=
    (cond_absolutelyContinuous (μ:=environmentLaw ν) (s:=badCrossingEvent e N (1/2))).ae_le C.rows
  let M : ℝ := ∫ ω, (C.activeCount hef N ω:ℝ) ∂Q
  have hM : 0<M := EpisodeChainLedger.operational_mass_positive (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N Q hN0
  let raw := actualOccupationRaw e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) N (C.activeCount hef N)
  obtain ⟨_,hm,hsum⟩ := C.conditional_episode_drops hef hD N hN hlarge hmass L hL hcharge
  have hd : C.b*(Real.log (N:ℝ)/(16*C.b)+1)=Real.log (N:ℝ)/16+C.b := by
    field_simp [ne_of_gt C.hb]
  have hm' : C.b*M ≤ Real.log (N:ℝ)/16+C.b := by
    rw [←hd]
    exact mul_le_mul_of_nonneg_left hm C.hb.le
  have hraw : C.b*M ≤ ∫ Y, dropMarkCut e B 0 Y ∂raw := by
    apply (show C.b*M ≤ (1/4:ℝ)*Real.log (N:ℝ) by nlinarith only [hm',hlarge,C.hb]).trans
    exact hsum.trans (C.raw_dropCut_lower hef N L Q hκQ B hB)
  change C.b ≤ ∫ Y, dropMarkCut e B 0 Y ∂(actualOccupation e ν Q
    (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N)
    N (C.activeCount hef N) : Measure (ActualEpisodeArray e))
  rw [actualOccupation_integral e ν Q _ _ _ _ _ (C.bad_raw_mass_pos hef N hN hmass)]
  have he : raw.real Set.univ=M := EpisodeChainLedger.operational_raw_mass (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ν Q
  change C.b ≤ (raw.real Set.univ)⁻¹ * ∫ Y, dropMarkCut e B 0 Y ∂raw
  rw [he]
  calc C.b = M⁻¹*(C.b*M) := by field_simp [ne_of_gt hM]
       _ ≤ _ := mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hM.le)

lemma bad_limit_positive_cut (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    ∃ B : ℝ≥0, C.b ≤ ∫ Y, dropMarkCut e B 0 Y ∂(ρ : Measure (ActualEpisodeArray e)) := by
  obtain ⟨L,hL,hcharge⟩ := C.finite_charge
  let B : ℝ≥0 := ⟨C.injectionCost+2*C.b*L,by have hA := C.cost_nonneg; have hb := C.hb; positivity⟩
  refine ⟨B,?_⟩
  exact ge_of_tendsto ((ProbabilityMeasure.continuous_integral_continuousMap (dropMarkCut e B 0)).continuousAt.tendsto.comp hlim)
    (Filter.Eventually.of_forall (fun n => C.bad_dropMarkCut_lower hef hD (Ns n) (hN n) (hlarge n) (hmass n) L hL hcharge B le_rfl))

end OperationalConstants
end DirectionalTransience

end

end OAI
