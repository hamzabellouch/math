import Mathlib
import OAI.Probability.Ballisticity.Estimates.RawDropBounds
import OAI.Probability.Ballisticity.Estimates.BadStageMoment

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma bad_dropMarkCut_upper (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (N : ℕ) (hN : C.sfloor ≤ (N:ℝ))
    (hlarge : 32*C.b ≤ (1/2:ℝ)*Real.log (N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2)))
    (B : ℝ≥0) :
    (∫ Y, dropMarkCut e B 0 Y ∂(C.occupation hef N
      ((environmentLaw ν)[|badCrossingEvent e N (1/2)]) : Measure (ActualEpisodeArray e))) ≤
      4/3*C.injectionCost := by
  let Q := (environmentLaw ν)[|badCrossingEvent e N (1/2)]
  have hN0 : 0<N := by exact_mod_cast lt_of_lt_of_le zero_lt_one (C.hs.trans hN)
  have : IsProbabilityMeasure Q := cond_isProbabilityMeasure
    (badCrossingEvent_pos e N (1/2) D (environmentLaw ν) hN0 hmass)
  have hκQ : ∀ᵐ ω ∂Q, ∀ y u, C.κ ≤ (ω y).1 u :=
    (cond_absolutelyContinuous (μ:=environmentLaw ν) (s:=badCrossingEvent e N (1/2))).ae_le C.rows
  let M : ℝ := ∫ ω, (C.activeCount hef N ω:ℝ) ∂Q
  let J : ℝ := ∫ ω, (EpisodeChainLedger.steps (k:=C.k) e f hef (episodeScaleRadius ν e f)
        C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω N:ℝ) ∂Q
  have hM : 0<M := EpisodeChainLedger.operational_mass_positive (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N Q hN0
  have hkl := badCrossing_cond_entropy e N (1/2) D (environmentLaw ν) hN0 hmass
  have hj := actual_expected_stages (k:=C.k) ν e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.K D (1/2) C.radius_nonneg N C.hs hN
    C.hf.le C.hg C.hb C.hK hD C.height C.stages Q hkl C.coeff C.small hlarge
  change 2*C.b*J ≤ (1/2:ℝ)/4*Real.log (N:ℝ) at hj
  obtain ⟨L,hL,hcharge⟩ := C.finite_charge
  have hm := (C.conditional_episode_drops hef hD N hN hlarge hmass L hL hcharge).1
  change 3/8*Real.log (N:ℝ) ≤ C.injectionCost*M at hm
  have hJM : 6*C.b*J ≤ C.injectionCost*M := by nlinarith only [hj,hm]
  have hraw := C.raw_dropCut_upper hef N Q hκQ B
  have hid : M⁻¹*(C.injectionCost*M)=C.injectionCost := by field_simp
  have hmean : M⁻¹*(C.injectionCost*M+2*C.b*J) ≤ 4/3*C.injectionCost := by
    have hh := mul_le_mul_of_nonneg_left hJM (inv_nonneg.mpr hM.le)
    rw [hid] at hh
    rw [mul_add,hid]
    nlinarith only [hh]
  change (∫ Y, dropMarkCut e B 0 Y ∂(actualOccupation e ν Q
    (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N)
    N (C.activeCount hef N) : Measure (ActualEpisodeArray e))) ≤ _
  rw [actualOccupation_integral e ν Q _ _ _ _ _ (C.bad_raw_mass_pos hef N hN hmass)]
  have he : (actualOccupationRaw e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) N (C.activeCount hef N)).real Set.univ=M :=
    EpisodeChainLedger.operational_raw_mass (k:=C.k) e f hef (episodeScaleRadius ν e f)
      C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ν Q
  rw [he]
  exact (mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hM.le)).trans hmean

lemma bad_limit_drop_moment (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), (Y.1 0).2.2<∞) ∧
      Integrable (fun Y => (Y.1 0).2.2.toReal) (ρ : Measure (ActualEpisodeArray e)) ∧
      C.b ≤ ∫ Y, (Y.1 0).2.2.toReal ∂(ρ : Measure (ActualEpisodeArray e)) := by
  let F : C(ActualEpisodeArray e,ℝ≥0∞) := ⟨fun Y => (Y.1 0).2.2,by fun_prop⟩
  have hh := mark_lintegral_bound_of_weak_limit _ ρ hlim F (4/3*C.injectionCost)
    (fun n B => C.bad_dropMarkCut_upper hef hD (Ns n) (hN n) (hlarge n) (hmass n) B)
  have hf := mark_integrable_of_lintegral_bound (ρ : Measure (ActualEpisodeArray e)) F
    F.continuous.measurable _ hh
  refine ⟨hf.1,hf.2,?_⟩
  obtain ⟨B,hB⟩ := C.bad_limit_positive_cut hef hD Ns hN hlarge hmass ρ hlim
  apply hB.trans
  apply integral_mono_ae ((dropMarkCut e B 0).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) hf.2
  filter_upwards [hf.1] with Y hY
  change (min (F Y) (B:ℝ≥0∞)).toReal ≤ (F Y).toReal
  exact ENNReal.toReal_mono hY.ne (min_le_left _ _)

end OperationalConstants
end DirectionalTransience

end

end OAI
