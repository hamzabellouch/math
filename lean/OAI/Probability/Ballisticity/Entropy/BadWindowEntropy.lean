import Mathlib
import OAI.Probability.Ballisticity.Geometry.WindowWeak
import OAI.Probability.Ballisticity.Estimates.BadOccupationLimit
import OAI.Probability.Ballisticity.Stationary.BadArraySampling

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)}
  {e f : Direction d} {D : ℝ}

lemma paddedTimes_stopping [IsProbabilityMeasure ν]
    (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (i : ℤ) (n : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)]
      {ω | C.paddedTimes hef N ω i=n} :=
  episodeBoundary_height_event (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N i.toNat n

lemma paddedTimes_mono [IsProbabilityMeasure ν]
    (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (ω : Environment d) : Monotone (fun i : ℕ => C.paddedTimes hef N ω i) := by
  simpa only [paddedTimes,EpisodeChainLedger.arrayTime_nat] using
    episodeBoundary_mono (k:=C.k) e f hef (episodeScaleRadius ν e f)
      C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω

lemma paddedTimes_active [IsProbabilityMeasure ν]
    (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (ω : Environment d) :
    C.paddedTimes hef N ω i<N ↔ i<C.activeCount hef N ω := by
  simpa only [paddedTimes,EpisodeChainLedger.arrayTime_nat,activeCount] using
    EpisodeChainLedger.active_iff_lt_number (k:=C.k) e f hef (episodeScaleRadius ν e f)
      C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω i

noncomputable def windowEntropyConstant (C : OperationalConstants ν e f D) : ℝ :=
  (8/3:ℝ)*D*C.injectionCost

lemma windowEntropyConstant_nonneg [IsProbabilityMeasure ν]
    (C : OperationalConstants ν e f D) (hD : 0≤D) :
    0≤C.windowEntropyConstant := mul_nonneg (mul_nonneg (by norm_num) hD) C.cost_nonneg

variable [IsProbabilityMeasure ν]

lemma bad_window_kl_le (C : OperationalConstants ν e f D) (hef : e.1≠f.1) (hD : 0≤D)
    (N m : ℕ) (hN : C.sfloor ≤ (N:ℝ))
    (hlarge : 32*C.b ≤ (1/2:ℝ)*Real.log (N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2))) :
    let W := actualCurrentLaw e m
      (C.occupation hef N ((environmentLaw ν)[|badCrossingEvent e N (1/2)]))
    klDiv (W : Measure (CurrentWindow e)) (currentReferenceLaw e ν W : Measure (CurrentWindow e)) ≤
      ENNReal.ofReal ((m:ℝ)*C.windowEntropyConstant) := by
  let Q := (environmentLaw ν)[|badCrossingEvent e N (1/2)]
  have hN0 : 0<N := by exact_mod_cast lt_of_lt_of_le zero_lt_one (C.hs.trans hN)
  have : IsProbabilityMeasure Q :=
    cond_isProbabilityMeasure (badCrossingEvent_pos e N (1/2) D (environmentLaw ν) hN0 hmass)
  have hkl := badCrossing_cond_entropy e N (1/2) D (environmentLaw ν) hN0 hmass
  have hfin : klDiv Q (environmentLaw ν)≠∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  have hpos := C.bad_raw_mass_pos hef N hN hmass
  have hb := actualOccupation_window_kl_le e ν Q hfin
    (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) (C.paddedStages_measurable hef N)
    (C.paddedTimes_stopping hef N) (C.paddedTimes_mono hef N) N m (C.activeCount hef N)
    (C.paddedTimes_active hef N) hpos
  have he := EpisodeChainLedger.operational_raw_mass (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ν Q
  change (actualOccupationRaw e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) N (C.activeCount hef N)).real Set.univ = _ at he
  rw [he] at hb hpos
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hlog : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN0.ne')
  have hkreal : (klDiv Q (environmentLaw ν)).toReal ≤ D*Real.log (N:ℝ) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hkl
    rwa [ENNReal.toReal_ofReal (mul_nonneg hD hlog)] at hh
  obtain ⟨L,hL,hcharge⟩ := C.finite_charge
  have hl := (C.conditional_episode_drops hef hD N hN hlarge hmass L hL hcharge).1
  have hd := mul_le_mul_of_nonneg_left hl hD
  have hbudget : (klDiv Q (environmentLaw ν)).toReal ≤
      C.windowEntropyConstant*(∫ ω, (C.activeCount hef N ω:ℝ) ∂Q) := by
    unfold windowEntropyConstant
    dsimp only [Q]
    nlinarith only [hkreal,hd]
  apply (div_le_iff₀ hpos).mpr
  have hh := mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg m)
  simpa only [activeCount,mul_assoc] using hh

lemma bad_occupation_currentOffsets (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (hN : C.sfloor≤(N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2))) :
    ∀ᵐ Y ∂(C.occupation hef N ((environmentLaw ν)[|badCrossingEvent e N (1/2)]) : Measure (ActualEpisodeArray e)),
      ∀ j, ReferenceClasses.Consistent (currentOffsets e j Y) :=
  actualOccupation_currentOffsets e ν _ (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) (C.paddedStages_measurable hef N) N (C.activeCount hef N)
    (C.bad_raw_mass_pos hef N hN hmass)

theorem bad_limit_window_entropy (C : OperationalConstants ν e f D) (hef : e.1≠f.1) (hD : 0≤D)
    (Ns : ℕ → ℕ)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) (m : ℕ) :
    klDiv (actualCurrentLaw e m ρ : Measure (CurrentWindow e))
      (currentReferenceLaw e ν (actualCurrentLaw e m ρ) : Measure (CurrentWindow e)) ≤
      ENNReal.ofReal ((m:ℝ)*C.windowEntropyConstant) :=
  actualCurrentLaw_kl_weak_limit e ν m _ ρ hlim
    (fun n => C.bad_occupation_currentOffsets hef (Ns n) (hN n) (hmass n))
    ((m:ℝ)*C.windowEntropyConstant) (mul_nonneg (Nat.cast_nonneg m) (C.windowEntropyConstant_nonneg hD))
    (fun n => C.bad_window_kl_le hef hD (Ns n) m (hN n) (hlarge n) (hmass n))

end OperationalConstants
end DirectionalTransience

end

end OAI
