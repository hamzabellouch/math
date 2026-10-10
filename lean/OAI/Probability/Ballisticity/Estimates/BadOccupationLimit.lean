import Mathlib
import OAI.Probability.Ballisticity.Stationary.BadCrossingEpisodes

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

noncomputable def paddedTimes (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) : Environment d → ℤ → ℕ :=
  EpisodeChainLedger.arrayTime (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N

noncomputable def paddedStages (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) : Environment d → ℤ → ℕ :=
  EpisodeChainLedger.arrayStages (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N

omit [IsProbabilityMeasure ν] in
lemma paddedTimes_measurable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (i : ℤ) : Measurable (fun ω => C.paddedTimes hef N ω i) :=
  EpisodeChainLedger.arrayTime_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N i

omit [IsProbabilityMeasure ν] in
lemma paddedStages_measurable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (i : ℤ) : Measurable (fun ω => C.paddedStages hef N ω i) :=
  EpisodeChainLedger.arrayStages_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N i

omit [IsProbabilityMeasure ν] in
lemma activeCount_measurable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) : Measurable (C.activeCount hef N) :=
  EpisodeChainLedger.number_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N N

omit [IsProbabilityMeasure ν] in
lemma activeCount_le (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (ω : Environment d) : C.activeCount hef N ω ≤ N :=
  EpisodeChainLedger.number_le (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω N

noncomputable def occupation (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (Q : Measure (Environment d)) [IsFiniteMeasure Q] : ProbabilityMeasure (ActualEpisodeArray e) :=
  actualOccupation e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) N (C.activeCount hef N)

lemma bad_counts_tendsto (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2))) :
    Tendsto (fun n => ∫ ω, (C.activeCount hef (Ns n) ω:ℝ)
      ∂(environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)]) atTop atTop := by
  have hlog : Tendsto (fun n => Real.log (Ns n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hNs)
  obtain ⟨L,hL,hcharge⟩ := C.finite_charge
  apply tendsto_atTop.2
  intro R
  filter_upwards [hlog.eventually (eventually_ge_atTop ((8/3:ℝ)*(C.injectionCost+1)*R))] with n hn
  have hl := (C.conditional_episode_drops hef hD (Ns n) (hN n) (hlarge n) (hmass n) L hL hcharge).1
  have hm : 0 ≤ ∫ ω, (C.activeCount hef (Ns n) ω:ℝ)
      ∂(environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)] :=
    integral_nonneg (fun _ => Nat.cast_nonneg _)
  have hA := C.cost_nonneg
  have hx : (C.injectionCost+1)*R ≤ (C.injectionCost+1)*(∫ ω, (C.activeCount hef (Ns n) ω:ℝ)
      ∂(environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)]) := by nlinarith only [hn,hl,hm]
  exact (mul_le_mul_iff_right₀ (show 0<C.injectionCost+1 by positivity)).mp hx

theorem bad_occupation_stationary_limit (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2))) :
    ∃ ρ : ProbabilityMeasure (ActualEpisodeArray e), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun n => C.occupation hef (Ns (φ n))
        ((environmentLaw ν)[|badCrossingEvent e (Ns (φ n)) (1/2)])) atTop (𝓝 ρ) ∧
      MeasurePreserving StationaryCompact.shift (ρ : Measure (ActualEpisodeArray e))
        (ρ : Measure (ActualEpisodeArray e)) := by
  let Q := fun n => (environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)]
  have hN0 (n) : 0<Ns n := by exact_mod_cast lt_of_lt_of_le zero_lt_one (C.hs.trans (hN n))
  have (n : ℕ) : IsProbabilityMeasure (Q n) :=
    cond_isProbabilityMeasure (badCrossingEvent_pos e (Ns n) (1/2) D (environmentLaw ν) (hN0 n) (hmass n))
  let t := fun n => C.paddedTimes hef (Ns n)
  let J := fun n => C.paddedStages hef (Ns n)
  let μs := fun n => episodeInputLaw e ν (Q n) (t n) (C.paddedTimes_measurable hef (Ns n))
  let As := fun n => actualArrayMap e (t n) (J n)
  let Ms := fun n (X : EpisodeInput e) => C.activeCount hef (Ns n) X.1.1
  have hMs (n) : Measurable (Ms n) := (C.activeCount_measurable hef (Ns n)).comp (measurable_fst.comp measurable_fst)
  have hAs (n) : Measurable (As n) := actualArrayMap_measurable e (t n) (J n)
    (C.paddedTimes_measurable hef (Ns n)) (C.paddedStages_measurable hef (Ns n))
  have hmass_eq (n) : (∫ X, (Ms n X:ℝ) ∂μs n)=(∫ ω, (C.activeCount hef (Ns n) ω:ℝ) ∂Q n) :=
    episodeInputLaw_env_integral e ν (Q n) (t n) (C.paddedTimes_measurable hef (Ns n)) _
      ((measurable_of_countable (fun m : ℕ => (m:ℝ))).comp (C.activeCount_measurable hef (Ns n)))
  have hpos (n) : 0<∫ X, (Ms n X:ℝ) ∂μs n := by
    rw [hmass_eq]
    exact EpisodeChainLedger.operational_mass_positive (k:=C.k) e f hef (episodeScaleRadius ν e f)
      C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg (Ns n) (Q n) (hN0 n)
  have hcount : Tendsto (fun n => ∫ X, (Ms n X:ℝ) ∂μs n) atTop atTop := by
    simp only [hmass_eq]
    exact C.bad_counts_tendsto hef hD Ns hNs hN hlarge hmass
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  obtain ⟨ρ,φ,hφ,hlim,hstat⟩ := StationaryCompact.episodeOccupation_stationary_limit Ns μs As hAs
    Ms hMs (fun n X => C.activeCount_le hef (Ns n) X.1.1) hpos hcount
    StationaryCompact.shift StationaryCompact.shift_continuous
  refine ⟨ρ,φ,hφ,?_,hstat⟩
  exact hlim

end OperationalConstants
end DirectionalTransience

end

end OAI
