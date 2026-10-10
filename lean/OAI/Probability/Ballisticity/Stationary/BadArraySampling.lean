import Mathlib
import OAI.Probability.Ballisticity.Stationary.BadCrossingEpisodes
import OAI.Probability.Ballisticity.Estimates.BadOccupationLimit

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma bad_raw_mass_pos (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (hN : C.sfloor ≤ (N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2))) :
    0<(actualOccupationRaw e ν ((environmentLaw ν)[|badCrossingEvent e N (1/2)])
      (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N)
      N (C.activeCount hef N)).real Set.univ := by
  have hN0 : 0<N := by exact_mod_cast lt_of_lt_of_le zero_lt_one (C.hs.trans hN)
  have : IsProbabilityMeasure ((environmentLaw ν)[|badCrossingEvent e N (1/2)]) :=
    cond_isProbabilityMeasure (badCrossingEvent_pos e N (1/2) D (environmentLaw ν) hN0 hmass)
  have hpos := EpisodeChainLedger.operational_mass_positive (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N
    ((environmentLaw ν)[|badCrossingEvent e N (1/2)]) hN0
  have he := EpisodeChainLedger.operational_raw_mass (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ν
    ((environmentLaw ν)[|badCrossingEvent e N (1/2)])
  exact hpos.trans_eq he.symm

theorem bad_array_sampling_limit (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2))) :
    ∃ ρ : ProbabilityMeasure (ActualEpisodeArray e), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun n => C.occupation hef (Ns (φ n))
        ((environmentLaw ν)[|badCrossingEvent e (Ns (φ n)) (1/2)])) atTop (𝓝 ρ) ∧
      MeasurePreserving StationaryCompact.shift (ρ : Measure (ActualEpisodeArray e))
        (ρ : Measure (ActualEpisodeArray e)) ∧
      (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ∀ p j z,
        Tendsto (fun n => arraySamplingError e p j z (2^n) Y) atTop (𝓝 0)) ∧
      (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ∀ p q z, p≠q →
        arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0) := by
  obtain ⟨ρ,φ,hφ,hlim,hstat⟩ := C.bad_occupation_stationary_limit hef hD Ns hNs hN hlarge hmass
  refine ⟨ρ,φ,hφ,hlim,hstat,?_,?_⟩
  · apply ae_all_iff.mpr
    intro p
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro z
    exact actualOccupation_limit_sampling e ν
      (fun n => (environmentLaw ν)[|badCrossingEvent e (Ns (φ n)) (1/2)])
      (fun n => C.paddedTimes hef (Ns (φ n))) (fun n => C.paddedStages hef (Ns (φ n)))
      (fun n => C.paddedTimes_measurable hef (Ns (φ n)))
      (fun n => C.paddedStages_measurable hef (Ns (φ n)))
      (fun n => Ns (φ n)) (fun n => C.activeCount hef (Ns (φ n)))
      (fun n => C.activeCount_measurable hef (Ns (φ n)))
      (fun n => C.bad_raw_mass_pos hef (Ns (φ n)) (hN (φ n)) (hmass (φ n))) ρ hlim p j z
  · apply ae_all_iff.mpr
    intro p
    apply ae_all_iff.mpr
    intro q
    apply ae_all_iff.mpr
    intro z
    by_cases hpq : p=q
    · exact Filter.Eventually.of_forall (fun _ h => (h hpq).elim)
    · exact (actualOccupation_limit_zero e ν
        (fun n => (environmentLaw ν)[|badCrossingEvent e (Ns (φ n)) (1/2)])
        (fun n => C.paddedTimes hef (Ns (φ n))) (fun n => C.paddedStages hef (Ns (φ n)))
        (fun n => C.paddedTimes_measurable hef (Ns (φ n)))
        (fun n => C.paddedStages_measurable hef (Ns (φ n)))
        (fun n => Ns (φ n)) (fun n => C.activeCount hef (Ns (φ n)))
        (fun n => C.activeCount_measurable hef (Ns (φ n)))
        (fun n => C.bad_raw_mass_pos hef (Ns (φ n)) (hN (φ n)) (hmass (φ n))) ρ hlim p q hpq z).mono
        (fun _ h _ => h)

end OperationalConstants
end DirectionalTransience

end

end OAI
