import Mathlib
import OAI.Probability.Ballisticity.Stationary.StationaryWindowEntropy

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma row_law_lower_bound (C : OperationalConstants ν e f D) :
    ∀ᵐ r ∂ν, ∀ u, C.κ ≤ r.1 u := by
  have hp : ∀ᵐ ω ∂environmentLaw ν, ∀ u, C.κ ≤ (ω 0).1 u :=
    C.rows.mono fun ω hω => hω 0
  have hm : MeasurableSet {r : Row d | ∀ u, C.κ ≤ r.1 u} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun u => measurableSet_le measurable_const
      ((measurable_pi_apply u).comp measurable_subtype_coe)
  have hmp := measurePreserving_eval_infinitePi (fun _ : Lattice d => ν) 0
  have hh := (ae_map_iff hmp.measurable.aemeasurable hm).mpr hp
  simpa only [environmentLaw,hmp.map_eq] using hh

lemma bad_limit_elliptic (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (Ns : ℕ → ℕ) (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    ∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ArrayElliptic e C.κ Y := by
  apply closed_support_weak_limit _ ρ hlim _ (arrayElliptic_closed e C.κ)
  intro n
  exact actualOccupation_elliptic e ν _
    (C.paddedTimes hef (Ns n)) (C.paddedStages hef (Ns n))
    (C.paddedTimes_measurable hef (Ns n)) (C.paddedStages_measurable hef (Ns n)) (Ns n)
    (C.activeCount hef (Ns n)) (C.bad_raw_mass_pos hef (Ns n) (hN n) (hmass n))
    C.κ C.row_law_lower_bound
    ((cond_absolutelyContinuous (μ:=environmentLaw ν)
      (s:=badCrossingEvent e (Ns n) (1/2))).ae_le C.rows)

end OperationalConstants
end DirectionalTransience

end

end OAI
