import OAI.Computability.PerfectCompleteness.Decoding.FixedProjectionErrorLemmas
import OAI.Computability.PerfectCompleteness.Decoding.SourceChildProjectionComparison

namespace OAI

section

namespace PerfectCompleteness.FixedSourceProjectionComparison

open FixedParameters FixedRows RecursiveSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

def projectionFlag (height : Nat) : FiniteDistribution Bool :=
  ProjectionPosterior.bernoulli (projectionProbability p height : ℝ)
    (by exact_mod_cast (projectionProbability_bounds p height).1.le)
    (by exact_mod_cast (projectionProbability_bounds p height).2.le)

variable {v m height : Nat} {C : Type*} [Fintype C]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch p height) → Slots (branch p) height)

abbrev Observation :=
  SourcePhysicalAssemblyLaw.Observation (C := C) (t := sourceLength p.plan hδ)
    (rows p.plan) clauses designated

def mixedLaw [NeZero m] : FiniteDistribution (Observation (C := C) p clauses designated) :=
  (SourceChildKernel.originalLaw (C := C) (t := sourceLength p.plan hδ)
    (rows p.plan) clauses designated (fun _ => projectionFlag p height)).pushforward
      (SourcePhysicalAssemblyLaw.observe (rows p.plan) clauses designated)

def uniformLaw [NeZero m] : FiniteDistribution (Observation (C := C) p clauses designated) :=
  (SourceChildKernel.originalLaw (C := C) (t := sourceLength p.plan hδ)
    (rows p.plan) clauses designated (fun _ => SourceChildNativeLaw.falseFlag)).pushforward
      (SourcePhysicalAssemblyLaw.observe (rows p.plan) clauses designated)

theorem observed_totalVariation_lt [NeZero m] {Γ : Type*} [Fintype Γ]
    (hcalls : Fintype.card C ≤ calls p.plan)
    (observe : Observation (C := C) p clauses designated → Γ) :
    ((mixedLaw p clauses designated).pushforward observe).totalVariation
      ((uniformLaw p clauses designated).pushforward observe) < p.accuracy := by
  have hβ : 0 ≤ (projectionProbability p height : ℝ) := by
    exact_mod_cast (projectionProbability_bounds p height).1.le
  have hβ' : (projectionProbability p height : ℝ) ≤ 1 := by
    exact_mod_cast (projectionProbability_bounds p height).2.le
  have h := SourceChildProjectionComparison.original_observed_variation
    (C := C) (t := sourceLength p.plan hδ) (rows p.plan) clauses designated
    (branch_pos p height) (projectionProbability p height : ℝ) hβ hβ' observe
  have herror := FixedProjectionError.sparse_error_lt p hcalls height
  have hlt := h.trans_lt herror
  simpa only [mixedLaw, uniformLaw, projectionFlag,
    FiniteDistribution.pushforward_comp] using hlt

theorem event_probability_abs_sub_lt [NeZero m] {Γ : Type*} [Fintype Γ]
    (hcalls : Fintype.card C ≤ calls p.plan)
    (observe : Observation (C := C) p clauses designated → Γ) (event : Γ → Bool) :
    |(mixedLaw p clauses designated).probability (fun record => event (observe record)) -
      (uniformLaw p clauses designated).probability (fun record => event (observe record))| <
      p.accuracy := by
  have h := FiniteDistribution.probability_abs_sub_le_totalVariation
    ((mixedLaw p clauses designated).pushforward observe)
    ((uniformLaw p clauses designated).pushforward observe) event
  have hlt := h.trans_lt (observed_totalVariation_lt p clauses designated hcalls observe)
  simpa only [FiniteDistribution.probability_pushforward] using hlt

theorem event_probability_transfer [NeZero m] {Γ : Type*} [Fintype Γ]
    (hcalls : Fintype.card C ≤ calls p.plan)
    (observe : Observation (C := C) p clauses designated → Γ) (event : Γ → Bool) :
    (mixedLaw p clauses designated).probability (fun record => event (observe record)) <
      (uniformLaw p clauses designated).probability (fun record => event (observe record)) +
        p.accuracy := by
  have h := event_probability_abs_sub_lt p clauses designated hcalls observe event
  have hsub := lt_of_le_of_lt (le_abs_self
    ((mixedLaw p clauses designated).probability (fun record => event (observe record)) -
      (uniformLaw p clauses designated).probability (fun record => event (observe record)))) h
  exact (sub_lt_iff_lt_add').mp hsub

end
end PerfectCompleteness.FixedSourceProjectionComparison

end

end OAI
