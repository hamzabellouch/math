import Mathlib.Probability.ProbabilityMassFunction.Constructions
import OAI.Combinatorics.BalancedRyser.Local.InjectionExposure

namespace OAI

namespace Balanced.InjectionExposure

variable {I J Z : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def DependsOnExposed (K : Finset I) (noise : (I ↪ J) → PMF Z) : Prop :=
  ∀ e f, (∀ j ∈ K, e j = f j) → noise e = noise f

noncomputable def auxiliaryLaw (K : Finset I) (base : I ↪ J)
    (noise : (I ↪ J) → PMF Z) : PMF ((I ↪ J) × Z) :=
  (PMF.uniformOfFinset (completions K base) (completions_nonempty K base)).bind
    (fun e => (noise e).map (fun z => (e, z)))

theorem auxiliaryLaw_reveal_last (K : Finset I) (base : I ↪ J)
    (noise : (I ↪ J) → PMF Z) (hnoise : DependsOnExposed K noise) :
    auxiliaryLaw K base noise =
      (noise base).bind (fun z =>
        (PMF.uniformOfFinset (completions K base) (completions_nonempty K base)).map
          (fun e => (e, z))) := by
  classical
  let p := PMF.uniformOfFinset (completions K base) (completions_nonempty K base)
  have hconstant : auxiliaryLaw K base noise =
      p.bind (fun e => (noise base).map (fun z => (e, z))) := by
    ext x
    simp only [auxiliaryLaw, PMF.bind_apply]
    apply tsum_congr
    intro e
    by_cases he : e ∈ completions K base
    · rw [hnoise e base ((mem_completions K base e).mp he)]
    · simp [p, PMF.uniformOfFinset_apply, he]
  rw [hconstant]
  simpa only [PMF.map, Function.comp_def] using
    PMF.bind_comm p (noise base) (fun e z => PMF.pure (e, z))

variable [Fintype Z]

theorem auxiliary_next_event_probability (K : Finset I) (base : I ↪ J)
    (noise : (I ↪ J) → PMF Z) (hnoise : DependsOnExposed K noise)
    (i : I) (hi : i ∉ K) (P : Z → J → Prop) [∀ z, DecidablePred (P z)] :
    ((auxiliaryLaw K base noise).toOuterMeasure {x | P x.2 (x.1 i)}).toReal =
      ∑ z, (noise base z).toReal *
        ((((remaining K base).filter (P z)).card : ℝ) /
          ((remaining K base).card : ℝ)) := by
  classical
  rw [auxiliaryLaw_reveal_last K base noise hnoise,
    PMF.toOuterMeasure_bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro z _
    rw [ENNReal.toReal_mul, PMF.toOuterMeasure_map_apply]
    change (noise base z).toReal *
      ((PMF.uniformOfFinset (completions K base) (completions_nonempty K base)).toOuterMeasure
        {e | P z (e i)}).toReal = _
    rw [next_event_probability K base i hi (P z)]
  · intro z _
    apply ENNReal.mul_ne_top ((noise base).apply_ne_top z)
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _

theorem auxiliary_next_event_probability_le (K : Finset I) (base : I ↪ J)
    (noise : (I ↪ J) → PMF Z) (hnoise : DependsOnExposed K noise)
    (i : I) (hi : i ∉ K) (P : Z → J → Prop) [∀ z, DecidablePred (P z)]
    (hP : ∀ z, ((remaining K base).filter (P z)).card ≤ 1) :
    ((auxiliaryLaw K base noise).toOuterMeasure {x | P x.2 (x.1 i)}).toReal ≤
      1 / ((remaining K base).card : ℝ) := by
  rw [auxiliary_next_event_probability K base noise hnoise i hi P]
  have hsum : ∑ z, (noise base z).toReal = 1 := by
    have hs : (∑ z : Z, noise base z) = 1 := by
      simpa only [tsum_fintype] using (noise base).tsum_coe
    rw [← ENNReal.toReal_sum (fun z _ => (noise base).apply_ne_top z), hs]
    simp
  calc
    (∑ z, (noise base z).toReal *
        ((((remaining K base).filter (P z)).card : ℝ) /
          ((remaining K base).card : ℝ))) ≤
        ∑ z, (noise base z).toReal * (1 / ((remaining K base).card : ℝ)) := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact div_le_div_of_nonneg_right (by exact_mod_cast hP z) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

end Balanced.InjectionExposure

end OAI
