import OAI.Combinatorics.BalancedRyser.Local.InjectionExposure
import OAI.Combinatorics.BalancedRyser.Probability.FiniteUniformConditioning

namespace OAI

namespace Balanced.InjectionExposure

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Nonempty (I ↪ J)]

theorem original_uniform_conditioned (K : Finset I) (base : I ↪ J)
    (h : ∃ e ∈ (↑(completions K base) : Set (I ↪ J)),
      e ∈ (PMF.uniformOfFintype (I ↪ J)).support) :
    (PMF.uniformOfFintype (I ↪ J)).filter (↑(completions K base)) h =
      PMF.uniformOfFinset (completions K base) (completions_nonempty K base) := by
  classical
  let S := completions K base
  have : Nonempty (↑S : Set (I ↪ J)) := ⟨⟨base, by simp [S]⟩⟩
  rw [uniform_filter_eq_subtype_map]
  ext e
  by_cases he : e ∈ completions K base
  · rw [PMF.map_apply, tsum_eq_single (⟨e, he⟩ : (↑S : Set (I ↪ J)))]
    · simp only [PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply,
        he, ite_true]
      exact congrArg (fun n : ℕ => (n : ENNReal)⁻¹)
        (Fintype.card_coe (completions K base))
    · intro f hf
      rw [ite_eq_right]
      intro hef
      exact hf (Subtype.ext hef.symm)
  · rw [PMF.uniformOfFinset_apply_of_notMem (completions_nonempty K base) he,
      PMF.map_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro f
    rw [ite_eq_right]
    intro hef
    exact he (hef ▸ f.property)

theorem original_conditioned_next_event (K : Finset I) (base : I ↪ J)
    (h : ∃ e ∈ (↑(completions K base) : Set (I ↪ J)),
      e ∈ (PMF.uniformOfFintype (I ↪ J)).support)
    (i : I) (hi : i ∉ K) (P : J → Prop) [DecidablePred P] :
    (((PMF.uniformOfFintype (I ↪ J)).filter (↑(completions K base)) h).toOuterMeasure
      {e | P (e i)}).toReal =
        (((remaining K base).filter P).card : ℝ) / ((remaining K base).card : ℝ) := by
  rw [original_uniform_conditioned K base h]
  exact next_event_probability K base i hi P

end Balanced.InjectionExposure

end OAI
