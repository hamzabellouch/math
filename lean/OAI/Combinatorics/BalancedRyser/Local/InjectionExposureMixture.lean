import OAI.Combinatorics.BalancedRyser.Local.InjectionAuxiliaryExposure

namespace OAI

namespace Balanced.InjectionExposure
noncomputable section
open scoped Classical BigOperators
variable {I J Z : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem mem_completions_symm (K : Finset I) (e f : I ↪ J) :
    e ∈ completions K f ↔ f ∈ completions K e := by
  simp only [mem_completions]
  exact ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩

theorem completions_eq_of_mem (K : Finset I) (e f : I ↪ J)
    (h : e ∈ completions K f) : completions K e = completions K f := by
  ext a
  simp only [mem_completions] at h ⊢
  exact ⟨fun ha j hj => (ha j hj).trans (h j hj),
    fun ha j hj => (ha j hj).trans (h j hj).symm⟩

variable [Nonempty (I ↪ J)]

theorem uniform_bind_completions (K : Finset I) :
    (PMF.uniformOfFintype (I ↪ J)).bind
      (fun e => PMF.uniformOfFinset (completions K e) (completions_nonempty K e)) =
        PMF.uniformOfFintype (I ↪ J) := by
  ext f
  rw [PMF.bind_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum]
  suffices hs : (∑ e : I ↪ J,
      PMF.uniformOfFinset (completions K e) (completions_nonempty K e) f) = 1 by
    rw [hs, mul_one]
  have heq : (∑ e : I ↪ J,
      PMF.uniformOfFinset (completions K e) (completions_nonempty K e) f) =
      ∑ e : I ↪ J, if e ∈ completions K f then
        ((completions K f).card : ENNReal)⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro e _
    rw [PMF.uniformOfFinset_apply]
    by_cases h : e ∈ completions K f
    · have hf : f ∈ completions K e := (mem_completions_symm K e f).mp h
      rw [ite_eq_left hf, ite_eq_left h, completions_eq_of_mem K e f h]
    · have hf : f ∉ completions K e := fun hf => h ((mem_completions_symm K f e).mp hf)
      rw [ite_eq_right hf, ite_eq_right h]
  rw [heq]
  have hfilter : Finset.univ.filter (fun e => e ∈ completions K f) = completions K f := by
    ext e
    simp
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel
    (by exact_mod_cast (completions_nonempty K f).card_pos.ne') (by simp)

theorem uniform_bind_auxiliaryLaw (K : Finset I)
    (noise : (I ↪ J) → PMF Z) :
    (PMF.uniformOfFintype (I ↪ J)).bind (fun e => auxiliaryLaw K e noise) =
      (PMF.uniformOfFintype (I ↪ J)).bind
        (fun e => (noise e).map (fun z => (e,z))) := by
  unfold auxiliaryLaw
  rw [← PMF.bind_bind, uniform_bind_completions]

theorem original_probability_eq_auxiliary_average (K : Finset I)
    (noise : (I ↪ J) → PMF Z) (E : Set ((I ↪ J) × Z)) :
    (((PMF.uniformOfFintype (I ↪ J)).bind
      (fun e => (noise e).map (fun z => (e,z)))).toOuterMeasure E).toReal =
      (∑ e : I ↪ J, ((auxiliaryLaw K e noise).toOuterMeasure E).toReal) /
        Fintype.card (I ↪ J) := by
  rw [← uniform_bind_auxiliaryLaw K noise, PMF.toOuterMeasure_bind_apply,
    tsum_fintype, ENNReal.toReal_sum]
  · simp_rw [ENNReal.toReal_mul, PMF.uniformOfFintype_apply,
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [← Finset.mul_sum]
    ring
  · intro e _
    apply ENNReal.mul_ne_top ((PMF.uniformOfFintype (I ↪ J)).apply_ne_top e)
    rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _

theorem original_probability_le_of_auxiliary (K : Finset I)
    (noise : (I ↪ J) → PMF Z) (E : Set ((I ↪ J) × Z)) (B : ℝ)
    (h : ∀ e, ((auxiliaryLaw K e noise).toOuterMeasure E).toReal ≤ B) :
    (((PMF.uniformOfFintype (I ↪ J)).bind
      (fun e => (noise e).map (fun z => (e,z)))).toOuterMeasure E).toReal ≤ B := by
  rw [original_probability_eq_auxiliary_average K noise E]
  have hc : (0 : ℝ) < Fintype.card (I ↪ J) := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hc).mpr
  calc
    _ ≤ ∑ _e : I ↪ J, B := Finset.sum_le_sum (fun e _ => h e)
    _ = B * Fintype.card (I ↪ J) := by simp [mul_comm]

end
end Balanced.InjectionExposure

end OAI
