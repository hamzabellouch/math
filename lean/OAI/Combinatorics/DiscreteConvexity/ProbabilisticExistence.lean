import OAI.Combinatorics.DiscreteConvexity.FiniteProbability

namespace OAI

/-!
# Extracting outcomes from a finite probability law

Normalization guarantees a positive-weight outcome. It also guarantees an
outcome below the expectation and a witness to every positive-probability
event; strict positivity of every individual mass is not required.
-/

namespace TalagrandDiscreteConvexity.FiniteLaw

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem exists_weight_pos (μ : FiniteLaw Ω) : ∃ ω, 0 < μ.weight ω := by
  classical
  by_contra h
  have hz (ω : Ω) : μ.weight ω = 0 :=
    le_antisymm (le_of_not_gt (fun hp => h ⟨ω, hp⟩)) (μ.nonneg ω)
  have htotal : (∑ ω, μ.weight ω) = 0 := by simp [hz]
  rw [μ.total] at htotal
  exact one_ne_zero htotal

theorem exists_le_expectation (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    ∃ ω, f ω ≤ μ.expectation f := by
  classical
  obtain ⟨ω₀, hω₀⟩ := μ.exists_weight_pos
  by_contra h
  have hlt (ω : Ω) : μ.expectation f < f ω :=
    lt_of_not_ge (fun hle => h ⟨ω, hle⟩)
  have hsum : μ.expectation (fun _ => μ.expectation f) < μ.expectation f := by
    apply Finset.sum_lt_sum
    · intro ω _
      exact mul_le_mul_of_nonneg_left (hlt ω).le (μ.nonneg ω)
    · exact ⟨ω₀, Finset.mem_univ ω₀,
        mul_lt_mul_of_pos_left (hlt ω₀) hω₀⟩
  rw [expectation_const] at hsum
  exact (lt_irrefl _) hsum

theorem exists_of_prob_pos (μ : FiniteLaw Ω) {P : Ω → Prop}
    (hP : 0 < μ.prob P) : ∃ ω, P ω := by
  classical
  by_contra h
  have hz : μ.prob P = 0 := by
    unfold prob
    apply Finset.sum_eq_zero
    intro ω _
    exact ite_eq_right (fun hp => h ⟨ω, hp⟩)
  exact (ne_of_gt hP) hz

end TalagrandDiscreteConvexity.FiniteLaw

end OAI
