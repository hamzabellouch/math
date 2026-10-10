import OAI.Analysis.MarkovType.FiniteMartingaleConditional
import OAI.Analysis.MarkovType.FiniteFirstCrossing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [Fintype Ω]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : FinitePartitionFiltration Ω} {μ : FiniteLaw Ω}
variable {M : ℕ → Ω → E} {N : ℕ} {t : ℝ}

theorem finite_martingale_maximal_sq (hM : F.IsMartingaleUpTo μ M N) (ht : 0 < t) :
    t ^ (2 : ℕ) * μ.prob (fun ω => ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖) ≤
      μ.expect (fun ω => ‖M N ω‖ ^ (2 : ℕ)) := by
  classical
  let τ := FinitePartitionFiltration.firstCrossing M N t
  have hτ : F.IsStoppingTime τ := F.isStoppingTime_firstCrossing M N t hM.1
  have hτN : ∀ ω, τ ω ≤ N := FinitePartitionFiltration.firstCrossing_le M N t
  calc
    t ^ (2 : ℕ) * μ.prob (fun ω => ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖) =
        μ.expect (fun ω => if ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖
          then t ^ (2 : ℕ) else 0) := by
      unfold FiniteLaw.prob FiniteLaw.expect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖ <;> simp [h, mul_comm]
    _ ≤ μ.expect (fun ω => ‖M (τ ω) ω‖ ^ (2 : ℕ)) := by
      apply μ.expect_mono
      intro ω
      by_cases h : ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖
      · rw [ite_eq_left h]
        have hc : t < ‖M (τ ω) ω‖ :=
          FinitePartitionFiltration.firstCrossing_spec M N t ω h
        nlinarith only [hc, ht, norm_nonneg (M (τ ω) ω)]
      · rw [ite_eq_right h]
        exact sq_nonneg _
    _ ≤ _ := hM.expect_stopped_norm_sq_le hτ hτN

theorem finite_martingale_maximal_sq_le_l2 (hM : F.IsMartingaleUpTo μ M N)
    (ht : 0 < t) :
    t ^ (2 : ℕ) * μ.prob (fun ω => ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖) ≤
      finiteL2Norm μ (M N) ^ (2 : ℕ) := by
  rw [finiteL2Norm_sq]
  exact finite_martingale_maximal_sq hM ht

end MarkovSuperreflexivity

end

end OAI
