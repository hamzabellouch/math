import OAI.Probability.SwitchChain.Definitions
import OAI.Probability.SwitchChain.SwitchFoundations
import OAI.Probability.SwitchChain.TVFromL2

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TVBridge

variable {n : ℕ} {d : Fin n → ℕ}

theorem kernelPow_row_sum
    (hrow : ∀ G : GraphState n d, ∑ H ∈ allGraphStates n d, switchKernel n d G H = 1)
    (t : ℕ) (G : GraphState n d) : ∑ H ∈ allGraphStates n d, kernelPow n d t G H = 1 := by
  classical
  simp only [allGraphStates] at hrow ⊢
  induction t with
  | zero => simp [kernelPow]
  | succ t ih =>
    simp only [kernelPow, allGraphStates]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hrow, mul_one]
    exact ih

theorem centered_row_sum
    (hrow : ∀ G : GraphState n d, ∑ H ∈ allGraphStates n d, switchKernel n d G H = 1)
    (t : ℕ) (G : GraphState n d) :
    ∑ H ∈ allGraphStates n d, (kernelPow n d t G H - (1 : ℝ) / stateCount n d) = 0 := by
  classical
  have hc : (stateCount n d : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card (GraphState n d) := Fintype.card_pos_iff.mpr ⟨G⟩
    exact_mod_cast (show stateCount n d ≠ 0 by simpa [stateCount, allGraphStates] using Nat.ne_of_gt h)
  rw [Finset.sum_sub_distrib, kernelPow_row_sum hrow]
  simp only [Finset.sum_const, nsmul_eq_mul]
  change 1 - (stateCount n d : ℝ) * (1 / (stateCount n d : ℝ)) = 0
  field_simp
  norm_num

theorem centered_row_evolution
    (hrow : ∀ G : GraphState n d,
      ∑ H ∈ allGraphStates n d, switchKernel n d G H = 1)
    (t : ℕ) (G H : GraphState n d) :
    kernelPow n d (t + 1) G H - (1 : ℝ) / stateCount n d =
      markovApply n d
        (fun K => kernelPow n d t G K - (1 : ℝ) / stateCount n d) H := by
  classical
  unfold markovApply
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hrow H, one_mul]
  congr 1
  change (∑ K ∈ allGraphStates n d, kernelPow n d t G K * switchKernel n d K H) = _
  apply Finset.sum_congr rfl
  intro K hK
  rw [switchKernel_symm H K, mul_comm]

theorem l2_step_of_centered_contraction
    (hrow : ∀ G : GraphState n d,
      ∑ H ∈ allGraphStates n d, switchKernel n d G H = 1)
    (γ : ℝ)
    (hcontract : ∀ f : GraphState n d → ℝ,
      (∑ G ∈ allGraphStates n d, f G) = 0 →
      (∑ G ∈ allGraphStates n d, (markovApply n d f G) ^ 2) ≤
        Real.exp (-2 * γ) * (∑ G ∈ allGraphStates n d, (f G) ^ 2))
    (t : ℕ) (G : GraphState n d) :
    (∑ H ∈ allGraphStates n d,
      (kernelPow n d (t + 1) G H - (1 : ℝ) / stateCount n d) ^ 2) ≤
      Real.exp (-2 * γ) * (∑ H ∈ allGraphStates n d,
        (kernelPow n d t G H - (1 : ℝ) / stateCount n d) ^ 2) := by
  have h := hcontract
    (fun H => kernelPow n d t G H - (1 : ℝ) / stateCount n d)
    (centered_row_sum hrow t G)
  simpa only [← centered_row_evolution hrow t G] using h

theorem tv_bound_of_centered_contraction
    (hrow : ∀ G : GraphState n d,
      ∑ H ∈ allGraphStates n d, switchKernel n d G H = 1)
    (γ : ℝ)
    (hcontract : ∀ f : GraphState n d → ℝ,
      (∑ G ∈ allGraphStates n d, f G) = 0 →
      (∑ G ∈ allGraphStates n d, (markovApply n d f G) ^ 2) ≤
        Real.exp (-2 * γ) * (∑ G ∈ allGraphStates n d, (f G) ^ 2))
    (t : ℕ) (G : GraphState n d) :
    tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 *
      Real.exp (-γ * (t : ℝ)) := by
  exact tvDistanceFrom_bound_of_l2_step n d γ
    (l2_step_of_centered_contraction hrow γ hcontract) t G

end Problem315.TVBridge

end

end OAI
