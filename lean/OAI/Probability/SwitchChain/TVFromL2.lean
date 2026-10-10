import OAI.Probability.SwitchChain.Definitions
import OAI.Probability.SwitchChain.InitialTV

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315Aux

theorem half_sum_abs_le_sqrt_card_mul_sqrt_sum_sq
    {α : Type*} [Fintype α] (f : α → ℝ) :
    (1 / 2 : ℝ) * ∑ x : α, |f x| ≤
      Real.sqrt (Fintype.card α : ℝ) / 2 * Real.sqrt (∑ x : α, (f x) ^ 2) := by
  classical
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun _ : α => (1 : ℝ)) (fun x => |f x|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, sq_abs] at h
  nlinarith

theorem half_sum_abs_le_of_sum_sq_le_exp
    {α : Type*} [Fintype α] (f : α → ℝ) (a : ℝ)
    (h : (∑ x : α, (f x) ^ 2) ≤ Real.exp (-2 * a)) :
    (1 / 2 : ℝ) * ∑ x : α, |f x| ≤
      Real.sqrt (Fintype.card α : ℝ) / 2 * Real.exp (-a) := by
  have he : Real.exp (-2 * a) = (Real.exp (-a)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsqrt : Real.sqrt (∑ x : α, (f x) ^ 2) ≤ Real.exp (-a) :=
    Real.sqrt_le_iff.mpr ⟨Real.exp_nonneg _, h.trans_eq he⟩
  exact (half_sum_abs_le_sqrt_card_mul_sqrt_sum_sq f).trans
    (mul_le_mul_of_nonneg_left hsqrt (by positivity))

theorem l2_exponential_of_step (a : Nat → ℝ) (γ : ℝ)
    (hzero : a 0 ≤ 1)
    (hstep : ∀ t : Nat, a (t + 1) ≤ Real.exp (-2 * γ) * a t) :
    ∀ t : Nat, a t ≤ Real.exp (-2 * γ * (t : ℝ)) := by
  intro t
  induction t with
  | zero => simpa using hzero
  | succ t ih =>
    calc
      a (t + 1) ≤ Real.exp (-2 * γ) * a t := hstep t
      _ ≤ Real.exp (-2 * γ) * Real.exp (-2 * γ * (t : ℝ)) :=
        mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
      _ = Real.exp (-2 * γ * ((t + 1 : Nat) : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

end Problem315Aux

namespace Problem315

theorem tvDistanceFrom_le_of_l2_exponential
    (n : Nat) (d : Fin n → Nat) (t : Nat) (G : GraphState n d)
    (hL2 : (∑ H ∈ allGraphStates n d,
      (kernelPow n d t G H - (1 : ℝ) / (stateCount n d : ℝ)) ^ 2) ≤
      Real.exp (-2 * ((t : ℝ) /
        (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))))) :
    tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 *
      Real.exp (-(t : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  classical
  have h := Problem315Aux.half_sum_abs_le_of_sum_sq_le_exp
    (fun H => kernelPow n d t G H - (1 : ℝ) / (stateCount n d : ℝ))
    ((t : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)))
    (by simpa [allGraphStates] using hL2)
  simpa [tvDistanceFrom, stateCount, allGraphStates, neg_div] using h

theorem kernelPow_initial_l2_eq (n : Nat) (d : Fin n → Nat) (G : GraphState n d) :
    (∑ H ∈ allGraphStates n d,
      (kernelPow n d 0 G H - (1 : ℝ) / (stateCount n d : ℝ)) ^ 2) =
      1 - (1 : ℝ) / (stateCount n d : ℝ) := by
  classical
  simpa [kernelPow, stateCount, allGraphStates] using
    Problem315Aux.sum_sq_delta_uniform_eq G

theorem tvDistanceFrom_bound_of_l2_step
    (n : Nat) (d : Fin n → Nat) (γ : ℝ)
    (hstep : ∀ (t : Nat) (G : GraphState n d),
      (∑ H ∈ allGraphStates n d,
        (kernelPow n d (t + 1) G H - (1 : ℝ) / (stateCount n d : ℝ)) ^ 2) ≤
      Real.exp (-2 * γ) * (∑ H ∈ allGraphStates n d,
        (kernelPow n d t G H - (1 : ℝ) / (stateCount n d : ℝ)) ^ 2))
    (t : Nat) (G : GraphState n d) :
    tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 *
      Real.exp (-γ * (t : ℝ)) := by
  classical
  have hzero : (∑ H ∈ allGraphStates n d,
      (kernelPow n d 0 G H - (1 : ℝ) / (stateCount n d : ℝ)) ^ 2) ≤ 1 := by
    rw [kernelPow_initial_l2_eq]
    have hinv : (0 : ℝ) ≤ 1 / (stateCount n d : ℝ) := by positivity
    linarith
  have hL2 := Problem315Aux.l2_exponential_of_step
    (fun k => ∑ H ∈ allGraphStates n d,
      (kernelPow n d k G H - (1 : ℝ) / (stateCount n d : ℝ)) ^ 2)
    γ hzero (fun k => hstep k G) t
  have h := Problem315Aux.half_sum_abs_le_of_sum_sq_le_exp
    (fun H => kernelPow n d t G H - (1 : ℝ) / (stateCount n d : ℝ))
    (γ * (t : ℝ)) (by simpa [allGraphStates, mul_assoc] using hL2)
  simpa [tvDistanceFrom, stateCount, allGraphStates, neg_mul] using h

end Problem315

end

end OAI
