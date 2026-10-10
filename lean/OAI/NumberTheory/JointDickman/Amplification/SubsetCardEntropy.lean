import OAI.NumberTheory.JointDickman.Amplification.SubsetCountBounds

namespace OAI

/-! # Entropy bound for subsets of a prescribed size -/

namespace JointDickman
open Finset Classical

theorem subset_exact_count_exp_bound (P : Finset ℕ) (k : ℕ) (t : ℝ) :
    ((P.powerset.filter (fun A => A.card = k)).card : ℝ) ≤
      Real.exp (t*k)*(1+Real.exp (-t))^P.card := by
  let I := P.powerset.filter (fun A => A.card = k)
  have he : (I.card : ℝ)*Real.exp (-t*k) ≤ (1+Real.exp (-t))^P.card := by
    calc
      _ = ∑ _A ∈ I, Real.exp (-t*k) := by simp
      _ = ∑ A ∈ I, Real.exp (-t*(A.card : ℝ)) := by
        apply sum_congr rfl
        intro A hA
        rw [(mem_filter.mp hA).2]
      _ ≤ ∑ A ∈ P.powerset, Real.exp (-t*(A.card : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ = _ := subset_count_exp_sum P t
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (t*k)).le
  have hc : Real.exp (t*k)*Real.exp (-t*k) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [mul_left_comm (Real.exp (t*k)) (I.card : ℝ),hc,mul_one] at hm
  exact hm

/-- No rounding loss occurs for an exact cardinality. -/
theorem subset_exact_count_entropy (P : Finset ℕ) {k : ℕ} (hk : k ≤ P.card) :
    ((P.powerset.filter (fun A => A.card = k)).card : ℝ) ≤
      Real.exp ((P.card : ℝ)*Real.binEntropy ((k : ℝ)/P.card)) := by
  by_cases hk0 : k = 0
  · subst k
    have hf : P.powerset.filter (fun A => A.card = 0) = {∅} := by
      ext A
      simp only [mem_filter,mem_powerset,card_eq_zero,mem_singleton]
      exact ⟨fun h => h.2,fun h => ⟨by rw [h]; exact empty_subset _,h⟩⟩
    rw [hf]
    simp
  by_cases hkn : k = P.card
  · subst k
    have hf : P.powerset.filter (fun A => A.card = P.card) = {P} := by
      ext A
      simp only [mem_filter,mem_powerset,mem_singleton]
      exact ⟨fun h => eq_of_subset_of_card_le h.1 h.2.ge,fun h => by subst A; simp⟩
    have hn : (P.card : ℝ) ≠ 0 := by exact_mod_cast hk0
    simp [hf,hn]
  have hn : 0 < P.card := lt_of_lt_of_le (Nat.pos_of_ne_zero hk0) hk
  have hnr : (0 : ℝ) < P.card := by exact_mod_cast hn
  have hkr : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
  have hlt : (k : ℝ) < P.card := by exact_mod_cast lt_of_le_of_ne hk hkn
  let θ : ℝ := (k : ℝ)/P.card
  have hθ : 0 < θ := div_pos hkr hnr
  have hθ1 : θ < 1 := (div_lt_one hnr).mpr hlt
  let t := Real.log (1-θ)-Real.log θ
  have he : Real.exp (-t) = θ/(1-θ) := by
    dsimp [t]
    rw [neg_sub,Real.exp_sub,Real.exp_log hθ,Real.exp_log (by linarith)]
  have hb : 1+Real.exp (-t) = (1-θ)⁻¹ := by
    rw [he]
    field_simp [ne_of_gt (show 0 < 1-θ by linarith)]
    ring
  have hlog : Real.log (1+Real.exp (-t)) = -Real.log (1-θ) := by rw [hb,Real.log_inv]
  have hp : (1+Real.exp (-t))^P.card =
      Real.exp ((P.card : ℝ)*Real.log (1+Real.exp (-t))) := by
    rw [Real.exp_nat_mul,Real.exp_log (by positivity)]
  refine (subset_exact_count_exp_bound P k t).trans_eq ?_
  rw [hp,← Real.exp_add,hlog]
  congr 1
  have hθn : θ*(P.card : ℝ) = k := div_mul_cancel₀ _ hnr.ne'
  change _ = (P.card : ℝ)*Real.binEntropy θ
  simp only [Real.binEntropy,Real.log_inv,t]
  rw [← hθn]
  ring

end JointDickman

end OAI
