import OAI.NumberTheory.JointDickman.Counting.DiscreteShortEnergy

namespace OAI

/-! # Short translations of a finite convolution with small coefficient variation -/
namespace JointDickman
open Finset Classical

noncomputable def finiteConvolution (K : ℕ → ℝ) (g : ℕ → ℂ) (N v : ℕ) : ℂ :=
  ∑ j ∈ range N, (K j : ℂ)*g (v+j)

noncomputable def finiteCoefficientVariation (K : ℕ → ℝ) (N : ℕ) : ℝ :=
  |K 0|+|K N|+∑ j ∈ range N, |K j-K (j+1)|

theorem finiteConvolution_step (K : ℕ → ℝ) (g : ℕ → ℂ) (N v : ℕ) :
    finiteConvolution K g (N+1) (v+1)-finiteConvolution K g (N+1) v =
      (K N : ℂ)*g (v+N+1)-(K 0 : ℂ)*g v+
        ∑ j ∈ range N, ((K j-K (j+1) : ℝ) : ℂ)*g (v+j+1) := by
  have h₁ : finiteConvolution K g (N+1) (v+1) =
      (∑ j ∈ range N, (K j : ℂ)*g (v+j+1))+(K N : ℂ)*g (v+N+1) := by
    simp [finiteConvolution,sum_range_succ,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  have h₂ : finiteConvolution K g (N+1) v =
      (∑ j ∈ range N, (K (j+1) : ℂ)*g (v+j+1))+(K 0 : ℂ)*g v := by
    rw [finiteConvolution,sum_range_succ']
    simp only [Nat.add_assoc,add_zero]
  rw [h₁,h₂]
  simp only [Complex.ofReal_sub,sub_mul,sum_sub_distrib]
  ring

theorem finiteConvolution_step_bound (K : ℕ → ℝ) (g : ℕ → ℂ) (N v : ℕ)
    {G : ℝ} (hG : ∀ n, ‖g n‖ ≤ G) :
    ‖finiteConvolution K g (N+1) (v+1)-finiteConvolution K g (N+1) v‖ ≤
      G*finiteCoefficientVariation K N := by
  rw [finiteConvolution_step]
  have hb (a : ℝ) (n : ℕ) : ‖(a : ℂ)*g n‖ ≤ |a| *G := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hG n) (abs_nonneg a)
  calc
    _ ≤ ‖(K N : ℂ)*g (v+N+1)-(K 0 : ℂ)*g v‖+
        ‖∑ j ∈ range N, ((K j-K (j+1) : ℝ) : ℂ)*g (v+j+1)‖ := norm_add_le _ _
    _ ≤ (|K N| *G+|K 0| *G)+∑ j ∈ range N, |K j-K (j+1)| *G := by
      apply add_le_add
      · exact (norm_sub_le _ _).trans (add_le_add (hb _ _) (hb _ _))
      · exact (norm_sum_le _ _).trans (sum_le_sum (fun j _ => hb _ _))
    _ = _ := by rw [← sum_mul]; unfold finiteCoefficientVariation; ring

theorem finiteConvolution_shift_bound (K : ℕ → ℝ) (g : ℕ → ℂ) (N v h : ℕ)
    {G : ℝ} (hG : ∀ n, ‖g n‖ ≤ G) :
    ‖finiteConvolution K g (N+1) (v+h)-finiteConvolution K g (N+1) v‖ ≤
      G*finiteCoefficientVariation K N*h := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hs := finiteConvolution_step_bound K g N (v+h) hG
    calc
      _ ≤ ‖finiteConvolution K g (N+1) (v+h+1)-finiteConvolution K g (N+1) (v+h)‖+
          ‖finiteConvolution K g (N+1) (v+h)-finiteConvolution K g (N+1) v‖ := by
        convert norm_sub_le_norm_sub_add_norm_sub
          (finiteConvolution K g (N+1) (v+h+1))
          (finiteConvolution K g (N+1) (v+h)) (finiteConvolution K g (N+1) v) using 1
      _ ≤ G*finiteCoefficientVariation K N+G*finiteCoefficientVariation K N*h := add_le_add hs ih
      _ = _ := by push_cast; ring

end JointDickman

end OAI
