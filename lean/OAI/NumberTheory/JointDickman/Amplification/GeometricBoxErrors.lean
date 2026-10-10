import OAI.NumberTheory.JointDickman.Counting.HistogramWindowOverlap

namespace OAI

/-! # Summing per-box power savings over the manuscript's geometric scale -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem geometric_box_count {B : ℕ} (hB : 1 ≤ B) {t : ℝ} (ht : 0 < t)
    (S : Finset ℤ)
    (hS : ∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) :
    (S.card : ℝ) ≤ (8/(5*t)+1)*(B : ℝ) := by
  have hcount := integer_interval_card_le S
    (div_le_div_of_nonneg_right (by nlinarith [show (0 : ℝ) ≤ B from Nat.cast_nonneg B] : (9/10 : ℝ)*B ≤ (5/2 : ℝ)*B) ht.le)
    (by
      intro k hk
      exact ⟨(div_le_iff₀ ht).mpr (hS k hk).1,(le_div_iff₀ ht).mpr (hS k hk).2⟩)
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  refine hcount.trans ?_
  have he : ((5/2 : ℝ)*B)/t-((9/10 : ℝ)*B)/t = (8/(5*t))*(B : ℝ) := by ring
  rw [he]
  nlinarith

theorem geometric_box_error_sum {B : ℕ} (hB : 1 ≤ B) {t : ℝ} (ht : 0 < t)
    (S : Finset ℤ)
    (hS : ∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B))
    (E : ℤ → ℂ) {T C r : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hE : ∀ k ∈ S, T*‖E k‖ ≤ C*(B : ℝ)^r) :
    T*‖∑ k ∈ S, E k‖ ≤ ((8/(5*t)+1)*C)*(B : ℝ)^(r+1) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  calc
    _ ≤ T*∑ k ∈ S, ‖E k‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hT
    _ = ∑ k ∈ S, T*‖E k‖ := mul_sum _ _ _
    _ ≤ ∑ _k ∈ S, C*(B : ℝ)^r := sum_le_sum hE
    _ = (S.card : ℝ)*(C*(B : ℝ)^r) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ ((8/(5*t)+1)*(B : ℝ))*(C*(B : ℝ)^r) :=
      mul_le_mul_of_nonneg_right (geometric_box_count hB ht S hS) (by positivity)
    _ = _ := by rw [Real.rpow_add hBr,Real.rpow_one]; ring

theorem geometric_box_error_vanishing {t r C : ℝ} (_ht : 0 < t) (hr : r < -1) :
    Tendsto (fun B : ℕ => ((8/(5*t)+1)*C)*(B : ℝ)^(r+1)) atTop (𝓝 0) := by
  have h := ((tendsto_rpow_neg_atTop (by linarith : 0 < -(r+1))).comp
    tendsto_natCast_atTop_atTop).const_mul ((8/(5*t)+1)*C)
  simpa only [neg_neg,mul_zero,Function.comp_def] using h

end JointDickman

end OAI
