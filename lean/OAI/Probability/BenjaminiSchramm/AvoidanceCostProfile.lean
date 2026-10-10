import OAI.Probability.BenjaminiSchramm.CriticalHeightHit

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Percolation.BenjaminiSchramm

lemma exp_neg_two_le_one_sub (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) :
    Real.exp (-2*r) ≤ 1-r := by
  have hp : 0 < 1-r := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  have hi : (1-r)⁻¹ ≤ 1+2*r := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have he := Real.exp_le_exp.mpr (show -2*r ≤ Real.log (1-r) by linarith)
  rwa [Real.exp_log hp] at he

theorem exists_vanishing_avoidance_cost (h : ℕ → ℝ)
    (hh : ∀ l, 0 ≤ h l) (M : ℝ) (hM : ∀ l, h l ≤ M)
    (hlim : Tendsto h atTop (𝓝 0)) (κ : ℝ) (hκ : 0 < κ) (hκone : κ ≤ 1) :
    ∃ g : ℕ → ℝ, (∀ l, 0 ≤ g l) ∧
      (∃ C : ℝ, ∀ l, g l ≤ C) ∧ Tendsto g atTop (𝓝 0) ∧
      ∀ n : ℕ, ∀ z : ℝ, κ ≤ z → 1-h n ≤ z → Real.exp (-g n) ≤ z := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2)))
  let g : ℕ → ℝ := fun n => if N ≤ n then 2*h n else -Real.log κ
  have hlog : 0 ≤ -Real.log κ := neg_nonneg.mpr (Real.log_nonpos hκ.le hκone)
  refine ⟨g,fun n => ?_,⟨max (2*M) (-Real.log κ),fun n => ?_⟩,?_,?_⟩
  · dsimp [g]
    split_ifs
    · exact mul_nonneg (by norm_num) (hh n)
    · exact hlog
  · dsimp [g]
    split_ifs
    · exact (mul_le_mul_of_nonneg_left (hM n) (by norm_num)).trans (le_max_left _ _)
    · exact le_max_right _ _
  · apply Tendsto.congr' (f₁ := fun n => 2*h n)
    · filter_upwards [eventually_ge_atTop N] with n hn
      exact (ite_eq_left hn).symm
    · simpa only [mul_zero] using tendsto_const_nhds.mul hlim
  · intro n z hκz hhz
    dsimp [g]
    by_cases hn : N ≤ n
    · rw [ite_eq_left hn]
      simpa only [neg_mul] using (exp_neg_two_le_one_sub (h n) (hh n) (hN n hn).le).trans hhz
    · rw [ite_eq_right hn,neg_neg,Real.exp_log hκ]
      exact hκz

end Percolation.BenjaminiSchramm

end

end OAI
