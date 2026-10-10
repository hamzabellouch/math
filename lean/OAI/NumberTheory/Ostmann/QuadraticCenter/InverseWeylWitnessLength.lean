import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeyl

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter

theorem inverse_weyl_at_witness_scale (α β Y η B : ℝ) (n : ℕ)
    (hY : 1 ≤ Y) (hη : 0 < η) (hη2 : η ≤ 2)
    (hB : 1 ≤ B) (hBsmall : B ≤ Y*η)
    (hscale : 1024*(1+Real.log (2*Y)) ≤ η^2*B)
    (hn : (n:ℝ) ≤ 2*Y)
    (hlarge : Y*η ≤ ‖quadraticWeylSum α β 0 n‖)
    (hnlarge : Y*η ≤ (n:ℝ)) :
    ∃ q : ℕ,1 ≤ q ∧ (q:ℝ) ≤ 2*B ∧ integerDistance ((q:ℝ)*α) ≤ B/(Y*η)^2 := by
  have hYp : 0 < Y := by linarith
  have hnp : 0 < n := by
    have : (0:ℝ)<n := (mul_pos hYp hη).trans_le hnlarge
    exact_mod_cast this
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hnp)
  have hMp : (0:ℝ) < (m:ℝ)+1 := by positivity
  have hMle : (m+1:ℝ) ≤ 2*Y := by exact_mod_cast hn
  have hlog := Real.log_le_log hMp hMle
  have hscaled : 256*(1+Real.log (m+1:ℝ)) ≤ (η/2)^2*B := by nlinarith
  have hBL : B ≤ (m+1:ℝ) := by exact_mod_cast hBsmall.trans hnlarge
  have hlarge' : (η/2)*(m+1:ℝ) ≤ ‖quadraticWeylSum α β 0 (m+1)‖ := by
    have hh : (η/2)*(m+1:ℝ) ≤ Y*η := by nlinarith
    exact hh.trans hlarge
  obtain ⟨q,hq,hqB,herr⟩ := inverse_quadratic_weyl α β 0 m (η/2) B
    (by positivity) (by linarith) hB hBL hscaled hlarge'
  refine ⟨q,hq,hqB,herr.trans ?_⟩
  apply div_le_div_of_nonneg_left (by linarith : 0 ≤ B) (sq_pos_of_pos (mul_pos hYp hη))
  have hl : Y*η ≤ (m+1:ℝ) := by exact_mod_cast hnlarge
  exact pow_le_pow_left₀ (mul_pos hYp hη).le hl 2

end Ostmann.QuadraticCenter

end

end OAI
