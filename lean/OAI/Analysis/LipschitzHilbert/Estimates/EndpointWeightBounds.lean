import OAI.Analysis.LipschitzHilbert.Estimates.SegmentWeights
import OAI.Analysis.LipschitzHilbert.Estimates.TopMovingLogAbsorption

namespace OAI

/-! Endpoint variation bounds in the inverse-fourth-power form used by
the source amplitude motion argument. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem endpoint_variation_le_add (w w' : ℕ → ℂ) (start N : ℕ) :
    ‖w' N‖+(∑ j ∈ Finset.Ico start N, ‖w' (j+1)-w' j‖) ≤
      (‖w N‖+(∑ j ∈ Finset.Ico start N, ‖w (j+1)-w j‖)) +
      (‖w' N-w N‖+(∑ j ∈ Finset.Ico start N,
        ‖(w' (j+1)-w (j+1))-(w' j-w j)‖)) := by
  have hend : ‖w' N‖ ≤ ‖w N‖+‖w' N-w N‖ := by
    calc
      _ = ‖w N+(w' N-w N)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hsum : (∑ j ∈ Finset.Ico start N, ‖w' (j+1)-w' j‖) ≤
      (∑ j ∈ Finset.Ico start N, ‖w (j+1)-w j‖)+
      (∑ j ∈ Finset.Ico start N, ‖(w' (j+1)-w (j+1))-(w' j-w j)‖) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    calc
      _ = ‖(w (j+1)-w j)+((w' (j+1)-w (j+1))-(w' j-w j))‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  linarith

theorem boundary_weight_variation_fourth (n m : ℕ → ℝ) (phase : ℕ → ℂ)
    (start N K : ℕ) (a h S C Z : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hh : 0 < h) (hZ : 0 ≤ Z)
    (hC : 1 ≤ C) (hhC : h ≤ C)
    (hn : ∀ j ≤ N, h ≤ n j) (hnS : n 0 ≤ S) (hmono : AntitoneOn n (Set.Iic N))
    (hm : ∀ j < N, n (j+1) ≤ m j ∧ m j ≤ n (j+1-K))
    (hz0 : ∀ j < N, 0 ≤ (phase j).re) (hz : ∀ j < N, ‖phase j‖ ≤ Z) :
    ‖segmentWeight n (boundaryLog n m) phase a start N‖ +
      (∑ j ∈ Finset.Ico start N,
        ‖segmentWeight n (boundaryLog n m) phase a start (j+1)-
          segmentWeight n (boundaryLog n m) phase a start j‖) ≤
      C^4*(1+(a+Z*K)*(Real.log (max 1 S)+1))^2*h^(-(4:ℝ)) := by
  have hn0 : 0 < n 0 := hh.trans_le (hn 0 (Nat.zero_le N))
  have hnN : 0 < n N := hh.trans_le (hn N le_rfl)
  have hhS : h ≤ S := (hn 0 (Nat.zero_le N)).trans hnS
  have hS : 0 < S := hh.trans_le hhS
  have hQ : 0 ≤ a+Z*K := by positivity
  have hlog : Real.log (n 0/n N) ≤ Real.log (S/h) := by
    apply Real.log_le_log (div_pos hn0 hnN)
    exact (div_le_div_of_nonneg_right hnS hnN.le).trans
      (div_le_div_of_nonneg_left hS.le hh (hn N le_rfl))
  have hF : 1 ≤ 1+(a+Z*K)*Real.log (S/h) := by
    have := Real.log_nonneg ((one_le_div hh).mpr hhS)
    exact le_add_of_nonneg_right (mul_nonneg hQ this)
  have hsq : 1+(a+Z*K)*Real.log (n 0/n N) ≤ (1+(a+Z*K)*Real.log (S/h))^2 := by
    have hh' := mul_le_mul_of_nonneg_left hlog hQ
    nlinarith
  exact (boundary_weight_variation n m phase start N K a h Z ha0 hh hZ hn hmono hm hz0 hz).trans
    ((mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hh.le _)).trans
      (top_inverse_log_squared_absorption hh hhS hC hhC hQ ha0 ha1))

end LipschitzHilbert

end

end OAI
