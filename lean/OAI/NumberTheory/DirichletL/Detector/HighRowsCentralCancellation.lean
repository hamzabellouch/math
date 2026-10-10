import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedCancellation

namespace OAI

noncomputable section
namespace SevenEighths.ProbeLocal

theorem central_phase_error_bound (V W D P B q vInv : ℂ) (A T : ℝ)
    (hA : 1≤A) (hV : ‖V‖≤1/2) (hD : ‖D‖≤1/2)
    (hW : ‖W‖≤A) (hq : ‖q‖≤A) (hv : ‖vInv‖≤1)
    (hVT : A^2*‖V‖≤T) (hDT : A^2*‖D‖≤T)
    (hET : A^2*‖P+D‖≤28*T) (hBET : A*‖B‖*‖P+D‖≤28*T)
    (hBD : B*D=vInv) (hWq : vInv*W=q) :
    ‖compensatedReplacement V W D P B q+continuedCorrection V W D P*vInv‖≤720*T := by
  have hA0 : 0≤A := by linarith
  have hT : 0≤T := (mul_nonneg (sq_nonneg A) (norm_nonneg V)).trans hVT
  have h1V : ‖1-V‖≤2 := by
    have hh := norm_sub_le (1:ℂ) V
    rw [norm_one] at hh
    linarith
  have h1W : ‖1-W‖≤2*A := by
    have hh := norm_sub_le (1:ℂ) W
    rw [norm_one] at hh
    linarith
  have hdiff : ‖vInv-q‖≤2*A := (norm_sub_le vInv q).trans (by linarith)
  have hfac : ‖(1-V)*(1-W)/(1-D)‖≤8*A := by
    rw [div_eq_mul_inv,norm_mul,norm_mul]
    have hi := inv_one_sub_norm_le_two D hD
    calc
      _ ≤ 2*(2*A)*2 := by gcongr
      _ = _ := by ring
  have hleft : ‖(vInv-q)*(V/(1-V)-D)‖≤2*A*(2*‖V‖+‖D‖) := by
    rw [norm_mul]
    apply mul_le_mul hdiff _ (norm_nonneg _) (by positivity)
    calc
      _ ≤ ‖V/(1-V)‖+‖D‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [div_eq_mul_inv,norm_mul]
        have hi := inv_one_sub_norm_le_two V hV
        nlinarith [mul_le_mul_of_nonneg_left hi (norm_nonneg V)]
  have hright : ‖(B+vInv-q)*(P+D)‖≤(‖B‖+2*A)*‖P+D‖ := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ = ‖B+(vInv-q)‖ := by congr 1;ring
      _ ≤ ‖B‖+‖vInv-q‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  rw [continued_normalized_cancellation V W D P B q vInv
    (one_sub_ne_zero_of_norm_le_half V hV) (one_sub_ne_zero_of_norm_le_half D hD) hBD hWq,norm_mul]
  calc
    _ ≤ (8*A)*(2*A*(2*‖V‖+‖D‖)+(‖B‖+2*A)*‖P+D‖) := by
      apply mul_le_mul hfac _ (norm_nonneg _) (by positivity)
      exact (norm_add_le _ _).trans (add_le_add hleft hright)
    _ = 32*(A^2*‖V‖)+16*(A^2*‖D‖)+8*(A*‖B‖*‖P+D‖)+16*(A^2*‖P+D‖) := by ring
    _ ≤ 720*T := by linarith

end SevenEighths.ProbeLocal
end

end OAI
