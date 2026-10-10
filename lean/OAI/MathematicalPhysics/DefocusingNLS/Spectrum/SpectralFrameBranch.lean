import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarInitialBound

namespace OAI

/-! Isolate one approximate branch from the two-column transfer by subtracting
the matching first-coordinate multiple at the terminal point. -/

namespace DefocusingNLS

noncomputable def spectralFrameTransfer (D U : ℝ → ℂ × ℂ) (W : ℂ)
    (r t : ℝ) (q : ℂ × ℂ) : ℂ × ℂ :=
  (spectralScalarWronskian q (U t)/W) • D r +
    (spectralScalarWronskian (D t) q/W) • U r

theorem spectralFrameTransfer_sub_branch
    (D U : ℝ → ℂ × ℂ) (W : ℂ) (r t : ℝ) (q : ℂ × ℂ) (z : ℂ)
    (hW : W ≠ 0) (hdet : spectralScalarWronskian (D t) (U t) = W) :
    spectralFrameTransfer D U W r t (q-z • D t) =
      spectralFrameTransfer D U W r t q - z • D r := by
  have he : (D t).1*(U t).2 - (D t).2*(U t).1 = W := hdet
  apply Prod.ext
  · dsimp only [spectralFrameTransfer,spectralScalarWronskian,Prod.fst_add,Prod.fst_sub,
      Prod.smul_fst,Prod.smul_snd,Prod.snd_sub,smul_eq_mul]
    field_simp
    linear_combination -z*(D r).1*he
  · dsimp only [spectralFrameTransfer,spectralScalarWronskian,Prod.snd_add,Prod.snd_sub,
      Prod.smul_fst,Prod.smul_snd,Prod.fst_sub,smul_eq_mul]
    field_simp
    linear_combination -z*(D r).2*he

theorem spectralFrameTransfer_branch_error
    (D U : ℝ → ℂ × ℂ) (W : ℂ) (q : ℂ × ℂ) (lambda : ℂ)
    (kr kt C c Hr Ht r t : ℝ)
    (hkr : 0 ≤ kr) (hkt : 0 < kt) (hC : 0 ≤ C) (hc : 0 < c) (hW : c ≤ ‖W‖)
    (hdet : spectralScalarWronskian (D t) (U t) = W) (hval : (D t).1 ≠ 0)
    (hq : q.2 = lambda*q.1)
    (hDr : spectralShellNorm kr (D r) ≤ C*Real.exp Hr)
    (hDt : spectralShellNorm kt (D t) ≤ C*Real.exp Ht)
    (hUr : spectralShellNorm kr (U r) ≤ C*Real.exp (-Hr))
    (hUt : spectralShellNorm kt (U t) ≤ C*Real.exp (-Ht)) :
    spectralShellNorm kr
      (spectralFrameTransfer D U W r t q - (q.1/(D t).1) • D r) ≤
      (2*C^2/c)*Real.exp |Hr-Ht| *
        (‖q.1‖/kt)*‖lambda-(D t).2/(D t).1‖ := by
  have hW0 := norm_pos_iff.mp (hc.trans_le hW)
  rw [← spectralFrameTransfer_sub_branch D U W r t q (q.1/(D t).1) hW0 hdet]
  have hb := spectralScalarInitialTerm_bound D U W (q-(q.1/(D t).1) • D t)
    kr kt C c Hr Ht r t hkr hkt hC hc hW hDr hDt hUr hUt
  have he : spectralShellNorm kt (q-(q.1/(D t).1) • D t) =
      (‖q.1‖/kt)*‖lambda-(D t).2/(D t).1‖ := by
    have hf : q.1-(q.1/(D t).1)*(D t).1 = 0 := by field_simp; ring
    have hs : q.2-(q.1/(D t).1)*(D t).2 =
        q.1*(lambda-(D t).2/(D t).1) := by rw [hq]; ring
    dsimp only [spectralShellNorm,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    rw [hf,hs,norm_zero,mul_zero,zero_add,norm_mul]
    ring
  change spectralShellNorm kr (spectralFrameTransfer D U W r t _) ≤ _ at hb
  rw [he] at hb
  simpa only [mul_assoc] using hb

end DefocusingNLS

end OAI
