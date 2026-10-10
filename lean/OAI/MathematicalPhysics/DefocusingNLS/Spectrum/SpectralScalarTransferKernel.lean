import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellGreenBounds

namespace OAI

/-! The initial-value transfer kernel of an approximate scalar frame.
Its exponential factor involves only the difference of the same channel's action. -/

namespace DefocusingNLS

noncomputable def spectralScalarTransferKernel (D U : ℝ → ℂ × ℂ)
    (W : ℂ) (r t : ℝ) : ℂ × ℂ :=
  ((D t).1/W) • U r-((U t).1/W) • D r

theorem spectralShellNorm_neg (k : ℝ) (u : ℂ × ℂ) :
    spectralShellNorm k (-u)=spectralShellNorm k u := by
  simp only [spectralShellNorm,Prod.fst_neg,Prod.snd_neg,norm_neg]

theorem spectralShellNorm_sub_le (k : ℝ) (hk : 0≤ k) (u v : ℂ × ℂ) :
    spectralShellNorm k (u-v)≤ spectralShellNorm k u+spectralShellNorm k v := by
  simpa only [sub_eq_add_neg,spectralShellNorm_neg] using spectralShellNorm_add_le k hk u (-v)

theorem spectralScalarTransferKernel_bound
    (D U : ℝ → ℂ × ℂ) (W : ℂ) (kr kt C c Hr Ht r t : ℝ)
    (hkr : 0≤ kr) (hkt : 0<kt) (hC : 0≤ C) (hc : 0<c) (hW : c≤‖W‖)
    (hDr : spectralShellNorm kr (D r)≤ C*Real.exp Hr)
    (hDt : spectralShellNorm kt (D t)≤ C*Real.exp Ht)
    (hUr : spectralShellNorm kr (U r)≤ C*Real.exp (-Hr))
    (hUt : spectralShellNorm kt (U t)≤ C*Real.exp (-Ht)) :
    spectralShellNorm kr (spectralScalarTransferKernel D U W r t)≤
      (2*C^2/(c*kt))*Real.exp |Hr-Ht| := by
  have hW0 : c*Real.exp 0≤‖W‖ := by simpa only [Real.exp_zero,mul_one] using hW
  have hfirst := spectralShellNorm_green_factor kr kt C c 0 Hr Ht hkr hkt hC hc
    (U r) (D t) W (by simpa only [zero_sub] using hUr) hDt hW0
  have hsecond := spectralShellNorm_green_factor kr kt C c 0 (-Hr) (-Ht) hkr hkt hC hc
    (D r) (U t) W (by simpa only [zero_sub,neg_neg] using hDr) hUt hW0
  have hc0 : 0≤ C^2/(c*kt) := by positivity
  have h1 : Ht-Hr≤|Hr-Ht| := by simpa only [abs_sub_comm] using le_abs_self (Ht-Hr)
  have h2 : -Ht- -Hr≤|Hr-Ht| := by linarith [le_abs_self (Hr-Ht)]
  calc
    _ ≤ spectralShellNorm kr (((D t).1/W) • U r)+
        spectralShellNorm kr (((U t).1/W) • D r) := spectralShellNorm_sub_le kr hkr _ _
    _ ≤ C^2/(c*kt)*Real.exp (Ht-Hr)+C^2/(c*kt)*Real.exp (-Ht- -Hr) :=
      add_le_add hfirst hsecond
    _ ≤ C^2/(c*kt)*Real.exp |Hr-Ht|+C^2/(c*kt)*Real.exp |Hr-Ht| :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) hc0)
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) hc0)
    _ = _ := by ring

end DefocusingNLS

end OAI
