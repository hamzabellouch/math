import OAI.Analysis.KadisonKastler.ModularStripKernel

namespace OAI

/-! # Boundary values of the modular strip kernel -/

namespace KadisonKastler

noncomputable section

private theorem negative_phase_exp (t s : ℝ) :
    Complex.exp ((-Complex.I * (t : ℂ)) * (resolventLogFrequency s : ℂ)) =
      modularSpectralPhase (-t) s := by
  unfold modularSpectralPhase resolventLogFrequency
  congr 1
  push_cast
  ring

theorem modularStripKernel_bottom (t s : ℝ) :
    modularStripKernel (t : ℂ) s = (s : ℂ) * modularSpectralPhase (-t) s := by
  unfold modularStripKernel
  rw [negative_phase_exp]

theorem modularStripKernel_top {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (t : ℝ) :
    modularStripKernel ((t : ℂ) + Complex.I) s =
      ((1 - s : ℝ) : ℂ) * modularSpectralPhase (-t) s := by
  have he : (-Complex.I * ((t : ℂ) + Complex.I)) * (resolventLogFrequency s : ℂ) =
      (resolventLogFrequency s : ℂ) + (-Complex.I * (t : ℂ)) * (resolventLogFrequency s : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hr : s * Real.exp (resolventLogFrequency s) = 1 - s := by
    unfold resolventLogFrequency
    rw [Real.exp_sub, Real.exp_log (sub_pos.mpr hs1), Real.exp_log hs]
    field_simp
  have hc := congrArg (fun q : ℝ => (q : ℂ)) hr
  push_cast at hc
  rw [modularStripKernel, he, Complex.exp_add, ← mul_assoc, hc,
    negative_phase_exp]
  simp only [Complex.ofReal_sub, Complex.ofReal_one]

end

end KadisonKastler

end OAI
