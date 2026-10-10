import OAI.Analysis.KadisonKastler.WeightedStripKernel
import OAI.Analysis.KadisonKastler.ModularSpectralPhase
import OAI.Analysis.KadisonKastler.CharacterContinuity

namespace OAI

/-! # Boundary values of the endpoint-weighted spectral strip -/

namespace KadisonKastler

noncomputable section

theorem weightedStripKernel_vertical {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (x t : ℝ) :
    weightedStripKernel ((x : ℂ) + t * Complex.I) s =
      weightedStripKernel (x : ℂ) s * modularSpectralPhase t s := by
  have hsn : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hqn : ((1 - s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_pos.mpr hs1).ne'
  have h₁ : (3 / 2 : ℂ) - (x + t * Complex.I) = ((3 / 2 : ℂ) - x) + -(t * Complex.I) := by ring
  have h₂ : (5 / 2 : ℂ) + (x + t * Complex.I) = ((5 / 2 : ℂ) + x) + t * Complex.I := by ring
  unfold weightedStripKernel modularSpectralPhase
  rw [h₁, h₂, Complex.cpow_add _ _ hsn, Complex.cpow_add _ _ hqn]
  rw [Complex.cpow_def_of_ne_zero hsn (-(t * Complex.I)),
    Complex.cpow_def_of_ne_zero hqn (t * Complex.I)]
  rw [← Complex.ofReal_log hs.le, ← Complex.ofReal_log (sub_nonneg.mpr hs1.le)]
  push_cast
  have he : Complex.exp ((Real.log s : ℂ) * -(t * Complex.I)) *
      Complex.exp ((Real.log (1 - s) : ℂ) * (t * Complex.I)) =
      Complex.exp (Complex.I * (t * ((Real.log (1 - s) : ℂ) - (Real.log s : ℂ)))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = ((s : ℂ) ^ ((3 / 2 : ℂ) - x) * ((1 - (s : ℂ)) ^ ((5 / 2 : ℂ) + x))) *
        (Complex.exp ((Real.log s : ℂ) * -(t * Complex.I)) *
          Complex.exp ((Real.log (1 - s) : ℂ) * (t * Complex.I))) := by ring
    _ = _ := by rw [he]

theorem weightedStripKernel_right {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (t : ℝ) :
    weightedStripKernel ((1 / 2 : ℂ) + t * Complex.I) s =
      (s : ℂ) * ((1 - s : ℝ) : ℂ) ^ 3 * modularSpectralPhase t s := by
  have h := weightedStripKernel_vertical hs hs1 (1 / 2) t
  convert h using 1 <;> push_cast
  · congr 1
  · unfold weightedStripKernel
    norm_num [Complex.cpow_ofNat]

theorem weightedStripKernel_left {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (t : ℝ) :
    weightedStripKernel ((-1 / 2 : ℂ) + t * Complex.I) s =
      (s : ℂ) ^ 2 * ((1 - s : ℝ) : ℂ) ^ 2 * modularSpectralPhase t s := by
  have h := weightedStripKernel_vertical hs hs1 (-1 / 2) t
  convert h using 1 <;> push_cast
  · congr 1
  · unfold weightedStripKernel
    norm_num [Complex.cpow_ofNat]


theorem weightedStripKernel_center {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    weightedStripKernel 0 s =
      (s : ℂ) * ((1 - s : ℝ) : ℂ) ^ 2 *
        ((Real.sqrt s : ℂ) * (Real.sqrt (1 - s) : ℂ)) := by
  have hsn : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hqn : ((1 - s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_pos.mpr hs1).ne'
  have hsqrt (x : ℝ) (hx : 0 ≤ x) :
      (x : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt x : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow hx (1 / 2)).symm
  unfold weightedStripKernel
  rw [sub_zero, add_zero, show (3 / 2 : ℂ) = 1 + 1 / 2 by ring,
    show (5 / 2 : ℂ) = 2 + 1 / 2 by ring,
    Complex.cpow_add _ _ hsn, Complex.cpow_add _ _ hqn,
    Complex.cpow_one, Complex.cpow_two, hsqrt s hs.le,
    hsqrt (1 - s) (sub_nonneg.mpr hs1.le)]
  ring

end

end KadisonKastler

end OAI
