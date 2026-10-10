import OAI.NumberTheory.TwoPoint.Fourier.MinorArcFirstBand
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTResolution

namespace OAI

/-! The first-band logarithmic resolution absorbs the explicit kernel
costs for the fixed lower endpoint used in the MRT application. -/

namespace TwoPointCorrelations

open Filter

lemma mrt_first_resolution_lower (A : ℕ) (hA : 500000 ≤ A) {H Q : ℝ}
    (hL : 1 ≤ Real.log H) (hLL : 0 ≤ Real.log (Real.log H))
    (hQ : 1 < Q) (hQH : Q ≤ H) :
    (Real.log H)^100 ≤ mrtBaseResolution (minorArcFirstLower A H) Q (1/100) := by
  have hL0 : 0 < Real.log H := by linarith
  have hA' : (500000:ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hA' hLL
  have hmono := Real.log_le_log (Real.log_pos hQ)
    (Real.log_le_log (by linarith : 0 < Q) hQH)
  have he : (Real.log H)^100 = Real.exp (100*Real.log (Real.log H)) := by
    rw [show (100:ℝ) = ((100:ℕ):ℝ) by norm_num, Real.exp_nat_mul,
      Real.exp_log hL0]
  rw [he, mrtBaseResolution, minor_arc_first_lower_log]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma mrt_first_kernel_error (A : ℕ) (hA : 500000 ≤ A) {H Q : ℝ}
    (hL : 1 ≤ Real.log H) (hLL : 0 ≤ Real.log (Real.log H))
    (hQ : 1 < Q) (hQH : Q ≤ H) :
    33792*Real.exp 1*(mrtBaseResolution (minorArcFirstLower A H) Q (1/100))⁻¹ +
      2*(minorArcFirstLower A H)⁻¹ +
      1024*Real.exp 2*(mrtBaseResolution (minorArcFirstLower A H) Q (1/100))⁻¹*
        (1+Q/H) ≤ (33792*Real.exp 1+2+2048*Real.exp 2)/(Real.log H)^100 := by
  have hH0 : 0 < H := (by linarith : 0 < Q).trans_le hQH
  have hp : 0 < (Real.log H)^100 := pow_pos (by linarith) _
  have hres := mrt_first_resolution_lower A hA hL hLL hQ hQH
  have hfirst : (Real.log H)^100 ≤ minorArcFirstLower A H :=
    pow_le_pow_right₀ hL (by omega : 100 ≤ 5*A)
  have hr : (mrtBaseResolution (minorArcFirstLower A H) Q (1/100))⁻¹ ≤
      ((Real.log H)^100)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hp hres
  have hf : (minorArcFirstLower A H)⁻¹ ≤ ((Real.log H)^100)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hp hfirst
  have hq : 1+Q/H ≤ 2 := by
    have hh := (div_le_one hH0).mpr hQH
    linarith
  have hb : 1024*Real.exp 2*(mrtBaseResolution (minorArcFirstLower A H) Q (1/100))⁻¹*
      (1+Q/H) ≤ 1024*Real.exp 2*((Real.log H)^100)⁻¹*2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hr (by positivity)) hq (by positivity) (by positivity)
  calc
    _ ≤ 33792*Real.exp 1*((Real.log H)^100)⁻¹ +
        2*((Real.log H)^100)⁻¹+1024*Real.exp 2*((Real.log H)^100)⁻¹*2 :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hr (by positivity))
        (mul_le_mul_of_nonneg_left hf (by norm_num))) hb
    _ = _ := by ring

theorem mrt_first_kernel_error_eventually (A : ℕ) (hA : 500000 ≤ A) :
    ∀ᶠ H : ℝ in atTop,
      33792*Real.exp 1*(mrtBaseResolution (minorArcFirstLower A H)
        (minorArcFirstUpper H) (1/100))⁻¹ +
      2*(minorArcFirstLower A H)⁻¹ +
      1024*Real.exp 2*(mrtBaseResolution (minorArcFirstLower A H)
        (minorArcFirstUpper H) (1/100))⁻¹*(1+minorArcFirstUpper H/H) ≤
        (33792*Real.exp 1+2+2048*Real.exp 2)/(Real.log H)^100 := by
  filter_upwards [minor_arc_first_band_scale A 0 (by omega)] with H hscale
  obtain ⟨hH, hL, hLL, hP, _, _, hPQ, hQU, _, _⟩ := hscale
  apply mrt_first_kernel_error A hA (by linarith) (by linarith) (by linarith)
  exact hQU.trans (div_le_self (by linarith) (one_le_pow₀ (by linarith : 1 ≤ Real.log H)))

end TwoPointCorrelations

end OAI
