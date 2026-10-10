import OAI.NumberTheory.Ostmann.Quadratic.QuadraticHalfReflection

namespace OAI

/-! # The square-root weight in the second Poisson transform -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform

private theorem quadratic_log_pair_range {N s t : ℕ} (hN : 0 < N)
    (hs : N ≤ s) (hs₂ : s ≤ 2 * N) (ht : N ≤ t) (ht₂ : t ≤ 2 * N) :
    |Real.log s + Real.log t - 2 * Real.log N| ≤ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsR : (0 : ℝ) < s := hNR.trans_le (by exact_mod_cast hs)
  have htR : (0 : ℝ) < t := hNR.trans_le (by exact_mod_cast ht)
  have hslo : Real.log N ≤ Real.log s := Real.log_le_log hNR (by exact_mod_cast hs)
  have htlo : Real.log N ≤ Real.log t := Real.log_le_log hNR (by exact_mod_cast ht)
  have hsu : Real.log s ≤ Real.log 2 + Real.log N := by
    have hh := Real.log_le_log hsR (show (s : ℝ) ≤ 2 * N by exact_mod_cast hs₂)
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNR.ne'] at hh
  have htu : Real.log t ≤ Real.log 2 + Real.log N := by
    have hh := Real.log_le_log htR (show (t : ℝ) ≤ 2 * N by exact_mod_cast ht₂)
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNR.ne'] at hh
  have hl2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hu : |Real.log s + Real.log t - 2 * Real.log N| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  exact hu

noncomputable def quadraticLogRootKernel (ρ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) : 𝓢(ℝ, ℂ) :=
  (quadraticHalfReflection (quadraticLogWindow ρ (X * N))).compSubConstCLM ℂ (2 * Real.log N)

 theorem quadratic_log_root_kernel_identity (ρ : 𝓢(ℝ, ℂ)) (X : ℝ)
    {N s t : ℕ} (hN : 0 < N) (hs : N ≤ s) (hs₂ : s ≤ 2 * N)
    (ht : N ≤ t) (ht₂ : t ≤ 2 * N) :
    quadraticLogRootKernel ρ X N (Real.log s + Real.log t) =
      ρ (X * Real.sqrt ((s : ℝ) * t)) := by
  let v := Real.log s + Real.log t - 2 * Real.log N
  have hv : |v| ≤ 2 := quadratic_log_pair_range hN hs hs₂ ht ht₂
  have hv₂ : |-v / 2| ≤ 2 := by
    rw [abs_div, abs_neg]
    norm_num
    linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsR : (0 : ℝ) < s := hNR.trans_le (by exact_mod_cast hs)
  have htR : (0 : ℝ) < t := hNR.trans_le (by exact_mod_cast ht)
  have hvlog : v = Real.log (((s : ℝ) * t) / (N : ℝ) ^ 2) := by
    rw [Real.log_div (mul_ne_zero hsR.ne' htR.ne') (pow_ne_zero _ hNR.ne'),
      Real.log_mul hsR.ne' htR.ne', Real.log_pow]
    norm_num [v]
  have he : Real.exp (v / 2) ^ 2 = ((s : ℝ) * t) / (N : ℝ) ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (v / 2) = v by ring, hvlog, Real.exp_log (by positivity)]
  have hsquare : ((N : ℝ) * Real.exp (v / 2)) ^ 2 = (s : ℝ) * t := by
    rw [mul_pow, he]
    field_simp
  have hr : (N : ℝ) * Real.exp (v / 2) = Real.sqrt ((s : ℝ) * t) := by
    have hnonneg : 0 ≤ (N : ℝ) * Real.exp (v / 2) := by positivity
    have hsq := Real.sq_sqrt (show 0 ≤ (s : ℝ) * t by positivity)
    have hsqrt := Real.sqrt_nonneg ((s : ℝ) * t)
    nlinarith
  rw [quadraticLogRootKernel, SchwartzMap.compSubConstCLM_apply,
    quadraticHalfReflection_apply]
  change quadraticLogWindow ρ (X * N) (-v / 2) = _
  rw [quadraticLogWindow_eq ρ _ _ hv₂, show -(-v / 2) = v / 2 by ring]
  congr 1
  calc
    _ = X * ((N : ℝ) * Real.exp (v / 2)) := by ring
    _ = _ := by rw [hr]

 theorem quadratic_log_root_kernel_envelope (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ X Y : ℝ, 0 < Y → Y ≤ X → ∀ u : ℝ,
      ‖𝓕 (quadraticLogRootKernel ρ X N) u‖ ≤
        C * min 1 (1 / (Y * N) ^ A) * quadraticFourierEnvelope u := by
  obtain ⟨C, hC, hc⟩ := quadratic_log_window_envelope ρ A
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN X Y hY hYX u
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hX : 0 < X := hY.trans_le hYX
  rw [quadraticLogRootKernel, quadratic_fourier_translate_norm,
    quadratic_half_reflection_fourier_norm]
  have hh := hc (X * N) (by positivity) (-2 * u)
  calc
    _ ≤ 2 * (C * min 1 (1 / (X * N) ^ A) * quadraticFourierEnvelope (-2 * u)) := by
      gcongr
    _ ≤ 2 * (C * min 1 (1 / (Y * N) ^ A) * quadraticFourierEnvelope u) := by
      gcongr
      · exact quadraticFourierEnvelope_nonneg _
      · exact quadraticFourierEnvelope_half_reflection u
    _ = _ := by ring

end Ostmann

end OAI
