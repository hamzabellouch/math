import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.L2Pairings
import OAI.Analysis.RieszRectifiability.Kernel.KernelTails

namespace OAI

/-!
# First-moment bounds on dyadic shells

Cauchy–Schwarz bounds an absolute first moment by the mass and second moment of
a finite measure. Applying this estimate to dyadic annuli combines upper growth
with shellwise second-moment decay to control the corresponding height integral.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem integral_abs_sq_le_mass_second_moment {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (w : X → ℝ) (hw : MemLp w 2 ν) :
    (∫ x, |w x| ∂ν) ^ 2 ≤ ν.real univ * (∫ x, w x ^ 2 ∂ν) := by
  have h := integral_mul_cauchy_schwarz_sq ν (fun x => ‖w x‖) (fun _ => (1 : ℝ))
    hw.norm (memLp_const 1)
  simpa only [mul_one, one_mul, one_pow, integral_const, smul_eq_mul, Real.norm_eq_abs,
    sq_abs, mul_comm] using! h

theorem integral_abs_le_of_mass_second_moment {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (w : X → ℝ) (hw : MemLp w 2 ν)
    (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hmass : ν.real univ ≤ M) (hsecond : (∫ x, w x ^ 2 ∂ν) ≤ M * A ^ 2) :
    (∫ x, |w x| ∂ν) ≤ M * A := by
  have hsq : (∫ x, |w x| ∂ν) ^ 2 ≤ (M * A) ^ 2 := by
    calc
      _ ≤ ν.real univ * (∫ x, w x ^ 2 ∂ν) := integral_abs_sq_le_mass_second_moment ν w hw
      _ ≤ M * (M * A ^ 2) := mul_le_mul hmass hsecond
        (integral_nonneg fun x => sq_nonneg _) hM
      _ = _ := by ring
  exact (sq_le_sq₀ (integral_nonneg fun x => abs_nonneg _) (mul_nonneg hM hA)).mp hsq

theorem shell_height_l1_bound {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (w : Ambient d → ℝ) (hw : MemLp w 2 (μ.restrict (dyadicAnnulus a R k)))
    (δ b : ℝ) (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (hsecond : (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    (∫ y in dyadicAnnulus a R k, |w y| ∂μ) ≤
      B * δ * (R * 2 ^ k) ^ (m + 1) * b ^ k := by
  let ν := μ.restrict (dyadicAnnulus a R k)
  have : IsFiniteMeasure ν := ⟨by
    simpa only [ν, Measure.restrict_apply_univ] using! dyadicAnnulus_measure_lt_top m C μ hg a R hR k⟩
  have hB : 0 ≤ B := (mul_nonneg hg.1 (by positivity)).trans hCB
  have hmass : ν.real univ ≤ B * (R * 2 ^ k) ^ m := by
    have hmass' : μ.real (dyadicAnnulus a R k) ≤ C * (R * 2 ^ (k + 1)) ^ m :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (by positivity))
        ((measure_mono (dyadicAnnulus_subset_ball a R k)).trans (hg.2 a _ (by positivity)))
    have heq : C * (R * (2 : ℝ) ^ (k + 1)) ^ m = (C * 2 ^ m) * (R * 2 ^ k) ^ m := by
      rw [pow_succ, show R * ((2 : ℝ) ^ k * 2) = (R * 2 ^ k) * 2 by ring, mul_pow]
      ring
    change (μ.restrict (dyadicAnnulus a R k)).real univ ≤ _
    simpa only [Measure.real, Measure.restrict_apply_univ] using!
      hmass'.trans (heq ▸ mul_le_mul_of_nonneg_right hCB (by positivity))
  have h := integral_abs_le_of_mass_second_moment ν w hw
    (B * (R * 2 ^ k) ^ m) (δ * (R * 2 ^ k) * b ^ k) (by positivity) (by positivity) hmass hsecond
  convert! h using 1
  rw [pow_succ]
  ring

end

end RieszRectifiability

end OAI
