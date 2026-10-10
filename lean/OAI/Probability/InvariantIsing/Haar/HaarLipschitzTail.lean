import OAI.Probability.InvariantIsing.Haar.HaarLipschitzMoment
import OAI.Probability.InvariantIsing.Haar.HaarLipschitzContinuity

namespace OAI

/-! Gaussian tails about the Haar mean for arbitrary Lipschitz observables. -/
noncomputable section
open Matrix MeasureTheory Set
namespace InvariantIsing

theorem haar_lipschitz_chernoff {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V)
    (r β : ℝ) (hβ : 0 < β) :
    μ.real {U | r ≤ f U-(∫ V, f V ∂μ)} ≤
      Real.exp ((4*L^2)/(2*((N:ℝ)-2))*β^2-β*r) := by
  have hf := continuous_of_frobenius_lipschitz f L hLip
  let m := ∫ V, f V ∂μ
  let A := (4*L^2)/(2*((N:ℝ)-2))
  let F (U : SpecialOrthogonal N) := Real.exp (β*(f U-m))
  have hfi : Integrable F μ := continuous_haar_integrable μ _
    (Real.continuous_exp.comp (continuous_const.mul (hf.sub continuous_const)))
  have hmoment := haar_lipschitz_moment_bound hN μ f hf L hL hLip hβ
  have hI : (∫ U, F U ∂μ) ≤ Real.exp (A*β^2) := by
    have he : (∫ U, F U ∂μ) = Real.exp (-β*m)*(∫ U, Real.exp (β*f U) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all μ fun U => by
        change Real.exp (β*(f U-m)) = Real.exp (-β*m)*Real.exp (β*f U)
        rw [← Real.exp_add]
        congr 1
        ring
    rw [he]
    calc
      _ ≤ Real.exp (-β*m)*Real.exp (m*β+A*β^2) :=
        mul_le_mul_of_nonneg_left hmoment (Real.exp_pos _).le
      _ = Real.exp (A*β^2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hset : {U | Real.exp (β*r) ≤ F U} = {U | r ≤ f U-m} := by
    ext U
    simp only [mem_ofPred_eq,F,Real.exp_le_exp]
    exact mul_le_mul_iff_right₀ hβ
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ fun U => (Real.exp_pos _).le)
    hfi (Real.exp (β*r))
  rw [hset] at hm
  have hb : μ.real {U | r ≤ f U-m} ≤ Real.exp (A*β^2)/Real.exp (β*r) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    nlinarith [hm]
  simpa only [Real.exp_sub] using hb

theorem haar_lipschitz_upper_tail {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) {r : ℝ} (hr : 0 < r) :
    μ.real {U | r ≤ f U-(∫ V, f V ∂μ)} ≤
      Real.exp (-((N:ℝ)-2)*r^2/(8*L^2)) := by
  have hρ : 0 < (N:ℝ)-2 := by exact_mod_cast (show 0 < (N:ℤ)-2 by omega)
  have hC : 0 < 4*L^2 := by positivity
  have hb : 0 < ((N:ℝ)-2)*r/(4*L^2) := div_pos (mul_pos hρ hr) hC
  have h := haar_lipschitz_chernoff hN μ f L hL hLip r (((N:ℝ)-2)*r/(4*L^2)) hb
  convert h using 1
  congr 1
  field_simp
  ring

end InvariantIsing

end

end OAI
