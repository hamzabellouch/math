import OAI.Probability.InvariantIsing.Haar.HaarTwoSidedTail
import OAI.Probability.InvariantIsing.Gaussian.GaussianMedianTail

namespace OAI

/-!
The exact Gromov--Milman specialization used by the pressure proof. The proof
uses the actual polynomial heat operator on SO(N), its proved curvature bound,
positive polynomial convolution, and the scalar entropy argument.
-/
noncomputable section
open Matrix MeasureTheory
namespace InvariantIsing

theorem haarConcentration_proved : HaarConcentrationInput := by
  refine ⟨Real.exp 1,1/192,Real.exp_pos _,by norm_num,?_⟩
  intro N hN μ hμ hμinv f hf L hL hLip
  let : IsProbabilityMeasure μ := hμ
  let : μ.IsMulLeftInvariant := hμinv
  obtain ⟨m,hm1,hm2⟩ := measurable_median μ f hf
  refine ⟨m,hm1,hm2,?_⟩
  intro r hr
  let k := ((N:ℝ)-2)/(8*L^2)
  have hρ : 0 < (N:ℝ)-2 := by exact_mod_cast (show 0 < (N:ℤ)-2 by omega)
  have hk : 0 < k := div_pos hρ (by positivity)
  have hplus (s : ℝ) (hs : 0 < s) :
      μ.real {U | s ≤ f U-(∫ V, f V ∂μ)} ≤ Real.exp (-k*s^2) := by
    have hh := haar_lipschitz_upper_tail hN μ f L hL hLip hs
    convert hh using 1
    congr 1
    dsimp only [k]
    ring
  have hminus (s : ℝ) (hs : 0 < s) :
      μ.real {U | s ≤ (∫ V, f V ∂μ)-f U} ≤ Real.exp (-k*s^2) := by
    have hh := haar_lipschitz_lower_tail hN μ f L hL hLip hs
    convert hh using 1
    congr 1
    dsimp only [k]
    ring
  apply (gaussian_median_tail μ f (∫ V, f V ∂μ) m k hk hm1 hm2 hplus hminus hr).trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
  have hdim : (N:ℝ) ≤ 3*((N:ℝ)-2) := by
    have hn : (3:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hnum : -3*((N:ℝ)-2)*r^2 ≤ -(N:ℝ)*r^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdim) (sq_nonneg r)]
  calc
    -k*r^2/8 = (-3*((N:ℝ)-2)*r^2)/(192*L^2) := by dsimp only [k]; ring
    _ ≤ (-(N:ℝ)*r^2)/(192*L^2) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = -(1/192)*(N:ℝ)*r^2/L^2 := by ring

end InvariantIsing

end

end OAI
