import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialDuhamel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! # The differential of the noncommutative exponential

The difference formula and continuity of integrals on a compact interval
identify the derivative along each line. Analyticity then identifies the
actual Frechet differential; no inverse-exponential theorem is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

theorem hasDerivAt_exp_add_smul_zero (a b : A) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (a + s • b))
      (∫ t in (0 : ℝ)..1, NormedSpace.exp ((1 - t) • a) * b *
        NormedSpace.exp (t • a)) 0 := by
  let F : ℝ → ℝ → A := fun s t =>
    NormedSpace.exp ((1 - t) • a) * b * NormedSpace.exp (t • (a + s • b))
  have hF : Continuous F.uncurry := by
    exact ((NormedSpace.exp_continuous.comp
      ((continuous_const.sub continuous_snd).smul continuous_const)).mul
      continuous_const).mul (NormedSpace.exp_continuous.comp
        (continuous_snd.smul (continuous_const.add (continuous_fst.smul continuous_const))))
  have hc : Continuous (fun s => ∫ t in (0 : ℝ)..1, F s t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 1
  have he (s : ℝ) : NormedSpace.exp (a + s • b) - NormedSpace.exp a =
      s • ∫ t in (0 : ℝ)..1, F s t := by
    have h := exponential_sub_eq_integral a (a + s • b)
    simpa only [add_sub_cancel_left, mul_smul_comm, smul_mul_assoc,
      intervalIntegral.integral_smul, F] using h
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hlim : Tendsto (fun s => ∫ t in (0 : ℝ)..1, F s t) (𝓝[≠] 0)
      (𝓝 (∫ t in (0 : ℝ)..1, F 0 t)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have heq : slope (fun s : ℝ => NormedSpace.exp (a + s • b)) 0 =ᶠ[𝓝[≠] 0]
      (fun s => ∫ t in (0 : ℝ)..1, F s t) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s ≠ 0 := hs
    simp only [slope, sub_zero, zero_smul, add_zero, vsub_eq_sub, he,
      smul_smul, inv_mul_cancel₀ hs', one_smul]
  have hlim' := hlim.congr' heq.symm
  simpa only [F, zero_smul, add_zero] using hlim'

theorem fderiv_exp_eq_integral (a b : A) :
    fderiv ℝ NormedSpace.exp a b =
      ∫ t in (0 : ℝ)..1, NormedSpace.exp ((1 - t) • a) * b *
        NormedSpace.exp (t • a) := by
  have hd := (NormedSpace.exp_analytic (𝕂 := ℝ) a).differentiableAt.hasFDerivAt
  have hb : HasDerivAt (fun s : ℝ => a + s • b) b 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const b |>.const_add a
  have hd' : HasFDerivAt NormedSpace.exp (fderiv ℝ NormedSpace.exp a) (a + (0 : ℝ) • b) := by
    simpa only [zero_smul, add_zero] using hd
  have h := hd'.comp_hasDerivAt 0 hb
  simpa only [zero_smul, add_zero, Function.comp_def] using
    h.unique (hasDerivAt_exp_add_smul_zero a b)

end PolycyclicRecognition

end

end OAI
