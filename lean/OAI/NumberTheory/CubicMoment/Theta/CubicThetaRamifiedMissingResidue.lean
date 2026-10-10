import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedMissingClass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierParity

namespace OAI

/-! The first absent ramified class is absent from the actual continued
coefficient and its spectral residue, not merely from a formal model. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

theorem cubicThetaFrequencyContinuation_lambda_missing_germ
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) {s : ℂ} (hs : 1<s.re) :
    cubicThetaFrequencyContinuation (lambdaE*h)=ᶠ[𝓝[≠] s] (fun _ => 0) := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero lambdaE)
  apply cubicThetaMeromorphic_identity
    (fun z hz => cubicThetaFrequencyContinuation_meromorphic
      (mul_ne_zero lambdaE_prime.ne_zero hh0) hz)
    (fun _ _ => analyticAt_const.meromorphicAt)
    (convex_halfSpace_re_gt 1).isPreconnected (z₀:=(4:ℂ))
    (by change 1<(4:ℂ).re; norm_num) hs
  have hn : ∀ᶠ z : ℂ in 𝓝 4, 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaFrequencyContinuation_right _ hz]
  exact cubicThetaFrequencyDirichlet_lambda_missing (by linarith) hh

theorem cubicThetaRegularizedFrequency_lambda_missing
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) {s : ℂ} (hs : 1<s.re) :
    cubicThetaRegularizedFrequency (lambdaE*h) s=0 := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero lambdaE)
  have he : cubicThetaRegularizedFrequency (lambdaE*h)=ᶠ[𝓝[≠] s] (fun _ => 0) := by
    filter_upwards [cubicThetaRegularizedFrequency_germ
      (mul_ne_zero lambdaE_prime.ne_zero hh0) hs,
      cubicThetaFrequencyContinuation_lambda_missing_germ hh hs] with z hz hz0
    rw [hz,hz0,mul_zero]
  exact tendsto_nhds_unique
    (((cubicThetaRegularizedFrequency_analytic
      (mul_ne_zero lambdaE_prime.ne_zero hh0) s hs).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds).congr' he) tendsto_const_nhds

theorem cubicThetaArithmeticFourierResidue_lambda_missing
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) :
    cubicThetaArithmeticFourierResidue (lambdaE*h) (4/3)=0 := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero lambdaE)
  rw [← cubicThetaRegularizedFrequency_residue (mul_ne_zero lambdaE_prime.ne_zero hh0)]
  exact cubicThetaRegularizedFrequency_lambda_missing hh (by norm_num)

end CubicFirstMoment

end

end OAI
