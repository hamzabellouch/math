import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFieldParameterLimit

namespace OAI

/-! The elementary contraction bound also converges on a fixed subunit
profile ball, so the limiting gap holds for every sufficiently large power. -/

open Filter Topology
namespace DefocusingNLS

theorem circularFieldBound_subunit_tendsto (νp νm : ℕ → ℂ) (μp μm η : ℂ)
    (hp : Tendsto νp atTop (𝓝 μp)) (hm : Tendsto νm atTop (𝓝 μm))
    (m : ℕ → ℕ) (hmTop : Tendsto m atTop atTop)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun n => circularFieldBound (νp n) (νm n) η (m n) ρ) atTop
      (𝓝 (circularFieldBound μp μm η 1 0)) := by
  have h1 := ((hp.const_mul 2).add_const 10).norm
  have h2 := ((hm.const_mul 2).add_const 10).norm
  have h3 := ((hp.mul (hp.add_const 10)).sub_const η).norm
  have h4 := ((hm.mul (hm.add_const 10)).sub_const η).norm
  have h5 := (spectralSubunitCoefficient_decay ρ hρ hρ1).comp hmTop
  simpa only [Function.comp_def,circularFieldBound,pow_succ,pow_zero,zero_mul,mul_zero,add_zero]
    using ((((h1.const_add 1).add h2).add h3).add h4).add h5

end DefocusingNLS

end OAI
