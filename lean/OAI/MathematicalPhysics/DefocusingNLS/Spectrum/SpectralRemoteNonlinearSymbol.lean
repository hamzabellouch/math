import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteFamilyComposition
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationSubunit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialEquation

namespace OAI

/-! Uniform symbols for both circular components of the odd-power derivative
on a strictly subunit profile family. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

noncomputable def spectralRemoteDiagonalPart : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1/2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ 1) -
    Complex.I • (ContinuousLinearMap.apply ℝ ℂ Complex.I))

noncomputable def spectralRemoteCrossPart : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1/2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ 1) +
    Complex.I • (ContinuousLinearMap.apply ℝ ℂ Complex.I))

theorem spectralRemote_circular_parts (m : ℕ) (z : ℂ) :
    spectralRemoteDiagonalPart (fderiv ℝ (oddPowerNonlinearity m) z) =
      spectralDiagonalCoefficient m z ∧
    spectralRemoteCrossPart (fderiv ℝ (oddPowerNonlinearity m) z) =
      spectralCrossCoefficient m z := by
  rw [(hasFDerivAt_oddPowerNonlinearity m z).fderiv]
  constructor
  · change (1/2 : ℂ)*(oddPowerDerivative m z 1-Complex.I*oddPowerDerivative m z Complex.I) = _
    rw [spectralCoefficient_decomposition,spectralCoefficient_decomposition]
    simp only [star_one,mul_one,Complex.star_def,Complex.conj_I]
    linear_combination -(spectralDiagonalCoefficient m z-spectralCrossCoefficient m z)/2 * Complex.I_sq
  · change (1/2 : ℂ)*(oddPowerDerivative m z 1+Complex.I*oddPowerDerivative m z Complex.I) = _
    rw [spectralCoefficient_decomposition,spectralCoefficient_decomposition]
    simp only [star_one,mul_one,Complex.star_def,Complex.conj_I]
    linear_combination (spectralDiagonalCoefficient m z-spectralCrossCoefficient m z)/2 * Complex.I_sq

theorem spectralRemote_nonlinear_derivative_symbol
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (q : ℕ → ℝ → ℂ)
    (hq : HasUniformLogJetBound L 0 q) (rho : ℝ) (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (hb : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ‖q n t‖ ≤ rho) :
    HasUniformLogJetBound L 0 (fun n t => fderiv ℝ (oddPowerNonlinearity (m n)) (q n t)) := by
  apply spectralRemote_family_composition hL q
    (fun n => fderiv ℝ (oddPowerNonlinearity (m n))) hq
  · intro n
    exact (contDiff_oddPowerNonlinearity (m n)).fderiv_right (by simp)
  · intro k
    refine ⟨1,zero_le_one,?_⟩
    have hh := hm.eventually (homogeneous_oddPower_derivatives_subunit (k+1) rho hrho hrho1 1 (by norm_num))
    filter_upwards [hh,hb] with n hn hbn
    intro t ht
    rw [norm_iteratedFDeriv_fderiv]
    exact (hn _ (hbn t ht)).le

theorem spectralRemote_nonlinear_circular_symbols
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (q : ℕ → ℝ → ℂ)
    (hq : HasUniformLogJetBound L 0 q) (rho : ℝ) (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (hb : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ‖q n t‖ ≤ rho) :
    HasUniformLogJetBound L 0 (fun n t => spectralDiagonalCoefficient (m n) (q n t)) ∧
    HasUniformLogJetBound L 0 (fun n t => spectralCrossCoefficient (m n) (q n t)) := by
  have hd := spectralRemote_nonlinear_derivative_symbol hL m hm q hq rho hrho hrho1 hb
  constructor
  · simpa only [(spectralRemote_circular_parts _ _).1] using hd.map spectralRemoteDiagonalPart
  · simpa only [(spectralRemote_circular_parts _ _).2] using hd.map spectralRemoteCrossPart

end DefocusingNLS

end OAI
