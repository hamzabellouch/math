import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteCoefficientSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteSymbolFinite

namespace OAI

/-! The normalized angular and imaginary spectral parameters give the
actual two small leading coefficients on the remote half-line. -/

open Set Filter Topology
namespace DefocusingNLS

noncomputable def spectralRemoteLeadingCoefficient (omega eta : ℕ → ℝ) (n : ℕ) (t : ℝ)
    (i : Fin 2) : ℝ :=
  (if i = 0 then 1 else -1)*omega n*Real.exp (-2*t)+eta n*Real.exp (-4*t)

theorem spectralRemote_leading_coefficient_symbol
    {L omega eta : ℕ → ℝ}
    (homega : ∀ᶠ n in atTop, |omega n| *Real.exp (-2*L n) ≤ 1/64)
    (heta : ∀ᶠ n in atTop, |eta n| *Real.exp (-4*L n) ≤ 1/256) :
    HasUniformLogJetBound L 0 (spectralRemoteLeadingCoefficient omega eta) := by
  apply HasUniformLogJetBound.pi
  intro i
  exact spectralRemote_actual_coefficient_symbol _ (by norm_num) (by norm_num) homega heta

theorem spectralRemote_leading_coefficient_small
    {L omega eta : ℕ → ℝ}
    (homega : ∀ᶠ n in atTop, |omega n| *Real.exp (-2*L n) ≤ 1/64)
    (heta : ∀ᶠ n in atTop, |eta n| *Real.exp (-4*L n) ≤ 1/256) :
    ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ i,
      |spectralRemoteLeadingCoefficient omega eta n t i| ≤ 1/32 := by
  filter_upwards [homega,heta] with n hn hn'
  intro t ht i
  change L n < t at ht
  have he2 : Real.exp (-2*t) ≤ Real.exp (-2*L n) :=
    Real.exp_le_exp.mpr (by linarith [ht])
  have he4 : Real.exp (-4*t) ≤ Real.exp (-4*L n) :=
    Real.exp_le_exp.mpr (by linarith [ht])
  have hw : |omega n| *Real.exp (-2*t) ≤ 1/64 :=
    (mul_le_mul_of_nonneg_left he2 (abs_nonneg _)).trans hn
  have he : |eta n| *Real.exp (-4*t) ≤ 1/256 :=
    (mul_le_mul_of_nonneg_left he4 (abs_nonneg _)).trans hn'
  have hs : |(if i = 0 then 1 else -1 : ℝ)| = 1 := by split_ifs <;> norm_num
  calc
    _ ≤ |(if i = 0 then 1 else -1 : ℝ)*omega n*Real.exp (-2*t)|+
        |eta n*Real.exp (-4*t)| := abs_add_le _ _
    _ = |omega n| *Real.exp (-2*t)+|eta n| *Real.exp (-4*t) := by
      simp only [abs_mul,hs,one_mul,abs_of_pos (Real.exp_pos _)]
    _ ≤ 1/32 := by linarith

end DefocusingNLS

end OAI
