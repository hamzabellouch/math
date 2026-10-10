import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNaturalRadius

namespace OAI

/-! If angular degree plus frequency escapes while their angular ratio stays
bounded, the frequency itself escapes. The alternative is Case I. -/

open Filter Topology
namespace DefocusingNLS

theorem spectral_bounded_ratio_frequency_growth (ell : ℕ → ℕ) (omega : ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hw : ∀ i, 0 ≤ omega i)
    (hratio : ∀ i, ((ell i : ℝ)*(ell i+10))/(1+omega i) ≤ C)
    (hescape : Tendsto (fun i => (ell i : ℝ)+omega i) atTop atTop) :
    Tendsto omega atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hescape.eventually (eventually_ge_atTop (C+(C+1)*b))] with i hi
  have hden : 0 < 1+omega i := by linarith [hw i]
  have hh := (div_le_iff₀ hden).mp (hratio i)
  have hn : 0 ≤ (ell i : ℝ) := Nat.cast_nonneg _
  have hcoeff : 0 < C+1 := by linarith
  nlinarith [sq_nonneg (ell i : ℝ)]

theorem spectral_bounded_ratio_caseII (ell : ℕ → ℕ) (omega : ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hw : Tendsto omega atTop atTop)
    (hratio : ∀ i, ((ell i : ℝ)*(ell i+10))/(1+omega i) ≤ C) :
    ∀ᶠ i in atTop, (ell i : ℝ)*(ell i+10)+99/4 ≤ (2*C+25)*omega i := by
  filter_upwards [hw.eventually (eventually_ge_atTop 1)] with i hi
  have hden : 0 < 1+omega i := by linarith
  have hh := (div_le_iff₀ hden).mp (hratio i)
  nlinarith

end DefocusingNLS

end OAI
