import OAI.Analysis.LipschitzHilbert.Fourier.PlanarSliceFourier

namespace OAI

/-! Spectral rectangles and annular bounds for actual planar Schwartz
restrictions, using the proved fiber-vanishing identity. Frequencies use
the `exp(-2πi xξ)` convention throughout. -/

noncomputable section

open scoped FourierTransform

namespace LipschitzHilbert

private theorem frequency_rectangle_bound {ξ η θ η₀ s δ ε : ℝ}
    (hh : |ξ + θ * η| ≤ δ) (hv : |η - η₀| ≤ ε) :
    |ξ + s * η - η₀ * (s - θ)| ≤ δ + ε * |s - θ| := by
  have hid : ξ + s * η - η₀ * (s - θ) = (ξ + θ * η) + (η - η₀) * (s - θ) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hh (by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hv (abs_nonneg _)))

/-- The packet spectral rectangle projects to the expected carrier
interval on every affine reference line. -/
theorem planarSchwartzSlice_fourier_carrier_bound
    (f : SchwartzMap (ℝ × ℝ) ℂ) (b s θ η₀ δ ε : ℝ)
    (hspectrum : ∀ ξ η, planarFourier f (ξ, η) ≠ 0 →
      |ξ + θ * η| ≤ δ ∧ |η - η₀| ≤ ε)
    {ω : ℝ} (hω : 𝓕 (planarSchwartzSlice f b s) ω ≠ 0) :
    |ω - η₀ * (s - θ)| ≤ δ + ε * |s - θ| := by
  by_contra hbound
  apply hω
  apply planarSchwartzSlice_fourier_eq_zero
  intro η
  by_contra hnonzero
  have hs := hspectrum (ω - s * η) η hnonzero
  have h := frequency_rectangle_bound (s := s) hs.1 hs.2
  have hid : ω - s * η + s * η - η₀ * (s - θ) = ω - η₀ * (s - θ) := by ring
  rw [hid] at h
  exact hbound h

theorem planarSchwartzSlice_support_carrier_interval
    (f : SchwartzMap (ℝ × ℝ) ℂ) (b s θ η₀ δ ε : ℝ)
    (hspectrum : ∀ ξ η, planarFourier f (ξ, η) ≠ 0 →
      |ξ + θ * η| ≤ δ ∧ |η - η₀| ≤ ε) :
    Function.support (𝓕 ((planarSchwartzSlice f b s) : ℝ → ℂ)) ⊆
      Set.Icc (η₀ * (s - θ) - (δ + ε * |s - θ|))
        (η₀ * (s - θ) + (δ + ε * |s - θ|)) := by
  intro ω hω
  have h := planarSchwartzSlice_fourier_carrier_bound f b s θ η₀ δ ε hspectrum hω
  rcases abs_le.mp h with ⟨hl, hu⟩
  exact ⟨by linarith, by linarith⟩

theorem planarSchwartzSlice_tsupport_carrier_interval
    (f : SchwartzMap (ℝ × ℝ) ℂ) (b s θ η₀ δ ε : ℝ)
    (hspectrum : ∀ ξ η, planarFourier f (ξ, η) ≠ 0 →
      |ξ + θ * η| ≤ δ ∧ |η - η₀| ≤ ε) :
    tsupport (𝓕 ((planarSchwartzSlice f b s) : ℝ → ℂ)) ⊆
      Set.Icc (η₀ * (s - θ) - (δ + ε * |s - θ|))
        (η₀ * (s - θ) + (δ + ε * |s - θ|)) :=
  closure_minimal (planarSchwartzSlice_support_carrier_interval f b s θ η₀ δ ε hspectrum)
    isClosed_Icc

/-- Separating the carrier from zero turns the carrier interval into an
annulus; the constants are retained exactly for subsequent rescaling. -/
theorem planarSchwartzSlice_fourier_annulus
    (f : SchwartzMap (ℝ × ℝ) ℂ) (b s θ η₀ δ ε : ℝ)
    (hspectrum : ∀ ξ η, planarFourier f (ξ, η) ≠ 0 →
      |ξ + θ * η| ≤ δ ∧ |η - η₀| ≤ ε)
    {a A : ℝ} (hlower : a ≤ |η₀ * (s - θ)| - (δ + ε * |s - θ|))
    (hupper : |η₀ * (s - θ)| + (δ + ε * |s - θ|) ≤ A)
    {ω : ℝ} (hω : 𝓕 (planarSchwartzSlice f b s) ω ≠ 0) :
    a ≤ |ω| ∧ |ω| ≤ A := by
  have h := planarSchwartzSlice_fourier_carrier_bound f b s θ η₀ δ ε hspectrum hω
  have hlo := abs_sub_abs_le_abs_sub (η₀ * (s - θ)) ω
  rw [abs_sub_comm] at hlo
  have hhi := abs_sub_abs_le_abs_sub ω (η₀ * (s - θ))
  constructor <;> linarith

end LipschitzHilbert

end

end OAI
