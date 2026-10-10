import OAI.Analysis.LipschitzHilbert.Fourier.PlanarSliceFourierDerivative

namespace OAI

/-! The packet spectrum and selector separation in the manuscript,
§2, equations `red:packet-spectra` and `red:selector-assumptions`, give
the actual reference-line annuli used in §5, `conc:main-annuli`.

The only spectral premise is the original planar packet's tilted
wedge and positive vertical band. The same premise suffices for the
first two scaled covariant derivatives. Angular frequencies and
mathlib's cycles-per-unit convention are related explicitly. -/

noncomputable section

open scoped FourierTransform

namespace LipschitzHilbert

private theorem source_frequency_annulus
    {ω η s θ ell w cStar cEta CEta cb Cb : ℝ}
    (hell : 0 < ell) (hw : 0 < w) (hcEta : 0 < cEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hwedge : |ω - (s - θ) * η| ≤ cStar / ell)
    (hband : cEta ≤ w * η ∧ w * η ≤ CEta)
    (hselector : cb * w / ell ≤ |s - θ| ∧ |s - θ| ≤ Cb * w / ell) :
    (cEta * cb - cStar) / ell ≤ |ω| ∧
      |ω| ≤ (CEta * Cb + cStar) / ell := by
  have hη : 0 ≤ η :=
    ((mul_pos_iff_of_pos_left hw).mp (lt_of_lt_of_le hcEta hband.1)).le
  have hlo : cEta * cb ≤ |(s - θ) * η| * ell := by
    rw [abs_mul, abs_of_nonneg hη]
    calc
      cEta * cb = cb * cEta := mul_comm _ _
      _ ≤ cb * (w * η) := mul_le_mul_of_nonneg_left hband.1 hcb
      _ = (cb * w) * η := by ring
      _ ≤ (|s - θ| * ell) * η :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hell).mp hselector.1) hη
      _ = (|s - θ| * η) * ell := by ring
  have hhi : |(s - θ) * η| * ell ≤ CEta * Cb := by
    rw [abs_mul, abs_of_nonneg hη]
    calc
      (|s - θ| * η) * ell = (|s - θ| * ell) * η := by ring
      _ ≤ (Cb * w) * η :=
        mul_le_mul_of_nonneg_right ((le_div_iff₀ hell).mp hselector.2) hη
      _ = Cb * (w * η) := by ring
      _ ≤ Cb * CEta := mul_le_mul_of_nonneg_left hband.2 hCb
      _ = CEta * Cb := mul_comm _ _
  have hwedge' : |ω - (s - θ) * η| * ell ≤ cStar :=
    (le_div_iff₀ hell).mp hwedge
  have hlower := abs_sub_abs_le_abs_sub ((s - θ) * η) ω
  rw [abs_sub_comm] at hlower
  have hupper := abs_sub_abs_le_abs_sub ω ((s - θ) * η)
  have hlower' := mul_le_mul_of_nonneg_right hlower hell.le
  have hupper' := mul_le_mul_of_nonneg_right hupper hell.le
  constructor
  · apply (div_le_iff₀ hell).mpr
    nlinarith
  · apply (le_div_iff₀ hell).mpr
    nlinarith

section Packet

variable (f : SchwartzMap (ℝ × ℝ) ℂ)
  (b s θ ell w cStar cEta CEta cb Cb : ℝ)
  (hell : 0 < ell) (hw : 0 < w) (hcEta : 0 < cEta)
  (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
  (hspectrum : ∀ ξ η, planarAngularFourier f (ξ, η) ≠ 0 →
    |ξ + θ * η| ≤ cStar / ell ∧ cEta ≤ w * η ∧ w * η ≤ CEta)
  (hselector : cb * w / ell ≤ |s - θ| ∧ |s - θ| ≤ Cb * w / ell)

include hell hw hcEta hcb hCb hspectrum hselector in
/-- Exact angular-frequency annulus for an actual affine-line slice. -/
theorem sourcePacket_angular_annulus {ω : ℝ}
    (hω : angularFourier (planarSchwartzSlice f b s) ω ≠ 0) :
    (cEta * cb - cStar) / ell ≤ |ω| ∧
      |ω| ≤ (CEta * Cb + cStar) / ell := by
  by_contra hbound
  apply hω
  apply planarSchwartzSlice_angularFourier_eq_zero
  intro η
  by_contra hnonzero
  have hs := hspectrum (ω - s * η) η hnonzero
  have hwedge : |ω - (s - θ) * η| ≤ cStar / ell := by
    convert hs.1 using 2
    ring
  exact hbound (source_frequency_annulus hell hw hcEta hcb hCb hwedge hs.2 hselector)

include hell hw hcEta hcb hCb hspectrum hselector in
/-- The same annulus, with endpoints converted to mathlib's Fourier
transform convention by division by `2π`. -/
theorem sourcePacket_fourier_annulus {ξ : ℝ}
    (hξ : 𝓕 (planarSchwartzSlice f b s) ξ ≠ 0) :
    (cEta * cb - cStar) / (2 * Real.pi * ell) ≤ |ξ| ∧
      |ξ| ≤ (CEta * Cb + cStar) / (2 * Real.pi * ell) := by
  have hπ : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hcancel : (2 * Real.pi * ξ) / (2 * Real.pi) = ξ := by
    field_simp [Real.pi_ne_zero]
  have hangular : angularFourier (planarSchwartzSlice f b s) (2 * Real.pi * ξ) ≠ 0 := by
    simpa only [SchwartzMap.fourier_coe, angularFourier, hcancel] using hξ
  have h := sourcePacket_angular_annulus f b s θ ell w cStar cEta CEta cb Cb
    hell hw hcEta hcb hCb hspectrum hselector hangular
  simp only [abs_mul, abs_of_pos hπ] at h
  constructor
  · have hl : ((cEta * cb - cStar) / ell) / (2 * Real.pi) ≤ |ξ| :=
      (div_le_iff₀ hπ).mpr (by nlinarith [h.1])
    simpa only [div_div, mul_comm ell (2 * Real.pi)] using hl
  · have hu : |ξ| ≤ ((CEta * Cb + cStar) / ell) / (2 * Real.pi) :=
      (le_div_iff₀ hπ).mpr (by nlinarith [h.2])
    simpa only [div_div, mul_comm ell (2 * Real.pi)] using hu

include hspectrum in
theorem sourcePacket_jet_spectrum (frequency scale : ℝ) (i : Fin 3) :
    ∀ ξ η, planarAngularFourier (planarCovariantJet f frequency scale i) (ξ, η) ≠ 0 →
      |ξ + θ * η| ≤ cStar / ell ∧ cEta ≤ w * η ∧ w * η ≤ CEta := by
  intro ξ η hnonzero
  apply hspectrum ξ η
  intro hzero
  exact hnonzero (planarAngularFourier_covariantJet_eq_zero
    f frequency scale i ξ η hzero)

include hell hw hcEta hcb hCb hspectrum hselector in
/-- All three covariant jets lie in the same actual line annulus;
there is no separate spectral assumption on either derivative. -/
theorem sourcePacket_jet_fourier_annulus (frequency scale : ℝ) (i : Fin 3) {ξ : ℝ}
    (hξ : 𝓕 (planarSchwartzSlice (planarCovariantJet f frequency scale i) b s) ξ ≠ 0) :
    (cEta * cb - cStar) / (2 * Real.pi * ell) ≤ |ξ| ∧
      |ξ| ≤ (CEta * Cb + cStar) / (2 * Real.pi * ell) :=
  sourcePacket_fourier_annulus (planarCovariantJet f frequency scale i)
    b s θ ell w cStar cEta CEta cb Cb hell hw hcEta hcb hCb
    (sourcePacket_jet_spectrum f θ ell w cStar cEta CEta hspectrum frequency scale i)
    hselector hξ

include hell hw hcEta hcb hCb hspectrum hselector in
theorem sourcePacket_jet_fourier_cutoffs (frequency scale : ℝ) (i : Fin 3) :
    (∀ ξ, |ξ| < (cEta * cb - cStar) / (2 * Real.pi * ell) →
      𝓕 (planarSchwartzSlice (planarCovariantJet f frequency scale i) b s) ξ = 0) ∧
    (∀ ξ, (CEta * Cb + cStar) / (2 * Real.pi * ell) < |ξ| →
      𝓕 (planarSchwartzSlice (planarCovariantJet f frequency scale i) b s) ξ = 0) := by
  constructor
  · intro ξ hξ
    by_contra hnonzero
    exact (not_le_of_gt hξ) (sourcePacket_jet_fourier_annulus
      f b s θ ell w cStar cEta CEta cb Cb hell hw hcEta hcb hCb hspectrum hselector
      frequency scale i hnonzero).1
  · intro ξ hξ
    by_contra hnonzero
    exact (not_le_of_gt hξ) (sourcePacket_jet_fourier_annulus
      f b s θ ell w cStar cEta CEta cb Cb hell hw hcEta hcb hCb hspectrum hselector
      frequency scale i hnonzero).2

end Packet

/-- The prescribed small bandwidth makes the lower annulus endpoint
strictly positive, as required by the annular-variation theorem. -/
theorem sourcePacket_annulus_inner_pos {ell cStar cEta cb : ℝ}
    (hell : 0 < ell) (hgap : cStar < cEta * cb) :
    0 < (cEta * cb - cStar) / (2 * Real.pi * ell) :=
  div_pos (sub_pos.mpr hgap) (mul_pos (mul_pos (by norm_num) Real.pi_pos) hell)

theorem sourcePacket_annulus_outer_nonneg {ell cStar CEta Cb : ℝ}
    (hell : 0 < ell) (hcStar : 0 ≤ cStar) (hCEta : 0 ≤ CEta) (hCb : 0 ≤ Cb) :
    0 ≤ (CEta * Cb + cStar) / (2 * Real.pi * ell) :=
  div_nonneg (add_nonneg (mul_nonneg hCEta hCb) hcStar)
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) hell).le

end LipschitzHilbert

end

end OAI
