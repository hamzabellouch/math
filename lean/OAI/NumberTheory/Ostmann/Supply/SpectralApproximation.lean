import OAI.NumberTheory.Ostmann.Supply.SpectralProjection

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]
local notation "H" => EuclideanSpace ℂ (ZMod p)

def normalizedVector (S : Finset (ZMod p)) : H :=
  WithLp.toLp 2 (fun x => (normalizedIndicator S x : ℂ))

@[simp] theorem normalizedVector_apply (S : Finset (ZMod p)) (x : ZMod p) :
    normalizedVector S x = (normalizedIndicator S x : ℂ) := rfl

theorem spectralProjection_norm_sq (E : Finset (ZMod p)) (f : H) :
    ‖spectralProjection E f‖^2 = ∑ v ∈ E, ‖unitaryDFT f v‖^2 := by
  rw [← fourierEquiv.norm_map (spectralProjection E f), PiLp.norm_sq_eq_of_L2]
  simp only [fourierEquiv_apply, spectralProjection_fourier,
    apply_ite, norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_ite_mem, Finset.univ_inter]

theorem spectralProjection_error_sq (E : Finset (ZMod p)) (f : H) :
    ‖spectralProjection E f-f‖^2 = ∑ v ∈ Eᶜ, ‖unitaryDFT f v‖^2 := by
  rw [← fourierEquiv.norm_map (spectralProjection E f-f), PiLp.norm_sq_eq_of_L2]
  simp only [map_sub, PiLp.sub_apply, fourierEquiv_apply, spectralProjection_fourier]
  calc
    _ = ∑ v : ZMod p, if v ∈ Eᶜ then ‖unitaryDFT f v‖^2 else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hh : v ∈ E <;> simp [hh]
    _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem normalizedVector_norm_sq (S : Finset (ZMod p))
    (hpos : 0 < density S) (hlt : density S < 1) :
    ‖normalizedVector S‖^2 = p := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [normalizedVector_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simpa only [ZMod.card] using sum_normalizedIndicator_sq S hpos hlt

theorem sparse_projection_error_sq_le (S : Finset (ZMod p)) :
    ‖spectralProjection (largeSpectrum S) (normalizedVector S)-normalizedVector S‖^2 ≤
      gamma S*p := by
  rw [spectralProjection_error_sq]
  exact largeSpectrum_energy_le_complement S

theorem sparse_projection_error_le (S : Finset (ZMod p)) {ε : ℝ}
    (hε : 0 ≤ ε) (hg : gamma S ≤ ε^2) :
    ‖spectralProjection (largeSpectrum S) (normalizedVector S)-normalizedVector S‖ ≤
      ε*Real.sqrt p := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg p : (0:ℝ)≤p)
  have h := (sparse_projection_error_sq_le S).trans
    (mul_le_mul_of_nonneg_right hg (Nat.cast_nonneg _))
  have hn := norm_nonneg (spectralProjection (largeSpectrum S) (normalizedVector S)-normalizedVector S)
  have hprod := mul_nonneg hε (Real.sqrt_nonneg (p:ℝ))
  nlinarith

theorem sparse_projection_energy_ge (S : Finset (ZMod p))
    (hpos : 0 < density S) (hlt : density S < 1) :
    (1-gamma S)*p ≤ ‖spectralProjection (largeSpectrum S) (normalizedVector S)‖^2 := by
  rw [spectralProjection_norm_sq]
  exact largeSpectrum_energy_ge S hpos hlt

end Ostmann.Supply

end

end OAI
