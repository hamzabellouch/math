import OAI.NumberTheory.Ostmann.Supply.UniformProjection

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]
local notation "H" => EuclideanSpace ℂ (ZMod p)

theorem spectralProjection_inner_projected (E : Finset (ZMod p)) (f g : H) :
    inner ℂ f (spectralProjection E g) =
      inner ℂ (spectralProjection E f) (spectralProjection E g) := by
  change inner ℂ f ((frequencySpace E).starProjection g) =
    inner ℂ ((frequencySpace E).starProjection f) ((frequencySpace E).starProjection g)
  rw [Submodule.inner_starProjection_left_eq_right]
  rw [Submodule.starProjection_eq_self_iff.mpr ((frequencySpace E).starProjection_apply_mem g)]

theorem spectralProjection_scalar (S : Finset (ZMod p))
    (hpos : 0 < density S) (hlt : density S < 1) :
    inner ℂ (uniformVector S) (spectralProjection (largeSpectrum S) (uniformVector Sᶜ)) =
      (-((p:ℝ)⁻¹^2 * ‖spectralProjection (largeSpectrum S) (normalizedVector S)‖^2) : ℝ) := by
  rw [spectralProjection_inner_projected,
    spectralProjection_uniform S hpos hlt, spectralProjection_uniform_compl S hpos hlt,
    inner_smul_left, inner_smul_right]
  have hn (v : H) : inner ℂ v v = (‖v‖^2 : ℝ) := by
    rw [PiLp.inner_apply, PiLp.norm_sq_eq_of_L2]
    simp only [RCLike.inner_apply, Complex.mul_conj', Complex.ofReal_sum, Complex.ofReal_pow]
  rw [hn]
  have hc := congrArg (fun r : ℝ => (r:ℂ)) (uniformCoefficient_mul_compl S hpos hlt)
  push_cast at hc ⊢
  simp only [Complex.conj_ofReal]
  calc
    _ = -((uniformCoefficient S : ℂ)*(uniformCoefficient Sᶜ : ℂ))*
      ((‖spectralProjection (largeSpectrum S) (normalizedVector S)‖:ℂ)^2) := by ring
    _ = _ := by rw [hc]; ring

theorem spectralProjection_scalar_re_le (S : Finset (ZMod p))
    (hpos : 0 < density S) (hlt : density S < 1) :
    (inner ℂ (uniformVector S) (spectralProjection (largeSpectrum S) (uniformVector Sᶜ))).re ≤
      -(1-gamma S)/(p:ℝ) := by
  rw [spectralProjection_scalar S hpos hlt, Complex.ofReal_re]
  have hp : (p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have h := mul_le_mul_of_nonneg_left (sparse_projection_energy_ge S hpos hlt)
    (sq_nonneg (p:ℝ)⁻¹)
  have he : (p:ℝ)⁻¹^2*((1-gamma S)*p) = (1-gamma S)/p := by field_simp
  rw [he] at h
  simpa only [neg_div] using neg_le_neg h

theorem spectralProjection_scalar_norm_le (S : Finset (ZMod p))
    (hpos : 0 < density S) (hlt : density S < 1) :
    ‖inner ℂ (uniformVector S) (spectralProjection (largeSpectrum S) (uniformVector Sᶜ))‖ ≤
      1/(p:ℝ) := by
  rw [spectralProjection_scalar S hpos hlt, Complex.norm_real, Real.norm_eq_abs,
    abs_neg,abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hp : (p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hnorm := (frequencySpace (largeSpectrum S)).norm_starProjection_apply_le (normalizedVector S)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
  rw [normalizedVector_norm_sq S hpos hlt] at hsq
  calc
    _ ≤ (p:ℝ)⁻¹^2*p := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = _ := by field_simp

end Ostmann.Supply

end

end OAI
