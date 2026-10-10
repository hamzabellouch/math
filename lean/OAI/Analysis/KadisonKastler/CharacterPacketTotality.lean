import OAI.Analysis.KadisonKastler.FourierL1Uniqueness
import OAI.Analysis.KadisonKastler.RegularCoreHilbertSum
import OAI.Analysis.KadisonKastler.RegularCoreCharacters

namespace OAI

/-! # Totality of character translates of a nonvanishing scalar packet

Fourier uniqueness proves totality on the actual vector-valued `L²` space.
No countability or pointwise choice of vector representatives is needed.
-/

namespace KadisonKastler

open MeasureTheory FourierTransform

noncomputable section

private theorem fourierChar_eq_star_character (s t : ℝ) :
    (Real.fourierChar (-(t * s)) : ℂ) = star (regularCharacterScalar (2 * Real.pi * s) t) := by
  simp only [Real.fourierChar_apply', regularCharacterScalar, Circle.coe_exp,
    Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every vector orthogonal to all character translates of the packet is zero. -/
theorem eq_zero_of_inner_character_packets
    (φ : RegularCoreHilbert ℂ) (hφ : ∀ᵐ t : ℝ, φ t ≠ 0)
    (g : RegularCoreHilbert H)
    (hg : ∀ s : ℝ, ∀ x : H,
      inner ℂ ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularTensorVector φ x)) g = 0) :
    g = 0 := by
  let f : ℝ → H := fun t => star (φ t) • g t
  have hi : Integrable f :=
    memLp_one_iff_integrable.mp ((Lp.memLp φ).star.smul (Lp.memLp g))
  have hf (s : ℝ) : 𝓕 f s = 0 := by
    apply ext_inner_left ℂ
    intro x
    rw [inner_zero_right, Real.fourier_eq]
    have hconv := (Real.fourierIntegral_convergent_iff s).mpr hi
    change (innerSL ℂ x) (∫ t : ℝ, (Real.fourierChar (-inner ℝ t s) : ℂ) • f t) = 0
    have hconv' : Integrable (fun t : ℝ =>
        (Real.fourierChar (-inner ℝ t s) : ℂ) • f t) := by
      simpa only [Circle.smul_def] using hconv
    rw [← (innerSL ℂ x).integral_comp_comm hconv']
    calc
      _ = inner ℂ ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularTensorVector φ x)) g := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [regularCharacterUnitary_apply_ae (2 * Real.pi * s)
          (regularTensorVector φ x), regularTensorVector_apply_ae φ x] with t ht hx
        rw [ht, hx]
        change inner ℂ x ((Real.fourierChar (-inner ℝ t s) : ℂ) • (star (φ t) • g t)) = _
        simp only [inner_smul_left, inner_smul_right]
        rw [show inner ℝ t s = t * s by simp [RCLike.inner_apply, mul_comm],
          fourierChar_eq_star_character]
        simp only [starRingEnd_apply]
      _ = 0 := hg s x
  have hzero := ae_zero_of_integrable_fourier_zero hi hf
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hzero, hφ] with t ht hne
  change star (φ t) • g t = 0 at ht
  exact (smul_eq_zero.mp ht).resolve_left (star_ne_zero.mpr hne)

end

end KadisonKastler

end OAI
