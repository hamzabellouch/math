import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeODEUniqueness
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeCoreBoundary

namespace OAI

/-! The certified H columns solve exactly the physical free system. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralFreePositivePhysical (ell : ℕ) (b : ℝ) (ζ : ℂ) (r : ℝ) : E₄ :=
  (spectralPhysicalJet ((ell : ℂ)-2*spectralQ ell 1 b ζ)
    (spectralFreeSlowJet (spectralQ ell 1 b ζ) (ell+6)) r,0)

noncomputable def spectralFreeNegativePhysical (ell : ℕ) (b : ℝ) (ζ : ℂ) (r : ℝ) : E₄ :=
  (0,star (spectralPhysicalJet ((ell : ℂ)-2*star (spectralQ ell (-1) b ζ))
    (spectralFreeSlowJet (star (spectralQ ell (-1) b ζ)) (ell+6)) r))

theorem spectralFreeNegativePhysical_eq (ell : ℕ) (b : ℝ) (ζ : ℂ) (r : ℝ) :
    spectralFreeNegativePhysical ell b ζ r=
      (0,spectralPhysicalJet ((ell : ℂ)-2*spectralQ ell (-1) b ζ)
        (fun t => (spectralFreeSecondColumn ell (spectralQ ell (-1) b ζ) t).2) r) := by
  unfold spectralFreeNegativePhysical
  rw [← spectralPhysicalJet_star]
  congr 2
  simp

theorem spectralFreePositivePhysical_hasDerivAt (ell : ℕ) (b : ℝ) (ζ : ℂ)
    (hζ : -(1/32 : ℝ) ≤ ζ.re) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (spectralFreePositivePhysical ell b ζ)
      (spectralFreePhysicalPairField b ζ ((ell : ℂ)*((ell : ℂ)+10)) r
        (spectralFreePositivePhysical ell b ζ r)) r := by
  have hq : -1 < (spectralQ ell 1 b ζ).re := by
    rw [spectralQ_re]
    linarith [Nat.cast_nonneg (α := ℝ) ell]
  have he : -Complex.I*((ell : ℂ)-2*spectralQ ell 1 b ζ)/2=(b : ℂ)+Complex.I*ζ := by
    unfold spectralQ
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hd := (spectralFreeAngularPhysical_hasDerivAt ell (spectralQ ell 1 b ζ) hq r hr).prodMk
    (hasDerivAt_const r (0 : ℂ × ℂ))
  apply hd.congr_deriv
  apply Prod.ext <;> apply Prod.ext
  · rfl
  · simp only [spectralFreePhysicalPairField,spectralFreePhysicalField,spectralFreePositivePhysical,
      one_mul,he]
    push_cast
    ring
  · simp [spectralFreePhysicalPairField,spectralFreePhysicalField,spectralFreePositivePhysical]
  · simp [spectralFreePhysicalPairField,spectralFreePhysicalField,spectralFreePositivePhysical]

theorem spectralFreeNegativePhysical_hasDerivAt (ell : ℕ) (b : ℝ) (ζ : ℂ)
    (hζ : -(1/32 : ℝ) ≤ ζ.re) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (spectralFreeNegativePhysical ell b ζ)
      (spectralFreePhysicalPairField b ζ ((ell : ℂ)*((ell : ℂ)+10)) r
        (spectralFreeNegativePhysical ell b ζ r)) r := by
  have hq : -1 < (star (spectralQ ell (-1) b ζ)).re := by
    simp only [Complex.star_def,Complex.conj_re,spectralQ_re]
    linarith [Nat.cast_nonneg (α := ℝ) ell]
  have he : Complex.I*((ell : ℂ)-2*spectralQ ell (-1) b ζ)/2=(b : ℂ)-Complex.I*ζ := by
    unfold spectralQ
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hk : star (11/(r : ℂ)+Complex.I*(r : ℂ)/2)=11/(r : ℂ)-Complex.I*(r : ℂ)/2 := by
    simp [sub_eq_add_neg,neg_div]
  have hc : star (-Complex.I*((ell : ℂ)-2*star (spectralQ ell (-1) b ζ))/2-
      ((ell*(ell+10) : ℕ) : ℂ)/(r : ℂ)^2)=
      (b : ℂ)-Complex.I*ζ-(ell : ℂ)*((ell : ℂ)+10)/(r : ℂ)^2 := by
    calc
      _ = Complex.I*((ell : ℂ)-2*spectralQ ell (-1) b ζ)/2-
          ((ell*(ell+10) : ℕ) : ℂ)/(r : ℂ)^2 := by simp
      _ = _ := by rw [he]; push_cast; ring
  have hd := (hasDerivAt_const r (0 : ℂ × ℂ)).prodMk
    (spectralFreeAngularPhysical_hasDerivAt ell (star (spectralQ ell (-1) b ζ)) hq r hr).star
  apply hd.congr_deriv
  apply Prod.ext <;> apply Prod.ext
  · simp [spectralFreePhysicalPairField,spectralFreePhysicalField,spectralFreeNegativePhysical]
  · simp [spectralFreePhysicalPairField,spectralFreePhysicalField,spectralFreeNegativePhysical]
  · rfl
  · dsimp only [spectralFreePhysicalPairField,spectralFreePhysicalField,spectralFreeNegativePhysical,
      Prod.star_def]
    rw [star_sub,star_mul,star_mul,star_neg,hk,hc]
    ring

end DefocusingNLS

end OAI
