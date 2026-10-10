import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolarDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeInitialField

namespace OAI

/-! A local first-order polar jet, requiring regularity only at the point in question. -/

namespace DefocusingNLS

noncomputable def radialPolarSlope (A D v φ : ℝ → ℝ) (r : ℝ) : ℂ :=
  ((D r : ℂ)+Complex.I*(A r : ℂ)*(v r : ℂ))*Complex.exp (Complex.I*(φ r : ℂ))

theorem radialPolarJet_hasDerivAt (A D v φ : ℝ → ℝ) (r : ℝ)
    (hA : HasDerivAt A (D r) r) (hφ : HasDerivAt φ (v r) r) :
    HasDerivAt (radialPolar A φ) (radialPolarSlope A D v φ r) r := by
  have he := ((hφ.ofReal_comp.const_mul Complex.I).cexp)
  convert hA.ofReal_comp.mul he using 1
  · rfl
  · dsimp [radialPolarSlope]
    ring

theorem radialPolarJet_free (A D v φ : ℝ → ℝ) (r b d₁ v₁ : ℝ)
    (hA : HasDerivAt A (D r) r) (hD : HasDerivAt D d₁ r)
    (hφ : HasDerivAt φ (v r) r) (hv : HasDerivAt v v₁ r)
    (hRe : d₁+11/r*D r-A r*(v r)^2-r/2*A r*v r+b*A r=0)
    (hIm : 2*D r*v r+A r*v₁+11/r*A r*v r+r/2*D r=0) :
    HasDerivAt (radialPolarSlope A D v φ)
      (-radialFreeCoefficient r*radialPolarSlope A D v φ r-(b : ℂ)*radialPolar A φ r) r := by
  have he := ((hφ.ofReal_comp.const_mul Complex.I).cexp)
  have hZ := hD.ofReal_comp.add ((hA.ofReal_comp.const_mul Complex.I).mul hv.ofReal_comp)
  have hjet := hZ.mul he
  have hReC := congrArg (fun x : ℝ => (x : ℂ)) hRe
  have hImC := congrArg (fun x : ℝ => (x : ℂ)) hIm
  convert hjet using 1
  · rfl
  · dsimp [radialPolar,radialPolarSlope,radialFreeCoefficient]
    push_cast at hReC hImC ⊢
    linear_combination -(Complex.exp (Complex.I*(φ r : ℂ)))*hReC-
      Complex.I*Complex.exp (Complex.I*(φ r : ℂ))*hImC-
      (A r : ℂ)*(v r : ℂ)^2*Complex.exp (Complex.I*(φ r : ℂ))*Complex.I_sq-
      ((r : ℂ)/2)*(A r : ℂ)*(v r : ℂ)*Complex.exp (Complex.I*(φ r : ℂ))*Complex.I_sq

end DefocusingNLS

end OAI
