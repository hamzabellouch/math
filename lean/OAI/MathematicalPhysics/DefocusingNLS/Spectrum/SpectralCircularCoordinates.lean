import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorPropagator
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace OAI

/-! Exact slow/fast coordinates for the circular spectral equation.

The choice has leading eigenvectors (1,0) and (1,-hi/2), as in the
proof of spectrum.tex, Lemma spec:slow-basis. No asymptotic assertion
is assumed in these coordinate identities.
-/

namespace DefocusingNLS

noncomputable def spectralCircularNu (h : ℂ) (a b : ℝ) (lam : ℂ) : ℂ :=
  -2*((a : ℂ)+lam)+2*h*Complex.I*(b : ℂ)

noncomputable def spectralCircularFast (h : ℂ) (u' : ℝ → ℂ) (r : ℝ) : ℂ :=
  2*h*Complex.I*(u' r/(r : ℂ))

noncomputable def spectralCircularSlow (h : ℂ) (u u' : ℝ → ℂ) (r : ℝ) : ℂ :=
  u r-spectralCircularFast h u' r

theorem spectralCircular_reconstruct (h : ℂ) (hh : h^2=1)
    (u u' : ℝ → ℂ) (r : ℝ) (hr : r≠0) :
    spectralCircularSlow h u u' r+spectralCircularFast h u' r=u r ∧
      -(h*Complex.I*(r : ℂ)/2)*spectralCircularFast h u' r=u' r := by
  constructor
  · unfold spectralCircularSlow
    ring
  · have hrC : (r : ℂ)≠0 := by exact_mod_cast hr
    unfold spectralCircularFast
    field_simp [hrC]
    ring_nf
    simp only [hh,Complex.I_sq]
    ring

theorem spectralCircular_coordinate_derivatives (h : ℂ) (hh : h^2=1)
    (a b η : ℝ) (lam : ℂ) (u u' : ℝ → ℂ) (r : ℝ) (hr : r≠0) (u'' F : ℂ)
    (hu : HasDerivAt u (u' r) r) (hu' : HasDerivAt u' u'' r)
    (hODE : u''+(11/(r : ℂ)+h*Complex.I*(r : ℂ)/2)*u' r+
      ((b : ℂ)+h*Complex.I*((a : ℂ)+lam)-(η : ℂ)/(r : ℂ)^2)*u r=F) :
    HasDerivAt (spectralCircularSlow h u u')
      ((spectralCircularNu h a b lam*spectralCircularSlow h u u' r+
        (12+spectralCircularNu h a b lam)*spectralCircularFast h u' r-
        2*h*Complex.I*((η : ℂ)/(r : ℂ)^2*u r+F))/(r : ℂ)) r ∧
    HasDerivAt (spectralCircularFast h u')
      (((-h*Complex.I*(r : ℂ)^2/2-12-spectralCircularNu h a b lam)*
          spectralCircularFast h u' r-
        spectralCircularNu h a b lam*spectralCircularSlow h u u' r+
        2*h*Complex.I*((η : ℂ)/(r : ℂ)^2*u r+F))/(r : ℂ)) r := by
  have hrC : (r : ℂ)≠0 := by exact_mod_cast hr
  have hA : u''=F-(11/(r : ℂ)+h*Complex.I*(r : ℂ)/2)*u' r-
      ((b : ℂ)+h*Complex.I*((a : ℂ)+lam)-(η : ℂ)/(r : ℂ)^2)*u r := by
    linear_combination hODE
  have hfast := (hu'.div (hasDerivAt_id r).ofReal_comp hrC).const_mul (2*h*Complex.I)
  have hslow := hu.sub hfast
  constructor
  · apply hslow.congr_deriv
    rw [hA]
    unfold spectralCircularNu spectralCircularSlow spectralCircularFast
    simp only [id_eq,Complex.ofReal_one]
    field_simp [hrC]
    ring_nf
    simp only [hh,Complex.I_sq]
    ring
  · apply hfast.congr_deriv
    rw [hA]
    unfold spectralCircularNu spectralCircularSlow spectralCircularFast
    simp only [id_eq,Complex.ofReal_one]
    field_simp [hrC]
    ring_nf
    simp only [hh,Complex.I_sq]
    ring

end DefocusingNLS

end OAI
