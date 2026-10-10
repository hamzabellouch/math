import OAI.NumberTheory.CubicMoment.Estimates.AntiHarmonicGaussian
import OAI.NumberTheory.CubicMoment.Estimates.ResidueGaussianScale

namespace OAI

/-! Periodic Poisson for the actual positive and negative angular
polynomial Gaussians. The finite Fourier coefficient is retained exactly. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def residueHarmonicTheta (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (A : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ∑' z : Eisenstein, χ (Ideal.Quotient.mk (modulus q) z)*
    ((z:ℂ)^n*(Real.exp (-norm z*t/A):ℝ))

def residueAntiHarmonicTheta (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (A : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ∑' z : Eisenstein, χ (Ideal.Quotient.mk (modulus q) z)*
    ((star (z:ℂ))^n*(Real.exp (-norm z*t/A):ℝ))

lemma residueHarmonic_poisson {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) {A t : ℝ} (hA : 0 < A) (ht : 0 < t) (n : ℕ) :
    residueHarmonicTheta q χ A n t = (2/(Real.sqrt 3*norm q):ℝ) •
      ∑' h : Eisenstein, residueFiniteFourier q χ h *
        ((-2*(Real.pi:ℂ)*Complex.I/(t/A:ℝ))^n*
          (star ((h:ℂ)/((q:ℂ)*traceLambda)))^n*(Real.pi/(t/A):ℝ)*
          (Real.exp (-4*Real.pi^2/(t/A)*Complex.normSq ((h:ℂ)/((q:ℂ)*traceLambda))):ℝ)) := by
  have hp := poisson_eisenstein_periodic q hq (fun v => χ v)
    (harmonicGaussian (t/A) (div_pos ht hA) n)
  have he : (fun z : Eisenstein => χ (Ideal.Quotient.mk (modulus q) z)*
      harmonicGaussian (t/A) (div_pos ht hA) n (z:ℂ)) =
      fun z => χ (Ideal.Quotient.mk (modulus q) z)*
        ((z:ℂ)^n*(Real.exp (-norm z*t/A):ℝ)) := by
    funext z
    rw [harmonicGaussian_apply]
    unfold radialGaussian
    rw [eisenstein_norm_eq_sq]
    have hx : -(t/A)*‖(z:ℂ)‖^2 = -‖(z:ℂ)‖^2*t/A := by ring
    rw [hx]
    rfl
  rw [he] at hp
  simpa only [residueHarmonicTheta,residueFiniteFourier,harmonicGaussian_traceFourier] using hp

lemma residueAntiHarmonic_poisson {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) {A t : ℝ} (hA : 0 < A) (ht : 0 < t) (n : ℕ) :
    residueAntiHarmonicTheta q χ A n t = (2/(Real.sqrt 3*norm q):ℝ) •
      ∑' h : Eisenstein, residueFiniteFourier q χ h *
        ((-2*(Real.pi:ℂ)*Complex.I/(t/A:ℝ))^n*
          ((h:ℂ)/((q:ℂ)*traceLambda))^n*(Real.pi/(t/A):ℝ)*
          (Real.exp (-4*Real.pi^2/(t/A)*Complex.normSq ((h:ℂ)/((q:ℂ)*traceLambda))):ℝ)) := by
  have hp := poisson_eisenstein_periodic q hq (fun v => χ v)
    (antiHarmonicGaussian (t/A) (div_pos ht hA) n)
  have he : (fun z : Eisenstein => χ (Ideal.Quotient.mk (modulus q) z)*
      antiHarmonicGaussian (t/A) (div_pos ht hA) n (z:ℂ)) =
      fun z => χ (Ideal.Quotient.mk (modulus q) z)*
        ((star (z:ℂ))^n*(Real.exp (-norm z*t/A):ℝ)) := by
    funext z
    rw [antiHarmonicGaussian_apply]
    unfold radialGaussian
    rw [eisenstein_norm_eq_sq]
    have hx : -(t/A)*‖(z:ℂ)‖^2 = -‖(z:ℂ)‖^2*t/A := by ring
    rw [hx]
    rfl
  rw [he] at hp
  simpa only [residueAntiHarmonicTheta,residueFiniteFourier,antiHarmonicGaussian_traceFourier] using hp

end CubicFirstMoment

end

end OAI
