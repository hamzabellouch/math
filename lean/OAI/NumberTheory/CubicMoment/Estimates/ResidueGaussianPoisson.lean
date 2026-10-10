import OAI.NumberTheory.CubicMoment.Estimates.GaussianSchwartz
import OAI.NumberTheory.CubicMoment.Estimates.ResidueThetaLattice

namespace OAI

/-! Gaussian specialization of periodic lattice Poisson, retaining the exact
finite Fourier coefficient. Primitivity is only needed when this coefficient
is later evaluated as a Gauss eigenvalue. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def residueFiniteFourier (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (h : Eisenstein) : ℂ :=
  ∑' v : Residues q, χ v *
    (Real.fourierChar (tracePair (residueRepresentative q v : ℂ)
      ((h : ℂ)/((q:ℂ)*traceLambda))) : ℂ)

lemma residueGaussian_poisson {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    residueLatticeTheta q χ A t = (2/(Real.sqrt 3*norm q):ℝ) •
      ∑' h : Eisenstein, residueFiniteFourier q χ h *
        ((Real.pi/(t/A):ℝ)*(Real.exp
          (-4*Real.pi^2/(t/A)*Complex.normSq ((h:ℂ)/((q:ℂ)*traceLambda))):ℝ)) := by
  have hp := poisson_eisenstein_periodic q hq (fun v => χ v)
    (radialGaussianSchwartz (t/A) (div_pos ht hA))
  have he : (fun z : Eisenstein => χ (Ideal.Quotient.mk (modulus q) z)*
      radialGaussianSchwartz (t/A) (div_pos ht hA) (z:ℂ)) =
      fun z => χ (Ideal.Quotient.mk (modulus q) z)*(Real.exp (-norm z*t/A):ℝ) := by
    funext z
    rw [radialGaussianSchwartz_apply,eisenstein_norm_eq_sq]
    apply congrArg (fun r : ℝ => χ (Ideal.Quotient.mk (modulus q) z)*(Real.exp r:ℝ))
    change -(t/A)*‖(z:ℂ)‖^2 = -‖(z:ℂ)‖^2*t/A
    ring
  rw [he] at hp
  simpa only [residueLatticeTheta,residueFiniteFourier,radialGaussianSchwartz_traceFourier] using hp

end CubicFirstMoment

end

end OAI
