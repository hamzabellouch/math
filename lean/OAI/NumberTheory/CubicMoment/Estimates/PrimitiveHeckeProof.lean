import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveResidueConductorKernel
import OAI.NumberTheory.CubicMoment.Estimates.ResidueFourierBridge
import OAI.NumberTheory.CubicMoment.Estimates.ResidueHeckeFromFourier
import OAI.NumberTheory.CubicMoment.Angular.AngularHeckeFromFourier

namespace OAI

/-! Primitive finite and fixed-angular Hecke continuation derived from
finite Gauss orthogonality and the actual Gaussian Poisson formula. -/
noncomputable section
namespace CubicFirstMoment

private lemma primitive_poisson_gauss_norm {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hp : PrimitiveResidueCharacter q χ) :
    ‖gaussSum χ (residueFourierChar q hq)‖ = Real.sqrt (norm q) := by
  simpa only [normNat_cast] using primitiveResidueGauss_norm hq χ hp

private lemma primitive_poisson_gauss_fourier {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hp : PrimitiveResidueCharacter q χ) (h : Eisenstein) :
    residueFiniteFourier q χ h =
      gaussSum χ (residueFourierChar q hq)*(star χ) (Ideal.Quotient.mk (modulus q) h) := by
  rw [residueFiniteFourier_eq_characterFourier hq χ h,primitiveResidueFourier_eq hq χ hp,mul_comm]

theorem primitiveResidueHeckeInput_proved : PrimitiveResidueHeckeInput := by
  intro q hq χ hp hn hu
  let : Finite (Residues q) := finite_residues hq
  let : Fintype (Residues q) := Fintype.ofFinite _
  exact residueHecke_from_finiteFourier hq χ hn hu
    (gaussSum χ (residueFourierChar q hq)) (primitive_poisson_gauss_norm hq χ hp)
    (primitive_poisson_gauss_fourier hq χ hp)

theorem primitiveAngularHeckeInput_proved : PrimitiveAngularHeckeInput := by
  intro ℓ q hq χ hp hu hn
  let : Finite (Residues q) := finite_residues hq
  let : Fintype (Residues q) := Fintype.ofFinite _
  exact angularHecke_from_finiteFourier hq χ ℓ hu hn
    (gaussSum χ (residueFourierChar q hq)) (primitive_poisson_gauss_norm hq χ hp)
    (primitive_poisson_gauss_fourier hq χ hp)

end CubicFirstMoment

end

end OAI
