import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveResidueFourier
import OAI.NumberTheory.CubicMoment.Estimates.ResidueGaussianPoisson

namespace OAI

/-! The finite Fourier coefficient occurring in lattice Poisson is exactly
the Gauss transform for the primitive inverse-different additive character. -/
noncomputable section
namespace CubicFirstMoment

lemma residueFiniteFourier_eq_characterFourier {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ) (h : Eisenstein) :
    residueFiniteFourier q χ h =
      residueCharacterFourier q hq χ (Ideal.Quotient.mk (modulus q) h) := by
  unfold residueFiniteFourier residueCharacterFourier gaussSum
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro v _
  apply congrArg (fun z : ℂ => χ v*z)
  rw [AddChar.mulShift_apply]
  have hv : v = Ideal.Quotient.mk (modulus q) (residueRepresentative q v) :=
    (residueRepresentative_spec q v).symm
  conv_rhs => rw [hv,←map_mul,residueFourierChar_mk]
  congr 2
  unfold tracePair
  congr 2
  push_cast
  ring

end CubicFirstMoment

end

end OAI
