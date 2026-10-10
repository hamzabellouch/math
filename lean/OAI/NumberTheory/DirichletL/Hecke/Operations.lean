import OAI.NumberTheory.DirichletL.Hecke.Family
import OAI.NumberTheory.DirichletL.ResidueCharacter

namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

def Character.product (χ ψ : Character) : Character :=
  Character.ofResidue (χ.modulus ⊓ ψ.modulus)
    (Ideal.inf_ne_bot_of_ne_bot χ.modulus_ne_bot ψ.modulus_ne_bot)
    (ResidueCharacter.product χ.modulus ψ.modulus χ.residue ψ.residue)
    (ResidueCharacter.product_global_units _ _ _ _ χ.unit_trivial ψ.unit_trivial)

theorem elementCoeff_product (χ ψ : Character) (z : O) :
    elementCoeff (χ.product ψ) z = elementCoeff χ z * elementCoeff ψ z :=
  ResidueCharacter.product_mk _ _ _ _ z

def Character.inverse (χ : Character) : Character where
  modulus := χ.modulus
  modulus_ne_bot := χ.modulus_ne_bot
  residue := χ.residue⁻¹
  unit_trivial u := by simp [MulChar.inv_apply_eq_inv', χ.unit_trivial]
  period := χ.period
  period_pos := χ.period_pos
  period_mem := χ.period_mem

theorem elementCoeff_inverse (χ : Character) (z : O) :
    elementCoeff χ.inverse z = (elementCoeff χ z)⁻¹ := by
  exact MulChar.inv_apply_eq_inv' _ _

def Character.power (χ : Character) (n : ℕ) : Character where
  modulus := χ.modulus
  modulus_ne_bot := χ.modulus_ne_bot
  residue := χ.residue ^ n
  unit_trivial u := by
    let v := Units.map (Ideal.Quotient.mk χ.modulus).toMonoidHom u
    change (χ.residue ^ n) (v : O ⧸ χ.modulus) = 1
    rw [MulChar.pow_apply_coe]
    change χ.residue (Ideal.Quotient.mk χ.modulus u) ^ n = 1
    simp [χ.unit_trivial]
  period := χ.period
  period_pos := χ.period_pos
  period_mem := χ.period_mem

theorem elementCoeff_power_of_unit (χ : Character) (n : ℕ) (z : O)
    (hz : IsUnit (Ideal.Quotient.mk χ.modulus z)) :
    elementCoeff (χ.power n) z = elementCoeff χ z ^ n := by
  change (χ.residue ^ n) (Ideal.Quotient.mk χ.modulus z) = _
  obtain ⟨u, hu⟩ := hz
  rw [← hu, MulChar.pow_apply_coe, hu]
  rfl

end SevenEighths.HeckeFamily

end

end OAI
