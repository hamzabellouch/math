import OAI.NumberTheory.Ostmann.Characters.CharacterRootNumberBound
import OAI.NumberTheory.Ostmann.Characters.PrimitiveGaussFourier

namespace OAI

/-! # The exact modulus of the primitive character root number -/

namespace Ostmann

open Complex
open scoped Classical

 theorem PrimitiveComplexCharacter.rootNumber_norm_eq_one (χ : PrimitiveComplexCharacter) :
    ‖@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character‖ = 1 := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hq : (0 : ℝ) < χ.modulus := by exact_mod_cast χ.positive
  have hn : ‖(χ.modulus : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt χ.modulus := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq]
    norm_num only [div_ofNat_re, one_re]
    exact (Real.sqrt_eq_rpow _).symm
  have hG : ‖gaussSum χ.character ZMod.stdAddChar‖ = Real.sqrt χ.modulus := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [primitive_gauss_norm_sq χ.character χ.primitive, Real.sq_sqrt hq.le]
  simp only [DirichletCharacter.rootNumber, norm_div, norm_pow, norm_I, one_pow, div_one, hn, hG]
  exact div_self (Real.sqrt_pos.mpr hq).ne'

end Ostmann

end OAI
