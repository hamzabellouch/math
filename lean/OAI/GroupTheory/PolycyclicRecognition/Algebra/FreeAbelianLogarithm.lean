import OAI.GroupTheory.PolycyclicRecognition.Algebra.TorsionFreeAbelianRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ComplexSquareLogarithm
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Module.LinearMap.Defs

namespace OAI

/-! # Compatible logarithms of characters of free abelian groups

Choosing logarithms only on a basis preserves all multiplicative relations.
-/

noncomputable section
namespace PolycyclicRecognition

def complexUnitExp : Multiplicative ℂ →* ℂˣ := Complex.expMonoidHom.toHomUnits

@[simp] theorem complexUnitExp_val (z : Multiplicative ℂ) :
    (complexUnitExp z : ℂ) = Complex.exp z.toAdd := rfl

def freeAbelianLogarithm {n : ℕ} (ρ : IntegralLatticeGroup n →* ℂˣ) :
    IntegralLatticeGroup n →* Multiplicative ℂ := by
  let f := (Pi.basisFun ℤ (Fin n)).constr ℤ
    (fun i => Complex.log (ρ (Multiplicative.ofAdd ((Pi.basisFun ℤ (Fin n)) i)) : ℂ))
  exact f.toAddMonoidHom.toMultiplicative

theorem freeAbelianLogarithm_exp {n : ℕ} (ρ : IntegralLatticeGroup n →* ℂˣ) :
    complexUnitExp.comp (freeAbelianLogarithm ρ) = ρ := by
  let f := ((Pi.basisFun ℤ (Fin n)).constr ℤ
    (fun i => Complex.log (ρ (Multiplicative.ofAdd ((Pi.basisFun ℤ (Fin n)) i)) : ℂ)))
  have he : (complexUnitExp.toAdditive.toIntLinearMap).comp f =
      ρ.toAdditive.toIntLinearMap := by
    apply (Pi.basisFun ℤ (Fin n)).ext
    intro i
    erw [LinearMap.comp_apply]
    change complexUnitExp (Multiplicative.ofAdd (f ((Pi.basisFun ℤ (Fin n)) i))) = _
    rw [Module.Basis.constr_basis]
    apply Units.ext
    exact Complex.exp_log (Units.ne_zero _)
  apply MonoidHom.ext
  intro x
  exact DFunLike.congr_fun he x.toAdd

end PolycyclicRecognition

end

end OAI
