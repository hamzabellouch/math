import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeConjugation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexPointMeasure
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAutomorphicSections

namespace OAI

/-! Dilation by a cubed prime pulls an original section to a genuine
section on the integral cubed-prime subgroup, with the same multiplier. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeSections (p : Eisenstein) : Submodule ℂ C(CubicThetaPoint,ℂ) where
  carrier := {F | ∀ g : cubicThetaPrimeIwahori (p^3), ∀ x : CubicThetaPoint,
    F (g.val • x)=cubicThetaKubotaValue g.val*F x}
  zero_mem' := by simp
  add_mem' := by
    intro F G hF hG g x
    change F (g.val • x)+G (g.val • x)=cubicThetaKubotaValue g.val*(F x+G x)
    rw [hF,hG]
    ring
  smul_mem' := by
    intro c F hF g x
    change c*F (g.val • x)=cubicThetaKubotaValue g.val*(c*F x)
    rw [hF]
    ring

def cubicThetaPrimeCubeDilationSection {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) : cubicThetaPrimeCubeSections p :=
  ⟨⟨fun x => F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x),
    F.val.continuous.comp (continuous_const_smul _)⟩,by
    intro g x
    have he : cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (g.val • x)=
        cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g •
          (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x) := by
      change cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        (cubicThetaPrincipalComplex g.val • x)=
        cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g) •
          (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)
      rw [←mul_smul,←mul_smul,cubicThetaPrimeDilation_intertwines (cubicThetaPrimeCube_primary hp)]
    change F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (g.val • x))=_
    rw [he,F.property,←cubicThetaPrimeCubeConjugate_kubota hp g]
    rfl⟩

def cubicThetaPrimeCubeDilationLinear {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaSection →ₗ[ℂ] cubicThetaPrimeCubeSections p where
  toFun := cubicThetaPrimeCubeDilationSection hp
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

end CubicFirstMoment

end

end OAI
