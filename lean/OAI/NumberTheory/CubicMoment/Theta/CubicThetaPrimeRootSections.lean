import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootAction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeAtkinAction

namespace OAI

/-! The actual finite-cover section space and its fractional root action. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPrimeRootPoint_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) (y : CubicThetaPoint) :
    cubicThetaPrimeRootElement hp x • (g.val • y)=
      (cubicThetaPrimeRootConjugate hp x g).val • (cubicThetaPrimeRootElement hp x • y) := by
  change cubicThetaPrimeRootElement hp x • (cubicThetaPrincipalComplex g.val • y)=
    cubicThetaPrincipalComplex (cubicThetaPrimeRootConjugate hp x g).val •
      (cubicThetaPrimeRootElement hp x • y)
  rw [←mul_smul,←mul_smul,cubicThetaPrimeRootElement_intertwines]

lemma cubicThetaPrimeRootPoint_continuous {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : Continuous (fun y : CubicThetaPoint => cubicThetaPrimeRootElement hp x • y) := by
  change Continuous (fun y : CubicThetaPoint =>
    (⟨cubicThetaMobius (cubicThetaPrimeRootElement hp x) y.val,
      cubicThetaMobius_height_pos _ y.property⟩ : CubicThetaPoint))
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (cubicThetaMobius_continuousAt _ y.property).comp
    (x:=y) (f:=fun z : CubicThetaPoint => z.val) continuous_subtype_val.continuousAt

def cubicThetaPrimeRootSections (p : Eisenstein) : Submodule ℂ C(CubicThetaPoint,ℂ) where
  carrier := {F | ∀ g : cubicThetaPrimeRootSubgroup p, ∀ y : CubicThetaPoint,
    F (g.val • y)=cubicThetaKubotaValue g.val*F y}
  zero_mem' := by simp
  add_mem' := by
    intro F G hF hG g y
    change F (g.val • y)+G (g.val • y)=cubicThetaKubotaValue g.val*(F y+G y)
    rw [hF,hG]
    ring
  smul_mem' := by
    intro a F hF g y
    change a*F (g.val • y)=cubicThetaKubotaValue g.val*(a*F y)
    rw [hF]
    ring

def cubicThetaPrimeRootSectionRestrict {p : Eisenstein} (F : CubicThetaSection) :
    cubicThetaPrimeRootSections p := ⟨F.val,fun g y => F.property g.val y⟩

def cubicThetaPrimeRootSectionTranslate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeRootSections p) : cubicThetaPrimeRootSections p :=
  ⟨⟨fun y => F.val (cubicThetaPrimeRootElement hp x • y),
    F.val.continuous.comp (cubicThetaPrimeRootPoint_continuous hp x)⟩,by
    intro g y
    change F.val (cubicThetaPrimeRootElement hp x • (g.val • y))=
      cubicThetaKubotaValue g.val*F.val (cubicThetaPrimeRootElement hp x • y)
    rw [cubicThetaPrimeRootPoint_intertwines,F.property,cubicThetaPrimeRootConjugate_kubota]⟩

end CubicFirstMoment

end

end OAI
