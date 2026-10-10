import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeAtkinInvolution

namespace OAI

/-! The complex prime normalizer and its action on positive-height
points. The intertwining identity uses the constructed arithmetic involution. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeAtkinMatrix {p : Eisenstein} (hp : primaryPrime p) : SL(2,ℂ) :=
  cubicThetaFullComplex cubicThetaFullInversion*cubicThetaPrimeDilation hp.2.ne_zero

theorem cubicThetaPrimeAtkinMatrix_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) :
    cubicThetaPrimeAtkinMatrix hp*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeAtkinConjugate hp g).val*
        cubicThetaPrimeAtkinMatrix hp := by
  have he : cubicThetaPrincipalComplex (cubicThetaPrimeAtkinConjugate hp g).val=
      cubicThetaFullComplex cubicThetaFullInversion*
        cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1 g)*
          (cubicThetaFullComplex cubicThetaFullInversion)⁻¹ := by
    change cubicThetaFullComplex ((cubicThetaFullInversion⁻¹)⁻¹*
      (cubicThetaPrimeConjugate hp.1 g).val*cubicThetaFullInversion⁻¹)=_
    rw [inv_inv,map_mul,map_mul,map_inv]
    rfl
  rw [cubicThetaPrimeAtkinMatrix,mul_assoc,cubicThetaPrimeDilation_intertwines hp.1 g,he]
  group

lemma cubicThetaPrimeAtkinPoint_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCharacterKernel hp) (x : CubicThetaPoint) :
    cubicThetaPrimeAtkinMatrix hp • (g.val.val • x)=
      (cubicThetaPrimeAtkinKernel hp g).val.val • (cubicThetaPrimeAtkinMatrix hp • x) := by
  change cubicThetaPrimeAtkinMatrix hp • (cubicThetaPrincipalComplex g.val.val • x)=
    cubicThetaPrincipalComplex (cubicThetaPrimeAtkinKernel hp g).val.val •
      (cubicThetaPrimeAtkinMatrix hp • x)
  rw [←mul_smul,←mul_smul,cubicThetaPrimeAtkinMatrix_intertwines hp g.val]
  rfl

lemma cubicThetaPrimeAtkinPoint_continuous {p : Eisenstein} (hp : primaryPrime p) :
    Continuous (fun x : CubicThetaPoint => cubicThetaPrimeAtkinMatrix hp • x) := by
  change Continuous (fun x : CubicThetaPoint =>
    (⟨cubicThetaMobius (cubicThetaPrimeAtkinMatrix hp) x.val,
      cubicThetaMobius_height_pos _ x.property⟩ : CubicThetaPoint))
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (cubicThetaMobius_continuousAt _ x.property).comp
    (x:=x) (f:=fun y : CubicThetaPoint => y.val) continuous_subtype_val.continuousAt

def cubicThetaPrimeSections {p : Eisenstein} (hp : primaryPrime p) :
    Submodule ℂ C(CubicThetaPoint,ℂ) where
  carrier := {F | ∀ g : cubicThetaPrimeCharacterKernel hp, ∀ x : CubicThetaPoint,
    F (g.val.val • x)=cubicThetaKubotaValue g.val.val*F x}
  zero_mem' := by simp
  add_mem' := by
    intro F G hF hG g x
    change F (g.val.val • x)+G (g.val.val • x)=
      cubicThetaKubotaValue g.val.val*(F x+G x)
    rw [hF,hG]
    ring
  smul_mem' := by
    intro a F hF g x
    change a*F (g.val.val • x)=cubicThetaKubotaValue g.val.val*(a*F x)
    rw [hF]
    ring

def cubicThetaPrimeSectionRestrict {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) : cubicThetaPrimeSections hp :=
  ⟨F.val,fun g x => F.property g.val.val x⟩

def cubicThetaPrimeAtkinSection {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) : cubicThetaPrimeSections hp :=
  ⟨⟨fun x => F.val (cubicThetaPrimeAtkinMatrix hp • x),
    F.val.continuous.comp (cubicThetaPrimeAtkinPoint_continuous hp)⟩,by
    intro g x
    change F.val (cubicThetaPrimeAtkinMatrix hp • (g.val.val • x))=
      cubicThetaKubotaValue g.val.val*F.val (cubicThetaPrimeAtkinMatrix hp • x)
    rw [cubicThetaPrimeAtkinPoint_intertwines,F.property,cubicThetaPrimeAtkinKernel_kubota]⟩

end CubicFirstMoment

end

end OAI
