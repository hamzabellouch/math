import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCoverDomain
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeAtkinAction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexPointMeasure

namespace OAI

/-! The prime normalizer descends to a genuine homeomorphism of the
common arithmetic cover. Both directions use the same involution on its group. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCoverAtkinEquiv {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCoverGroup hp ≃ cubicThetaPrimeCoverGroup hp :=
  ((cubicThetaPrimeCoverGroupEquiv hp).symm.toEquiv.trans
    (cubicThetaPrimeAtkinKernelEquiv hp)).trans (cubicThetaPrimeCoverGroupEquiv hp).toEquiv

lemma cubicThetaPrimeCoverAtkinEquiv_apply {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCharacterKernel hp) :
    cubicThetaPrimeCoverAtkinEquiv hp (cubicThetaPrimeCoverGroupEquiv hp g)=
      cubicThetaPrimeCoverGroupEquiv hp (cubicThetaPrimeAtkinKernel hp g) := by
  simp [cubicThetaPrimeCoverAtkinEquiv,cubicThetaPrimeAtkinKernelEquiv]

lemma cubicThetaPrimeCoverAtkinEquiv_involutive {p : Eisenstein} (hp : primaryPrime p) :
    Function.Involutive (cubicThetaPrimeCoverAtkinEquiv hp) := by
  intro g
  obtain ⟨k,rfl⟩ := (cubicThetaPrimeCoverGroupEquiv hp).surjective g
  rw [cubicThetaPrimeCoverAtkinEquiv_apply,cubicThetaPrimeCoverAtkinEquiv_apply,
    cubicThetaPrimeAtkinKernel_involutive]

lemma cubicThetaPrimeCoverAtkin_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCoverGroup hp) (x : CubicThetaPoint) :
    cubicThetaPrimeAtkinMatrix hp • (g • x)=
      cubicThetaPrimeCoverAtkinEquiv hp g • (cubicThetaPrimeAtkinMatrix hp • x) := by
  obtain ⟨k,rfl⟩ := (cubicThetaPrimeCoverGroupEquiv hp).surjective g
  rw [cubicThetaPrimeCoverAtkinEquiv_apply]
  exact cubicThetaPrimeAtkinPoint_intertwines hp k x

lemma cubicThetaPrimeCoverAtkin_inverse_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCoverGroup hp) (x : CubicThetaPoint) :
    (cubicThetaPrimeAtkinMatrix hp)⁻¹ • (g • x)=
      cubicThetaPrimeCoverAtkinEquiv hp g • ((cubicThetaPrimeAtkinMatrix hp)⁻¹ • x) := by
  apply MulAction.injective (cubicThetaPrimeAtkinMatrix hp)
  dsimp only
  rw [smul_inv_smul,cubicThetaPrimeCoverAtkin_intertwines,
    cubicThetaPrimeCoverAtkinEquiv_involutive,smul_inv_smul]

def cubicThetaPrimeCoverAtkinMap {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPrimeCover hp → CubicThetaPrimeCover hp :=
  Quotient.map (fun x => cubicThetaPrimeAtkinMatrix hp • x) (by
    intro a b hab
    obtain ⟨g,hg⟩ := hab
    refine ⟨cubicThetaPrimeCoverAtkinEquiv hp g,?_⟩
    dsimp only at hg ⊢
    rw [←cubicThetaPrimeCoverAtkin_intertwines,hg])

def cubicThetaPrimeCoverAtkinInverse {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPrimeCover hp → CubicThetaPrimeCover hp :=
  Quotient.map (fun x => (cubicThetaPrimeAtkinMatrix hp)⁻¹ • x) (by
    intro a b hab
    obtain ⟨g,hg⟩ := hab
    refine ⟨cubicThetaPrimeCoverAtkinEquiv hp g,?_⟩
    dsimp only at hg ⊢
    rw [←cubicThetaPrimeCoverAtkin_inverse_intertwines,hg])

@[simp] lemma cubicThetaPrimeCoverAtkinMap_apply {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    cubicThetaPrimeCoverAtkinMap hp (cubicThetaPrimeCoverMap hp x)=
      cubicThetaPrimeCoverMap hp (cubicThetaPrimeAtkinMatrix hp • x) := rfl

def cubicThetaPrimeCoverAtkinHomeomorph {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPrimeCover hp ≃ₜ CubicThetaPrimeCover hp where
  toFun := cubicThetaPrimeCoverAtkinMap hp
  invFun := cubicThetaPrimeCoverAtkinInverse hp
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h x =>
      change cubicThetaPrimeCoverMap hp
        ((cubicThetaPrimeAtkinMatrix hp)⁻¹ • (cubicThetaPrimeAtkinMatrix hp • x))=
          cubicThetaPrimeCoverMap hp x
      rw [inv_smul_smul]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h x =>
      change cubicThetaPrimeCoverMap hp
        (cubicThetaPrimeAtkinMatrix hp • ((cubicThetaPrimeAtkinMatrix hp)⁻¹ • x))=
          cubicThetaPrimeCoverMap hp x
      rw [smul_inv_smul]
  continuous_toFun := by
    apply (cubicThetaPrimeCoverMap_open hp).isQuotientMap.continuous_iff.mpr
    exact (cubicThetaPrimeCoverMap_open hp).continuous.comp
      (continuous_const_smul (cubicThetaPrimeAtkinMatrix hp))
  continuous_invFun := by
    apply (cubicThetaPrimeCoverMap_open hp).isQuotientMap.continuous_iff.mpr
    exact (cubicThetaPrimeCoverMap_open hp).continuous.comp
      (continuous_const_smul (cubicThetaPrimeAtkinMatrix hp)⁻¹)

end CubicFirstMoment

end

end OAI
