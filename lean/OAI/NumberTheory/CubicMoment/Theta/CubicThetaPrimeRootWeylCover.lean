import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylSections

namespace OAI

/-! The same conjugated inversion is a homeomorphism of the actual
finite arithmetic cover. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeRootCoverWeyl {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPrimeRootCover hp → CubicThetaPrimeRootCover hp :=
  Quotient.map (fun y => cubicThetaPrimeRootWeylElement hp • y) (by
    intro a b hab
    obtain ⟨g,hg⟩ := hab
    let k : cubicThetaPrimeRootSubgroup p := ⟨g.val,g.property⟩
    refine ⟨⟨(cubicThetaPrimeRootWeylConjugate hp k).val,
      (cubicThetaPrimeRootWeylConjugate hp k).property⟩,?_⟩
    change k.val • b=a at hg
    change (cubicThetaPrimeRootWeylConjugate hp k).val • (cubicThetaPrimeRootWeylElement hp • b)=
      cubicThetaPrimeRootWeylElement hp • a
    rw [←cubicThetaPrimeRootWeylPoint_intertwines,hg])

@[simp] lemma cubicThetaPrimeRootCoverWeyl_apply {p : Eisenstein} (hp : primaryPrime p)
    (y : CubicThetaPoint) :
    cubicThetaPrimeRootCoverWeyl hp (cubicThetaPrimeRootCoverMap hp y)=
      cubicThetaPrimeRootCoverMap hp (cubicThetaPrimeRootWeylElement hp • y) := rfl

def cubicThetaPrimeRootCoverWeylHomeomorph {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPrimeRootCover hp ≃ₜ CubicThetaPrimeRootCover hp where
  toFun := cubicThetaPrimeRootCoverWeyl hp
  invFun := cubicThetaPrimeRootCoverWeyl hp
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h y =>
      change cubicThetaPrimeRootCoverMap hp
        (cubicThetaPrimeRootWeylElement hp • (cubicThetaPrimeRootWeylElement hp • y))=
          cubicThetaPrimeRootCoverMap hp y
      rw [cubicThetaPrimeRootWeylPoint_involutive]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h y =>
      change cubicThetaPrimeRootCoverMap hp
        (cubicThetaPrimeRootWeylElement hp • (cubicThetaPrimeRootWeylElement hp • y))=
          cubicThetaPrimeRootCoverMap hp y
      rw [cubicThetaPrimeRootWeylPoint_involutive]
  continuous_toFun := by
    apply (cubicThetaPrimeRootCoverMap_open hp).isQuotientMap.continuous_iff.mpr
    exact (cubicThetaPrimeRootCoverMap_open hp).continuous.comp
      (continuous_const_smul (cubicThetaPrimeRootWeylElement hp))
  continuous_invFun := by
    apply (cubicThetaPrimeRootCoverMap_open hp).isQuotientMap.continuous_iff.mpr
    exact (cubicThetaPrimeRootCoverMap_open hp).continuous.comp
      (continuous_const_smul (cubicThetaPrimeRootWeylElement hp))

end CubicFirstMoment

end

end OAI
