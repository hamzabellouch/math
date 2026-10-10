import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootCoverMeasure
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexPointMeasure

namespace OAI

/-! Fractional roots act on the actual finite arithmetic cover. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeRootCoverTranslate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : CubicThetaPrimeRootCover hp → CubicThetaPrimeRootCover hp :=
  Quotient.map (fun y => cubicThetaPrimeRootElement hp x • y) (by
    intro a b hab
    obtain ⟨g,hg⟩ := hab
    let k : cubicThetaPrimeRootSubgroup p := ⟨g.val,g.property⟩
    refine ⟨⟨(cubicThetaPrimeRootConjugate hp x k).val,
      (cubicThetaPrimeRootConjugate hp x k).property⟩,?_⟩
    change k.val • b=a at hg
    change (cubicThetaPrimeRootConjugate hp x k).val • (cubicThetaPrimeRootElement hp x • b)=
      cubicThetaPrimeRootElement hp x • a
    rw [←cubicThetaPrimeRootPoint_intertwines,hg])

@[simp] lemma cubicThetaPrimeRootCoverTranslate_apply {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (y : CubicThetaPoint) :
    cubicThetaPrimeRootCoverTranslate hp x (cubicThetaPrimeRootCoverMap hp y)=
      cubicThetaPrimeRootCoverMap hp (cubicThetaPrimeRootElement hp x • y) := rfl

def cubicThetaPrimeRootCoverHomeomorph {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : CubicThetaPrimeRootCover hp ≃ₜ CubicThetaPrimeRootCover hp where
  toFun := cubicThetaPrimeRootCoverTranslate hp x
  invFun := cubicThetaPrimeRootCoverTranslate hp (-x)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h y =>
      change cubicThetaPrimeRootCoverMap hp
        (cubicThetaPrimeRootElement hp (-x) • (cubicThetaPrimeRootElement hp x • y))=
          cubicThetaPrimeRootCoverMap hp y
      rw [cubicThetaPrimeRootElement_neg,inv_smul_smul]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h y =>
      change cubicThetaPrimeRootCoverMap hp
        (cubicThetaPrimeRootElement hp x • (cubicThetaPrimeRootElement hp (-x) • y))=
          cubicThetaPrimeRootCoverMap hp y
      rw [cubicThetaPrimeRootElement_neg,smul_inv_smul]
  continuous_toFun := by
    apply (cubicThetaPrimeRootCoverMap_open hp).isQuotientMap.continuous_iff.mpr
    exact (cubicThetaPrimeRootCoverMap_open hp).continuous.comp
      (continuous_const_smul (cubicThetaPrimeRootElement hp x))
  continuous_invFun := by
    apply (cubicThetaPrimeRootCoverMap_open hp).isQuotientMap.continuous_iff.mpr
    exact (cubicThetaPrimeRootCoverMap_open hp).continuous.comp
      (continuous_const_smul (cubicThetaPrimeRootElement hp (-x)))

end CubicFirstMoment

end

end OAI
