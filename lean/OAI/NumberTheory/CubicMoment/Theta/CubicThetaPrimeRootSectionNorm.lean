import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootCoverTransport

namespace OAI

/-! The norm of a section on the finite root cover is a genuine
continuous quotient function. The fractional-root pullback preserves its exact mass. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRootSection_property {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) (g : cubicThetaPrimeRootCoverGroup hp)
    (x : CubicThetaPoint) : F.val (g • x)=cubicThetaKubotaValue g.val*F.val x := by
  let k : cubicThetaPrimeRootSubgroup p := ⟨g.val,g.property⟩
  exact F.property k x

def cubicThetaPrimeRootSectionNorm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) : CubicThetaPrimeRootCover hp → ℝ :=
  Quotient.lift (fun x : CubicThetaPoint => ‖F.val x‖) (by
    intro x y hxy
    obtain ⟨g,hg⟩ := hxy
    dsimp only at hg
    rw [←hg,cubicThetaPrimeRootSection_property hp F,norm_mul,cubicThetaKubotaValue_norm,one_mul])

@[simp] lemma cubicThetaPrimeRootSectionNorm_apply {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) (x : CubicThetaPoint) :
    cubicThetaPrimeRootSectionNorm hp F (cubicThetaPrimeRootCoverMap hp x)=‖F.val x‖ := rfl

lemma cubicThetaPrimeRootSectionNorm_continuous {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) : Continuous (cubicThetaPrimeRootSectionNorm hp F) := by
  apply (cubicThetaPrimeRootCoverMap_open hp).isQuotientMap.continuous_iff.mpr
  exact F.val.continuous.norm

lemma cubicThetaPrimeRootSectionTranslate_norm {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeRootSections p) (q : CubicThetaPrimeRootCover hp) :
    cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootSectionTranslate hp x F) q=
      cubicThetaPrimeRootSectionNorm hp F (cubicThetaPrimeRootCoverTranslate hp x q) := by
  induction q using Quotient.inductionOn with
  | h x => rfl

theorem cubicThetaPrimeRootSectionTranslate_mass {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeRootSections p) :
    (∫ q, (cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootSectionTranslate hp x F) q)^2
      ∂cubicThetaPrimeRootCoverMeasure hp)=
    ∫ q, (cubicThetaPrimeRootSectionNorm hp F q)^2 ∂cubicThetaPrimeRootCoverMeasure hp := by
  simp_rw [cubicThetaPrimeRootSectionTranslate_norm]
  exact (cubicThetaPrimeRootCoverTranslate_measurePreserving hp x).integral_comp
    (cubicThetaPrimeRootCoverHomeomorph hp x).measurableEmbedding
    (fun q => (cubicThetaPrimeRootSectionNorm hp F q)^2)

end CubicFirstMoment

end

end OAI
