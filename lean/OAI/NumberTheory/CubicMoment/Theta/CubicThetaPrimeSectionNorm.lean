import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeAtkinMeasure

namespace OAI

/-! The norm of a section on the finite prime cover is a genuine
continuous quotient function. The Atkin pullback preserves its exact mass. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeSection_property {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) (g : cubicThetaPrimeCoverGroup hp)
    (x : CubicThetaPoint) : F.val (g • x)=cubicThetaKubotaValue g.val*F.val x := by
  obtain ⟨k,rfl⟩ := (cubicThetaPrimeCoverGroupEquiv hp).surjective g
  exact F.property k x

def cubicThetaPrimeSectionNorm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) : CubicThetaPrimeCover hp → ℝ :=
  Quotient.lift (fun x : CubicThetaPoint => ‖F.val x‖) (by
    intro x y hxy
    obtain ⟨g,hg⟩ := hxy
    dsimp only at hg
    rw [←hg,cubicThetaPrimeSection_property hp F,norm_mul,cubicThetaKubotaValue_norm,one_mul])

@[simp] lemma cubicThetaPrimeSectionNorm_apply {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) (x : CubicThetaPoint) :
    cubicThetaPrimeSectionNorm hp F (cubicThetaPrimeCoverMap hp x)=‖F.val x‖ := rfl

lemma cubicThetaPrimeSectionNorm_continuous {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) : Continuous (cubicThetaPrimeSectionNorm hp F) := by
  apply (cubicThetaPrimeCoverMap_open hp).isQuotientMap.continuous_iff.mpr
  exact F.val.continuous.norm

lemma cubicThetaPrimeAtkinSection_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) (q : CubicThetaPrimeCover hp) :
    cubicThetaPrimeSectionNorm hp (cubicThetaPrimeAtkinSection hp F) q=
      cubicThetaPrimeSectionNorm hp F (cubicThetaPrimeCoverAtkinMap hp q) := by
  induction q using Quotient.inductionOn with
  | h x => rfl

lemma cubicThetaPrimeSectionRestrict_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (q : CubicThetaPrimeCover hp) :
    cubicThetaPrimeSectionNorm hp (cubicThetaPrimeSectionRestrict hp F) q=
      cubicThetaSectionNorm F (cubicThetaPrimeCoverProjection hp q) := by
  induction q using Quotient.inductionOn with
  | h x =>
    exact (cubicThetaSectionNorm_apply F x).symm

theorem cubicThetaPrimeAtkinSection_mass {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) :
    (∫ q, (cubicThetaPrimeSectionNorm hp (cubicThetaPrimeAtkinSection hp F) q)^2
      ∂cubicThetaPrimeCoverMeasure hp)=
    ∫ q, (cubicThetaPrimeSectionNorm hp F q)^2 ∂cubicThetaPrimeCoverMeasure hp := by
  simp_rw [cubicThetaPrimeAtkinSection_norm]
  exact (cubicThetaPrimeCoverAtkin_measurePreserving hp).integral_comp
    (cubicThetaPrimeCoverAtkinHomeomorph hp).measurableEmbedding
    (fun q => (cubicThetaPrimeSectionNorm hp F q)^2)

end CubicFirstMoment

end

end OAI
