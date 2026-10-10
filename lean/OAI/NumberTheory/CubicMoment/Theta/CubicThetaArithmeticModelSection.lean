import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBorelRestriction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPointMeasurePositive
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStripReduction

namespace OAI

/-! Recover the global cubic automorphy of the continuous arithmetic
model from its actual L2 residue and the full positive-strip identities. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
local instance cubicThetaArithmeticModelSectionCountable : Countable Eisenstein :=
  coordinatesEquiv.symm.injective.countable

lemma cubicThetaArithmeticModel_three_periodic (A : ℂ) (w : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaArithmeticModel A (z+3*(w:ℂ),v)=cubicThetaArithmeticModel A (z,v) := by
  unfold cubicThetaArithmeticModel
  congr 1
  congr 1
  rw [cubicThetaArithmeticRowSeries,cubicThetaArithmeticRowSeries]
  apply tsum_congr
  intro h
  rw [cubicThetaArithmeticRowTerm_phase (z+3*(w:ℂ)),cubicThetaArithmeticRowTerm_phase z]
  change _*cubicThetaHorizontalCharacter h (z+3*(w:ℂ))=_*cubicThetaHorizontalCharacter h z
  rw [cubicThetaHorizontalCharacter_periodic]

lemma cubicThetaArithmeticModel_translation (A : ℂ) (w : Eisenstein) (p : CubicThetaPoint) :
    cubicThetaArithmeticModel A (cubicThetaPointCoordinates (cubicThetaPrincipalTranslation w • p))=
      cubicThetaArithmeticModel A p.val := by
  rw [cubicThetaPrincipalTranslation_coordinates,cubicThetaArithmeticModel_three_periodic]
  rfl

theorem cubicThetaArithmeticModel_global_ae :
    cubicThetaBorelLift (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)
      =ᵐ[cubicThetaPointMeasure]
        (fun p => cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val) := by
  have hslice (n : ℕ) : ∀ᵐ p ∂cubicThetaPointMeasure,
      p∈cubicThetaCuspStrip (1/(n+1:ℝ)) →
      cubicThetaBorelLift (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue) p=
        cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val :=
    (ae_restrict_iff' (cubicThetaCuspStrip_measurable _)).mp
      (cubicThetaResidue_borel_model (by positivity : (0:ℝ)<1/(n+1:ℝ)))
  have hall : ∀ᵐ p ∂cubicThetaPointMeasure,∀ w : Eisenstein,∀ n : ℕ,
      cubicThetaPrincipalTranslation w • p∈cubicThetaCuspStrip (1/(n+1:ℝ)) →
      cubicThetaBorelLift (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)
          (cubicThetaPrincipalTranslation w • p)=
        cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
          (cubicThetaPrincipalTranslation w • p).val :=
    ae_all_iff.mpr (fun w => ae_all_iff.mpr (fun n =>
      (measurePreserving_smul (cubicThetaPrincipalTranslation w) cubicThetaPointMeasure).quasiMeasurePreserving.ae (hslice n)))
  filter_upwards [hall] with p hp
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt p.property
  obtain ⟨w,hw⟩ := cubicThetaCuspStrip_reduction p hn
  have he := hp w n hw
  rw [cubicThetaBorelLift_automorphy,cubicThetaPrincipalTranslation_value,one_mul] at he
  exact he.trans (cubicThetaArithmeticModel_translation cubicThetaArithmeticBaseScalar w p)

theorem cubicThetaArithmeticModel_automorphy (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (g • p).val=
      cubicThetaKubotaValue g*cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val := by
  have hg := (measurePreserving_smul g cubicThetaPointMeasure).quasiMeasurePreserving.ae
    cubicThetaArithmeticModel_global_ae
  have he : (fun p : CubicThetaPoint =>
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (g • p).val)
      =ᵐ[cubicThetaPointMeasure]
      (fun p => cubicThetaKubotaValue g*cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val) := by
    filter_upwards [cubicThetaArithmeticModel_global_ae,hg] with p hp hgp
    rw [←hgp,cubicThetaBorelLift_automorphy,hp]
  have hc := cubicThetaArithmeticModel_point_continuous cubicThetaArithmeticBaseScalar
  exact congrFun (Measure.eq_of_ae_eq he (hc.comp (continuous_const_smul g)) (continuous_const.mul hc)) p

def cubicThetaArithmeticModelSection : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val,
    cubicThetaArithmeticModel_point_continuous cubicThetaArithmeticBaseScalar⟩,
    cubicThetaArithmeticModel_automorphy⟩

end CubicFirstMoment

end

end OAI
