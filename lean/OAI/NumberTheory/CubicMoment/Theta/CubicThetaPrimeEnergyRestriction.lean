import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeEnergySpace
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergyIntegralIdentities

namespace OAI

/-! Original compact smooth sections restrict to finite-energy prime
sections. Both mass and derivative energy scale by the exact covering degree. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

def cubicThetaPrimeSmoothC1 {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) : cubicThetaPrimeC1Sections hp :=
  ⟨cubicThetaPrimeSectionRestrict hp F.val,F.property.1.of_le (by simp)⟩

lemma cubicThetaPrimeSmoothC1_energy {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) (q : CubicThetaPrimeCover hp) :
    cubicThetaPrimeQuotientEnergy hp (cubicThetaPrimeSmoothC1 hp F) q=
      cubicThetaQuotientEnergy F (cubicThetaPrimeCoverProjection hp q) := by
  induction q using Quotient.inductionOn with
  | h x =>
    change cubicThetaPrimeQuotientEnergy hp (cubicThetaPrimeSmoothC1 hp F)
      (cubicThetaPrimeCoverMap hp x)=
        cubicThetaQuotientEnergy F
          (cubicThetaPrimeCoverProjection hp (cubicThetaPrimeCoverMap hp x))
    rw [cubicThetaPrimeQuotientEnergy_apply,cubicThetaPrimeCoverProjection_apply,
      cubicThetaQuotientEnergy_apply]
    exact cubicThetaPrimeSectionRestrict_energy hp F.val x

lemma cubicThetaPrimeSmoothC1_gradient_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    MemLp (cubicThetaPrimeGradientRepresentative hp (cubicThetaPrimeSmoothC1 hp F))
      2 (cubicThetaPrimeCoverMeasure hp) := by
  apply (memLp_norm_iff (cubicThetaPrimeGradientRepresentative_measurable hp _).aestronglyMeasurable).mp
  have hn := cubicThetaQuotientGradientNorm_memLp F
  have hs := hn.smul_measure
    (by simp : ((cubicThetaPrimeCoverGroup hp).index:ℝ≥0∞)≠∞)
  rw [←cubicThetaPrimeCoverProjection_measure hp] at hs
  have hc := hs.comp_of_map (cubicThetaPrimeCoverProjection_continuous hp).measurable.aemeasurable
  simpa only [Function.comp_def,cubicThetaPrimeGradientRepresentative_norm,
    cubicThetaPrimeSmoothC1_energy,cubicThetaQuotientGradientNorm] using hc

def cubicThetaPrimeSmoothEnergyRestriction {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSmoothTests →ₗ[ℂ] cubicThetaPrimeFiniteEnergy hp where
  toFun F := ⟨cubicThetaPrimeSmoothC1 hp F,
    cubicThetaPrimeSectionRestrict_memLp hp F.val (cubicThetaSectionRepresentative_memLp F),
    cubicThetaPrimeSmoothC1_gradient_memLp hp F⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeSmoothEnergy_gradient_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeEnergyGradient hp (cubicThetaPrimeSmoothEnergyRestriction hp F)‖^2=
      ((cubicThetaPrimeCoverGroup hp).index:ℝ)*
        ‖cubicThetaGlobalEnergyGradient (cubicThetaGlobalEnergyTest F)‖^2 := by
  rw [cubicThetaPrimeEnergyGradient_norm_sq,cubicThetaGlobalGradient_test_norm_sq]
  change (∫ q, cubicThetaPrimeQuotientEnergy hp (cubicThetaPrimeSmoothC1 hp F) q
    ∂cubicThetaPrimeCoverMeasure hp)=_
  simp_rw [cubicThetaPrimeSmoothC1_energy]
  have hi := integral_map_of_stronglyMeasurable (μ:=cubicThetaPrimeCoverMeasure hp)
    (cubicThetaPrimeCoverProjection_continuous hp).measurable
    (cubicThetaQuotientEnergy_continuous F).stronglyMeasurable
  rw [←hi,cubicThetaPrimeCoverProjection_measure hp,integral_smul_measure]
  simp only [ENNReal.toReal_natCast,smul_eq_mul]

theorem cubicThetaPrimeSmoothEnergyRestriction_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeEnergyTest hp (cubicThetaPrimeSmoothEnergyRestriction hp F)‖^2=
      ((cubicThetaPrimeCoverGroup hp).index:ℝ)*‖cubicThetaGlobalEnergyTest F‖^2 := by
  rw [cubicThetaPrimeEnergy_norm_sq,cubicThetaGlobalEnergy_norm_sq,
    cubicThetaPrimeEnergyInclusion_test,cubicThetaPrimeEnergyDerivative_test,
    cubicThetaPrimeSmoothEnergy_gradient_norm_sq,cubicThetaGlobalInclusion_test]
  have hm := cubicThetaPrimeSectionRestrict_L2_norm_sq hp F.val (cubicThetaSectionRepresentative_memLp F)
  change ‖cubicThetaPrimeEnergyValue hp (cubicThetaPrimeSmoothEnergyRestriction hp F)‖^2=
    ((cubicThetaPrimeCoverGroup hp).index:ℝ)*‖cubicThetaGlobalMass F‖^2 at hm
  rw [hm]
  ring

end CubicFirstMoment

end

end OAI
