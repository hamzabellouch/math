import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticGradientMass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalGradient

namespace OAI

/-! The actual arithmetic differential is globally square integrable.
The result uses the finite arithmetic cusp/core cover and the literal
hyperbolic energy density, without assuming energy-graph membership. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaArithmeticQuotientEnergy_cusp_integrable (δ : SL(2,Eisenstein))
    {s : ℂ} (hs : 3<s.re) :
    IntegrableOn (cubicThetaArithmeticQuotientEnergy s (by linarith))
      (cubicThetaCuspNeighborhood δ 2) cubicThetaQuotientMeasure := by
  apply (cubicThetaCuspNeighborhood_integrable_iff δ (by norm_num)
    (cubicThetaArithmeticQuotientEnergy_continuous s (by linarith))).mpr
  have h := cubicThetaArithmeticCoordinateEnergy_integrable δ hs
  rw [← cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2),
    ← cubicThetaPointIntegrable_density (cubicThetaCuspStrip_measurable 2)] at h
  simpa only [cubicThetaArithmeticQuotientEnergy_apply,cubicThetaArithmeticCoordinateEnergy_apply] using h

theorem cubicThetaArithmeticQuotientEnergy_integrable {s : ℂ} (hs : 3<s.re) :
    Integrable (cubicThetaArithmeticQuotientEnergy s (by linarith)) cubicThetaQuotientMeasure := by
  obtain ⟨S,hS⟩ := cubicThetaCuspNeighborhood_cover
  have hf := cubicThetaArithmeticQuotientEnergy_continuous s (show 2<s.re by linarith)
  have hc := hf.continuousOn.integrableOn_compact (μ:=cubicThetaQuotientMeasure)
    (cubicThetaQuotientCore_compact S 2)
  have hu : IntegrableOn (cubicThetaArithmeticQuotientEnergy s (by linarith))
      (⋃ δ∈S,cubicThetaCuspNeighborhood δ⁻¹ 2) cubicThetaQuotientMeasure :=
    integrableOn_finset_iUnion.mpr (fun δ _ => cubicThetaArithmeticQuotientEnergy_cusp_integrable δ⁻¹ hs)
  have h := hc.union hu
  rwa [hS 2,integrableOn_univ] at h

lemma cubicThetaArithmeticGradient_continuous {s : ℂ} (hs : 2<s.re) :
    Continuous (cubicThetaSectionGradient (cubicThetaArithmeticSection s hs)) := by
  have hd : Continuous (fun p : CubicThetaPoint =>
      fderiv ℝ (cubicThetaSectionFunction (cubicThetaArithmeticSection s hs)) p.val) :=
    ((cubicThetaArithmeticSectionFunction_contDiffOn_one hs).continuousOn_fderiv_of_isOpen
      (isOpen_lt continuous_const continuous_snd) (by norm_num)).comp_continuous
      continuous_subtype_val (fun p => p.property)
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi
  intro i
  exact (continuous_snd.comp continuous_subtype_val).smul (hd.clm_apply continuous_const)

lemma cubicThetaArithmeticGradientRepresentative_measurable {s : ℂ} (hs : 2<s.re) :
    Measurable (cubicThetaGradientRepresentative (cubicThetaArithmeticSection s hs)) :=
  (cubicThetaArithmeticGradient_continuous hs).measurable.comp cubicThetaBorelSection_measurable

lemma cubicThetaArithmeticGradientRepresentative_norm_sq {s : ℂ} (hs : 2<s.re)
    (q : CubicThetaQuotient) :
    ‖cubicThetaGradientRepresentative (cubicThetaArithmeticSection s hs) q‖^2=
      cubicThetaArithmeticQuotientEnergy s hs q := by
  unfold cubicThetaGradientRepresentative
  rw [cubicThetaSectionGradient_norm_sq,← cubicThetaArithmeticQuotientEnergy_apply,
    cubicThetaBorelSection_rightInverse]

lemma cubicThetaArithmeticGradientRepresentative_memLp {s : ℂ} (hs : 3<s.re) :
    MemLp (cubicThetaGradientRepresentative (cubicThetaArithmeticSection s (by linarith)))
      2 cubicThetaQuotientMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (cubicThetaArithmeticGradientRepresentative_measurable (by linarith)).aestronglyMeasurable).mpr
  simpa only [cubicThetaArithmeticGradientRepresentative_norm_sq] using
    cubicThetaArithmeticQuotientEnergy_integrable hs

def cubicThetaArithmeticGradientL2 (s : ℂ) (hs : 3<s.re) : CubicThetaGradientL2 :=
  (cubicThetaArithmeticGradientRepresentative_memLp hs).toLp _

lemma cubicThetaArithmeticGradientL2_coe (s : ℂ) (hs : 3<s.re) :
    cubicThetaArithmeticGradientL2 s hs =ᵐ[cubicThetaQuotientMeasure]
      cubicThetaGradientRepresentative (cubicThetaArithmeticSection s (by linarith)) :=
  (cubicThetaArithmeticGradientRepresentative_memLp hs).coeFn_toLp

end CubicFirstMoment

end

end OAI
