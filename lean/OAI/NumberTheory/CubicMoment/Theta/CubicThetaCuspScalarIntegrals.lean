import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspCoordinateEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStripReduction

namespace OAI

/-! Exact scalar transport from the quotient to each arithmetic cusp cell.
These formulas separate mass and derivative energy, so the sharp Hardy
coefficient is preserved when the cusp estimates are summed. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaCuspPullback (δ : SL(2,Eisenstein)) (f : CubicThetaQuotient → ℝ)
    (y : ℂ × ℝ) : ℝ :=
  f (cubicThetaQuotientMap (δ • cubicThetaPointInclusion.symm y))

lemma cubicThetaCuspPullback_apply (δ : SL(2,Eisenstein)) (f : CubicThetaQuotient → ℝ)
    (p : CubicThetaPoint) :
    cubicThetaCuspPullback δ f (cubicThetaPointCoordinates p)=f (cubicThetaQuotientMap (δ • p)) := by
  have h : cubicThetaPointInclusion.symm (cubicThetaPointCoordinates p)=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  simp only [cubicThetaCuspPullback,h]

lemma cubicThetaCuspPullback_integrable (δ : SL(2,Eisenstein))
    {f : CubicThetaQuotient → ℝ} (hf : Integrable f cubicThetaQuotientMeasure)
    {H : ℝ} (hH : 1≤H) :
    IntegrableOn (fun y => cubicThetaCuspPullback δ f y/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi H) := by
  rw [← cubicThetaCuspStrip_coordinates (zero_le_one.trans hH),
    ← cubicThetaPointIntegrable_density (cubicThetaCuspStrip_measurable H)]
  simpa only [cubicThetaCuspPullback_apply] using
    cubicThetaTranslatedCuspStrip_integrable δ hH hf

lemma cubicThetaCuspPullback_integral (δ : SL(2,Eisenstein))
    (f : CubicThetaQuotient → ℝ) (hf : StronglyMeasurable f) {H : ℝ} (hH : 1≤H) :
    (∫ y in cubicThetaHorizontalCell ×ˢ Ioi H, cubicThetaCuspPullback δ f y/y.2^3)=
      ∫ q in cubicThetaCuspNeighborhood δ H, f q ∂cubicThetaQuotientMeasure := by
  unfold cubicThetaCuspNeighborhood
  rw [cubicThetaTranslatedCuspStrip_integral δ hH f hf]
  rw [← cubicThetaCuspStrip_coordinates (zero_le_one.trans hH),
    ← cubicThetaPointIntegral_density (cubicThetaCuspStrip_measurable H)]
  apply setIntegral_congr_fun (cubicThetaCuspStrip_measurable H)
  intro p hp
  exact cubicThetaCuspPullback_apply δ f p

lemma cubicThetaMass_integrable (F : cubicThetaSmoothTests) :
    Integrable (fun q => cubicThetaSectionNorm F q^2) cubicThetaQuotientMeasure := by
  have h := (cubicThetaSectionRepresentative_memLp F).integrable_norm_pow (by norm_num)
  simpa only [cubicThetaSectionRepresentative_norm] using h

lemma cubicThetaGradientEnergy_integrable (F : cubicThetaSmoothTests) :
    Integrable (cubicThetaQuotientEnergy F) cubicThetaQuotientMeasure :=
  (cubicThetaQuotientEnergy_continuous F).integrable_of_hasCompactSupport
    (cubicThetaQuotientEnergy_compact F)

lemma cubicThetaCuspPullback_mass (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaCuspPullback δ (fun q => cubicThetaSectionNorm F q^2) (z,v)=
      ‖cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex δ) (z,v))‖^2 := by
  have h := cubicThetaCuspPullback_apply δ (fun q => cubicThetaSectionNorm F q^2)
    (cubicThetaVerticalPoint z v hv)
  change cubicThetaCuspPullback δ (fun q => cubicThetaSectionNorm F q^2) (z,v)=_ at h
  rw [h,cubicThetaCusp_raw_norm δ F z hv]

lemma cubicThetaCuspPullback_energy (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaCuspPullback δ (cubicThetaQuotientEnergy F) (z,v)=
      cubicThetaSectionEnergy F (δ • cubicThetaVerticalPoint z v hv) := by
  have h := cubicThetaCuspPullback_apply δ (cubicThetaQuotientEnergy F)
    (cubicThetaVerticalPoint z v hv)
  change cubicThetaCuspPullback δ (cubicThetaQuotientEnergy F) (z,v)=_ at h
  rw [h,cubicThetaQuotientEnergy_apply]

end CubicFirstMoment

end

end OAI
