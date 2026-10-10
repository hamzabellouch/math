import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTranslatedCuspStrip
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspVerticalEnergy

namespace OAI

/-! The true scalar mass and energy in each cusp, in the Euclidean
coordinates used for the radial integration. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaCuspCoordinateEnergy (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (y : ℂ × ℝ) : ℝ :=
  cubicThetaSectionNorm F
      (cubicThetaQuotientMap (δ • cubicThetaPointInclusion.symm y))^2+
    cubicThetaSectionEnergy F (δ • cubicThetaPointInclusion.symm y)

lemma cubicThetaCuspCoordinateEnergy_apply (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (p : CubicThetaPoint) :
    cubicThetaCuspCoordinateEnergy δ F (cubicThetaPointCoordinates p)=
      cubicThetaSectionNorm F (cubicThetaQuotientMap (δ • p))^2+
        cubicThetaSectionEnergy F (δ • p) := by
  have h : cubicThetaPointInclusion.symm (cubicThetaPointCoordinates p)=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  simp only [cubicThetaCuspCoordinateEnergy,h]

lemma cubicThetaCuspCoordinateEnergy_integrable (δ : SL(2,Eisenstein))
    (F : cubicThetaSmoothTests) {H : ℝ} (hH : 1≤H) :
    IntegrableOn (fun y => cubicThetaCuspCoordinateEnergy δ F y/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi H) := by
  have h := cubicThetaTranslatedCuspStrip_integrable δ hH (cubicThetaIntrinsicEnergy_integrable F)
  simp only [cubicThetaQuotientEnergy_apply] at h
  rw [← cubicThetaCuspStrip_coordinates (zero_le_one.trans hH),
    ← cubicThetaPointIntegrable_density (cubicThetaCuspStrip_measurable H)]
  simpa only [cubicThetaCuspCoordinateEnergy_apply] using h

lemma cubicThetaCusp_raw_norm (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    ‖cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex δ) (z,v))‖=
      cubicThetaSectionNorm F (cubicThetaQuotientMap (δ • cubicThetaVerticalPoint z v hv)) := by
  have h := cubicThetaSectionNorm_apply F (δ • cubicThetaVerticalPoint z v hv)
  rw [cubicThetaSectionFunction_apply F (cubicThetaMobius_height_pos
    (cubicThetaFullComplex δ) (p:=(z,v)) hv)]
  exact h.symm

lemma cubicThetaCuspCoordinateEnergy_norm (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaCuspCoordinateEnergy δ F (z,v)=
      ‖cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex δ) (z,v))‖^2+
        cubicThetaSectionEnergy F (δ • cubicThetaVerticalPoint z v hv) := by
  have h := cubicThetaCuspCoordinateEnergy_apply δ F (cubicThetaVerticalPoint z v hv)
  change cubicThetaCuspCoordinateEnergy δ F (z,v)=_ at h
  rw [cubicThetaCusp_raw_norm δ F z hv]
  exact h

lemma cubicThetaSectionEnergy_nonneg (F : cubicThetaSmoothTests) (p : CubicThetaPoint) :
    0≤cubicThetaSectionEnergy F p :=
  mul_nonneg (sq_nonneg _) (cubicThetaTangentEnergy_nonneg _)

end CubicFirstMoment

end

end OAI
