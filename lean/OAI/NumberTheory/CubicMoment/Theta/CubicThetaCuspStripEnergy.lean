import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStripMeasure
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateIntegrability

namespace OAI

/-! Finite scalar mass and energy on the exact half-open high cusp
strip. These are the Fubini bounds for the radial Hardy estimate. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaHorizontalCell : Set ℂ :=
  {z | ∀ i, cubicThetaPeriodCoordinates z i∈Ico (0:ℝ) 1}

lemma cubicThetaCuspStrip_coordinates {H : ℝ} (hH : 0≤H) :
    cubicThetaPointCoordinates '' cubicThetaCuspStrip H=
      cubicThetaHorizontalCell ×ˢ Ioi H := by
  ext y
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨hp.2,hp.1⟩
  · rintro ⟨hy,hv⟩
    exact ⟨⟨y,lt_of_le_of_lt hH hv⟩,⟨hv,hy⟩,rfl⟩

lemma cubicThetaCuspStrip_intrinsic_integrable {H : ℝ} (hH : 1≤H)
    (F : cubicThetaSmoothTests) :
    IntegrableOn (fun p => cubicThetaSectionNorm F (cubicThetaQuotientMap p)^2+
      cubicThetaSectionEnergy F p) (cubicThetaCuspStrip H) cubicThetaPointMeasure := by
  have h := (cubicThetaIntrinsicEnergy_integrable F).integrableOn
    (s:=cubicThetaQuotientMap '' cubicThetaCuspStrip H)
  unfold IntegrableOn at h
  rw [← cubicThetaInjective_map_restrict (cubicThetaCuspStrip_measurable H)
    (cubicThetaCuspStrip_injective hH)] at h
  have hi := h.comp_measurable cubicThetaQuotientMap_open.continuous.measurable
  simpa only [IntegrableOn,Function.comp_def,cubicThetaQuotientEnergy_apply] using hi

def cubicThetaCoordinateIntrinsicEnergy (F : cubicThetaSmoothTests) (y : ℂ × ℝ) : ℝ :=
  cubicThetaSectionNorm F (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))^2+
    cubicThetaSectionEnergy F (cubicThetaPointInclusion.symm y)

lemma cubicThetaCoordinateIntrinsicEnergy_apply (F : cubicThetaSmoothTests) (p : CubicThetaPoint) :
    cubicThetaCoordinateIntrinsicEnergy F (cubicThetaPointCoordinates p)=
      cubicThetaSectionNorm F (cubicThetaQuotientMap p)^2+cubicThetaSectionEnergy F p := by
  have h : cubicThetaPointInclusion.symm (cubicThetaPointCoordinates p)=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  simp only [cubicThetaCoordinateIntrinsicEnergy,h]

theorem cubicThetaCuspStrip_coordinate_integrable {H : ℝ} (hH : 1≤H)
    (F : cubicThetaSmoothTests) :
    IntegrableOn (fun y => cubicThetaCoordinateIntrinsicEnergy F y/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi H) := by
  rw [← cubicThetaCuspStrip_coordinates (zero_le_one.trans hH),
    ← cubicThetaPointIntegrable_density (cubicThetaCuspStrip_measurable H)]
  simpa only [cubicThetaCoordinateIntrinsicEnergy_apply] using
    cubicThetaCuspStrip_intrinsic_integrable hH F

end CubicFirstMoment

end

end OAI
