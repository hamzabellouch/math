import Mathlib
import OAI.Analysis.Conductivity.Geometry.PhysicalCollarBand

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

def sourceCollarVolumeConstant : ℝ :=
  2/(faceRayDensityLower 1*faceRayDensityLower sourceRadialWidth)

lemma sourceCollarVolumeConstant_pos : 0<sourceCollarVolumeConstant := by
  apply div_pos (by norm_num)
  exact mul_pos (faceRayDensityLower_pos (by norm_num))
    (faceRayDensityLower_pos (by norm_num [sourceRadialWidth,sourceHole]))

lemma sourceClosedBand_sq_integral_le {u : (Fin 3 → ℝ) → ℝ}
    (hu : Measurable u) {l r M : ℝ} (hlr : l≤r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hi : Integrable (fun z : ℝ×UnitAddTorus (Fin 2) => u (sourceAngularCollar z.1 z.2)^2)
      ((volume.restrict (Ioc l r)).prod volume))
    (hb : ∀ᵐ t∂volume.restrict (Ioc l r),(∫ θ,u (sourceAngularCollar t θ)^2)≤M) :
    (∫ y in sourceClosedCollarBand l r,u y^2)≤ sourceCollarVolumeConstant*(r-l)*M := by
  have he : Integrable (fun y => u y^2) (sourceAngularCollarMeasure l r) := by
    unfold sourceAngularCollarMeasure
    exact (integrable_map_measure (hu.pow_const 2).aestronglyMeasurable
      continuous_uncurry_sourceAngularCollar.aemeasurable).mpr hi
  have hc : Integrable (fun y => u y^2)
      (ENNReal.ofReal sourceCollarVolumeConstant • sourceAngularCollarMeasure l r) :=
    he.smul_measure ENNReal.ofReal_ne_top
  have hle : volume.restrict (sourceClosedCollarBand l r)≤
      ENNReal.ofReal sourceCollarVolumeConstant • sourceAngularCollarMeasure l r :=
    (sourceClosedCollarBand_measure_le hl hr).trans (sourcePhysicalCollarMeasure_le hlr hl hr)
  have H := integral_mono_measure hle (Eventually.of_forall (fun y => sq_nonneg (u y))) hc
  rw [integral_smul_measure,ENNReal.toReal_ofReal sourceCollarVolumeConstant_pos.le] at H
  have hmap : (∫ y,u y^2 ∂sourceAngularCollarMeasure l r)=
      ∫ t in Ioc l r,∫ θ,u (sourceAngularCollar t θ)^2 := by
    unfold sourceAngularCollarMeasure
    rw [integral_map continuous_uncurry_sourceAngularCollar.aemeasurable
      (hu.pow_const 2).aestronglyMeasurable]
    exact integral_prod _ hi
  rw [hmap] at H
  have hb' : (∫ t in Ioc l r,∫ θ,u (sourceAngularCollar t θ)^2)≤(r-l)*M := by
    have hh := integral_mono_ae hi.integral_prod_left (integrable_const M) hb
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hlr),smul_eq_mul] using hh
  simpa only [smul_eq_mul,mul_assoc] using H.trans
    (mul_le_mul_of_nonneg_left hb' sourceCollarVolumeConstant_pos.le)

end ScalarConductivity

end

end OAI
