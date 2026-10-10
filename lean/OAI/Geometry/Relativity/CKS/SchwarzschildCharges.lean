import OAI.Geometry.Relativity.CKS.SchwarzschildCKS
import OAI.Geometry.Relativity.CKS.SchwarzschildArea
import OAI.Geometry.Relativity.CKS.SourceReplacementDefinitions

namespace OAI

noncomputable section
open Set Filter MeasureTheory CKSLorentz CKSSphericalHarmonics
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma sphere_coordinate_integral (i : Fin 3) :
    (∫ n : Sphere, (n : E3) i ∂surfaceMeasure) = 0 := by
  let u : E3 ≃ₗᵢ[ℝ] E3 := LinearIsometryEquiv.neg ℝ
  have h := (sphereHome_measurePreserving u).integral_comp
    (sphereHome u).measurableEmbedding (fun n : Sphere => (n : E3) i)
  change (∫ n : Sphere, -(n : E3) i ∂surfaceMeasure) = _ at h
  rw [integral_neg] at h
  linarith

lemma constant_bondi_charge (m : ℝ) : bondiCharge (fun _ => 4*m) = (m,0) := by
  apply Prod.ext
  · rw [charge_energy contMDiff_const,integral_const,CKSADM.surfaceMeasure_real]
    change (16*Real.pi)⁻¹ * ((4*Real.pi) * (4*m)) = m
    field_simp
    ring
  · apply PiLp.ext
    intro i
    rw [charge_momentum contMDiff_const,integral_const_mul,sphere_coordinate_integral]
    simp
lemma bondi_charge {m : ℝ} (hm : 0 < m) : bondiCharge (cksData hm).massAspect = (m,0) :=
  constant_bondi_charge m

lemma source_minimum_area {m : ℝ} (hm : 0 < m) :
    CKSSourceExterior.minimumEnclosingArea (smoothMetric hm) = 16*Real.pi*m^2 := by
  rw [CKSSourceExterior.minimumEnclosingArea_eq_toReal,full_minimum_enclosing_area hm,ENNReal.toReal_ofReal (by positivity)]

lemma numerical_equality {m : ℝ} (hm : 0 < m) :
    Real.sqrt ((bondiCharge (cksData hm).massAspect).1^2 -
      ‖(bondiCharge (cksData hm).massAspect).2‖^2) =
    Real.sqrt (CKSSourceExterior.minimumEnclosingArea (smoothMetric hm) / (16*Real.pi)) := by
  rw [bondi_charge hm,source_minimum_area hm]
  simp only [norm_zero,zero_pow (by decide : 2 ≠ 0),sub_zero]
  congr 1
  field_simp
end CKSSchwarzschild

end

end OAI
