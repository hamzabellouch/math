import Mathlib
import OAI.Analysis.Conductivity.Geometry.AffineCylinder

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
local instance affineCylinderIntegralMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance affineCylinderIntegralProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma integrable_affineEndCoordinates {a b l r R : ℝ} (ha : a≠0)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Integrable F ((FiniteAxisMeasure R).prod volume)) :
    Integrable (F ∘ affineEndCoordinates a b) ((volume.restrict (Ioc l r)).prod volume) := by
  have hle := affineEndCoordinates_interval_le ha hT
  have hν : sourceCylinderMeasure 0 R=(FiniteAxisMeasure R).prod volume := by
    rfl
  have hμ : sourceCylinderMeasure l r=(volume.restrict (Ioc l r)).prod volume := by
    rfl
  rw [hν,hμ] at hle
  have h := (hF.smul_measure (c:=ENNReal.ofReal |a⁻¹|) ENNReal.ofReal_ne_top).mono_measure hle
  exact (integrable_map_measure h.aestronglyMeasurable
    (measurable_affineEndCoordinates a b).aemeasurable).mp h

lemma integral_affineEndCoordinates_pos {a b l r R : ℝ} (ha : 0<a) (hlr : l≤r)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (hl : a*(l-b)=0) (hr : a*(r-b)=R) (hR : 0≤R)
    {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Integrable F ((FiniteAxisMeasure R).prod volume)) :
    |a| *(∫ z,F (affineEndCoordinates a b z) ∂(volume.restrict (Ioc l r)).prod volume)=
      ∫ z,F z ∂(FiniteAxisMeasure R).prod volume := by
  have hg := integrable_affineEndCoordinates ha.ne' hT hF
  rw [integral_prod (fun z => F (affineEndCoordinates a b z)) hg,integral_prod F hF,abs_of_pos ha,
    ←intervalIntegral.integral_of_le hlr,←intervalIntegral.integral_of_le hR]
  have he : (fun t => ∫ θ,F (affineEndCoordinates a b (t,θ)))=
      (fun t => (fun u => ∫ θ,F (u,θ)) (a*t-a*b)) := by
    funext t
    simp only [affineEndCoordinates,Prod.map_apply,affineEndTime,id_eq]
    rw [mul_sub]
  rw [he]
  change a • (∫ t in l..r,(fun u => ∫ θ,F (u,θ)) (a*t-a*b))=_
  rw [intervalIntegral.smul_integral_comp_mul_sub (fun u => ∫ θ,F (u,θ)) a (a*b)]
  rw [←mul_sub,←mul_sub,hl,hr]

lemma integral_affineEndCoordinates_neg {a b l r R : ℝ} (ha : a<0) (hlr : l≤r)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (hl : a*(l-b)=R) (hr : a*(r-b)=0) (hR : 0≤R)
    {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Integrable F ((FiniteAxisMeasure R).prod volume)) :
    |a| *(∫ z,F (affineEndCoordinates a b z) ∂(volume.restrict (Ioc l r)).prod volume)=
      ∫ z,F z ∂(FiniteAxisMeasure R).prod volume := by
  have hg := integrable_affineEndCoordinates ha.ne hT hF
  rw [integral_prod (fun z => F (affineEndCoordinates a b z)) hg,integral_prod F hF,abs_of_neg ha,
    ←intervalIntegral.integral_of_le hlr,←intervalIntegral.integral_of_le hR]
  have he : (fun t => ∫ θ,F (affineEndCoordinates a b (t,θ)))=
      (fun t => (fun u => ∫ θ,F (u,θ)) (a*t-a*b)) := by
    funext t
    simp only [affineEndCoordinates,Prod.map_apply,affineEndTime,id_eq]
    rw [mul_sub]
  rw [he,neg_mul]
  change -(a • (∫ t in l..r,(fun u => ∫ θ,F (u,θ)) (a*t-a*b)))=_
  rw [intervalIntegral.smul_integral_comp_mul_sub (fun u => ∫ θ,F (u,θ)) a (a*b)]
  rw [←mul_sub,←mul_sub,hl,hr,intervalIntegral.integral_symm,neg_neg]

end ScalarConductivity

end
end

end OAI
