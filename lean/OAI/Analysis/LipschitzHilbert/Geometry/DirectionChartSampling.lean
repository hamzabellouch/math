import OAI.Analysis.LipschitzHilbert.Geometry.UnitDirectionCharts
import OAI.Analysis.LipschitzHilbert.Estimates.ProductSlopePrincipalValue
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace OAI

/-! Exact changes of coordinates and time in the directional integral. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

def planeCoordinatesLinear : (ℝ×ℝ) ≃ₗ[ℝ] Plane where
  toEquiv := planeCoordinates.toEquiv
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' c x := by ext i; fin_cases i <;> rfl

def planeCoordinatesContinuous : (ℝ×ℝ) ≃L[ℝ] Plane :=
  planeCoordinatesLinear.toContinuousLinearEquiv

@[simp] theorem planeCoordinatesContinuous_apply (z : ℝ×ℝ) :
    planeCoordinatesContinuous z=planeCoordinates z := rfl

@[simp] theorem planeCoordinatesContinuous_symm_apply (z : Plane) :
    planeCoordinatesContinuous.symm z=planeCoordinates.symm z := rfl

theorem sample_chart (d : Plane) (v : Plane → Plane) (t : ℝ) (x : Plane) :
    sample (chartField d v) t (directionChart d x)=directionChart d (sample v t x) := by
  simp only [sample,chartField,LinearIsometryEquiv.symm_apply_apply,map_sub,map_smul]

theorem shortTransform_chart (d : Plane) (v : Plane → Plane) (epsilon R : ℝ)
    (f : Plane → ℂ) (x : Plane) :
    shortTransform (chartField d v) epsilon R (f ∘ (directionChart d).symm)
      (directionChart d x)=shortTransform v epsilon R f x := by
  unfold shortTransform
  apply intervalIntegral.integral_congr
  intro t _
  simp only [sample_chart,Function.comp_apply,LinearIsometryEquiv.symm_apply_apply]

theorem sample_as_slope (v : Plane → Plane) (x : Plane) (t : ℝ)
    (h0 : v x 0≠0) :
    planeCoordinates.symm (sample v t x)=
      PacketRepresentation.productSlopeSample
        (fun z => v (planeCoordinates z) 1/v (planeCoordinates z) 0)
        (t*v x 0) (planeCoordinates.symm x) := by
  apply Prod.ext
  · rfl
  · simp only [PacketRepresentation.productSlopeSample, MeasurableEquiv.apply_symm_apply]
    change x 1-t*v x 1=x 1-(t*v x 0)*(v x 1/v x 0)
    field_simp

theorem shortTransform_as_slope (v : Plane → Plane) (x : Plane)
    (epsilon R : ℝ) (f : Plane → ℂ) (h0 : v x 0≠0) :
    shortTransform v epsilon R f x=
      PacketRepresentation.productSymmetricTruncation
        (fun z => v (planeCoordinates z) 1/v (planeCoordinates z) 0)
        (epsilon*v x 0) (R*v x 0) (f ∘ planeCoordinates) (planeCoordinates.symm x) := by
  let g := fun s : ℝ => s⁻¹ •
    ((f ∘ planeCoordinates) (PacketRepresentation.productSlopeSample
      (fun z => v (planeCoordinates z) 1/v (planeCoordinates z) 0) s (planeCoordinates.symm x))-
     (f ∘ planeCoordinates) (PacketRepresentation.productSlopeSample
      (fun z => v (planeCoordinates z) 1/v (planeCoordinates z) 0) (-s) (planeCoordinates.symm x)))
  have hg (t : ℝ) : g (t*v x 0)=(v x 0)⁻¹ •
      (t⁻¹ • (f (sample v t x)-f (sample v (-t) x))) := by
    dsimp only [g]
    rw [←sample_as_slope v x t h0,show -(t*v x 0)=(-t)*v x 0 by ring,
      ←sample_as_slope v x (-t) h0]
    simp only [Function.comp_apply,MeasurableEquiv.apply_symm_apply,mul_inv_rev,smul_smul]
  change _=∫ s in epsilon*v x 0..R*v x 0, g s
  rw [←intervalIntegral.smul_integral_comp_mul_right g (v x 0)]
  simp_rw [hg]
  rw [intervalIntegral.integral_smul,smul_smul,mul_inv_cancel₀ h0,one_smul]
  rfl

end LipschitzHilbert

end

end OAI
