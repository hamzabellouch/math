import Mathlib
import OAI.Analysis.SymmetricDomains.CoordinateFieldApply

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph
open scoped Classical
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

 theorem coordinateField_analytic (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) {X : Affine n → Affine n} (hX : AnalyticOnNhd ℂ X U) :
    AnalyticOnNhd ℂ (coordinateField e X) D := by
  apply analyticOnNhd_of_differentiableOn_affine hD
  intro x hx
  let p : D := ⟨x,hx⟩
  let y : U := e.toHomeomorph.symm p
  have hg : DifferentiableAt ℂ e.symm.ambientMap x :=
    (e.symm.ambientMap_analytic hD x hx).differentiableAt
  have he : e.symm.ambientMap x=y.val := ambientMap_apply e.symm p
  have hF := (e.ambientMap_analytic hU y.val y.property).fderiv.differentiableAt
  have hG := (hX y.val y.property).differentiableAt
  rw [←he] at hF hG
  have hh := (hF.comp x hg).clm_apply (hG.comp x hg)
  apply (hh.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hD.mem_nhds hx] with z hz
  rw [coordinateField_apply e X ⟨z,hz⟩]
  simp only [Function.comp_def,ambientMap_apply e.symm ⟨z,hz⟩,mapDerivative]
  rfl

 theorem coordinateField_eq_pullback (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) (X : Affine n → Affine n) (p : D) :
    coordinateField e X p.val=VectorField.pullback ℂ e.symm.ambientMap X p.val := by
  rw [VectorField.pullback_eq_of_fderiv_eq
    (M := mapDerivativeEquiv hD hU e.symm p) rfl]
  change coordinateField e X p.val=e.mapDerivative (e.toHomeomorph.symm p)
    (X (e.symm.ambientMap p.val))
  rw [ambientMap_apply,coordinateField_apply]
  rfl

 theorem coordinateField_lieBracket (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) {X Y : Affine n → Affine n}
    (hX : AnalyticOnNhd ℂ X U) (hY : AnalyticOnNhd ℂ Y U) :
    coordinateField e (VectorField.lieBracket ℂ X Y)=
      VectorField.lieBracket ℂ (coordinateField e X) (coordinateField e Y) := by
  funext x
  by_cases hx : x∈D
  · have hXeq : coordinateField e X =ᶠ[𝓝 x] VectorField.pullback ℂ e.symm.ambientMap X := by
      filter_upwards [hD.mem_nhds hx] with z hz
      exact coordinateField_eq_pullback hU hD e X ⟨z,hz⟩
    have hYeq : coordinateField e Y =ᶠ[𝓝 x] VectorField.pullback ℂ e.symm.ambientMap Y := by
      filter_upwards [hD.mem_nhds hx] with z hz
      exact coordinateField_eq_pullback hU hD e Y ⟨z,hz⟩
    rw [coordinateField_eq_pullback hU hD e _ ⟨x,hx⟩,
      hXeq.lieBracket_vectorField_eq hYeq]
    apply VectorField.pullback_lieBracket (le_top : minSmoothness ℂ 2 ≤ ⊤)
      (e.symm.ambientMap_analytic hD x hx).contDiffAt
    · rw [ambientMap_apply e.symm ⟨x,hx⟩]
      exact (hX _ (e.toHomeomorph.symm ⟨x,hx⟩).property).differentiableAt
    · rw [ambientMap_apply e.symm ⟨x,hx⟩]
      exact (hY _ (e.toHomeomorph.symm ⟨x,hx⟩).property).differentiableAt
  · simp only [coordinateField,dite_eq_right hx,VectorField.lieBracket,map_zero,sub_zero]

def coordinateFieldLinear (e : Biholomorph U D) :
    (Affine n → Affine n) →ₗ[ℝ] (Affine m → Affine m) where
  toFun := coordinateField e
  map_add' X Y := by
    funext x
    by_cases hx : x∈D
    · simp only [coordinateField,dite_eq_left hx,Pi.add_apply,map_add]
    · simp only [coordinateField,dite_eq_right hx,Pi.add_apply,add_zero]
  map_smul' c X := by
    funext x
    by_cases hx : x∈D
    · simp only [coordinateField,dite_eq_left hx,Pi.smul_apply,
        ContinuousLinearMap.map_smul_of_tower,Real.ringHom_apply]
    · simp only [coordinateField,dite_eq_right hx,Pi.smul_apply,smul_zero,Real.ringHom_apply]

end Biholomorph
end Release061

end

end OAI
