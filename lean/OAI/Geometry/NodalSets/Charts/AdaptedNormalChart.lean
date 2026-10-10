import OAI.Geometry.NodalSets.Charts.AdaptedMetricFrame
import OAI.Geometry.NodalSets.Spectral.NormalOrthonormalChart

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma basis_equivFunL_symm_single (b : Module.Basis (Fin 4) ℝ Coord) (i : Fin 4) :
    b.equivFunL.symm (Pi.single i 1) = b i := by
  apply b.equivFunL.injective
  rw [b.equivFunL.apply_symm_apply]
  ext k
  simp [Module.Basis.equivFunL, Module.Basis.equivFun, Pi.single_apply, Finsupp.single_apply, eq_comm]

theorem positive_coordinate_adapted_frame (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hp : ∀ v : Coord, v ≠ 0 → 0 < g v v) (hs : ∀ u v, g u v = g v u)
    (p q : Coord) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hpp : g p p = a^2) (hqq : g q q = b^2) (hpq : g p q = 0) :
    ∃ e : Coord ≃L[ℝ] Coord,
      e (Pi.single 0 1) = a⁻¹ • p ∧ e (Pi.single 1 1) = b⁻¹ • q ∧
      ∀ i j : Fin 4, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i = j then 1 else 0 := by
  let G : LinearMap.BilinForm ℝ Coord :=
    (LinearMap.toContinuousLinearMap : (Coord →ₗ[ℝ] ℝ) ≃ₗ[ℝ] Coord →L[ℝ] ℝ).symm.toLinearMap.comp
      g.toLinearMap
  have hdim : Module.finrank ℝ Coord = 4 := Module.finrank_fin_fun (R := ℝ)
  obtain ⟨v, hv0, hv1, hv⟩ := positive_form_adapted_basis G hp hs hdim p q a b ha hb hpp hqq hpq
  refine ⟨v.equivFunL.symm, ?_, ?_, ?_⟩
  · rw [basis_equivFunL_symm_single]; exact hv0
  · rw [basis_equivFunL_symm_single]; exact hv1
  · intro i j
    rw [basis_equivFunL_symm_single, basis_equivFunL_symm_single]
    exact hv i j

theorem exists_adapted_normal_chart
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
    (y : Coord) (hp : ∀ v : Coord, v ≠ 0 → 0 < g y v v)
    (p q : Coord) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hpp : g y p p = a^2) (hqq : g y q q = b^2) (hpq : g y p q = 0) :
    ∃ F : OpenPartialHomeomorph Coord Coord,
      0 ∈ F.source ∧ F 0 = y ∧ ContDiff ℝ ∞ (F : Coord → Coord) ∧
      ContDiffAt ℝ ∞ F.symm y ∧
      fderiv ℝ (F : Coord → Coord) 0 (Pi.single 0 1) = a⁻¹ • p ∧
      fderiv ℝ (F : Coord → Coord) 0 (Pi.single 1 1) = b⁻¹ • q ∧
      (∀ i j : Fin 4, pullbackMetric g F 0 (Pi.single i 1) (Pi.single j 1) =
        if i = j then 1 else 0) ∧
      ∀ u v, fderiv ℝ (fun x ↦ pullbackMetric g F x u v) 0 = 0 := by
  have hd := (hg.differentiable (by simp)).differentiableAt.hasFDerivAt (x := y)
  obtain ⟨B, hB, hc⟩ := positive_metric_connection (g y) hp (hs y) (fderiv ℝ g y)
    (metric_derivative_symmetric g (fderiv ℝ g y) y hd hs)
  obtain ⟨e, he0, he1, he⟩ := positive_coordinate_adapted_frame (g y) hp (hs y) p q a b ha hb hpp hqq hpq
  let C := frameConnection B e
  have hC : ∀ u v, C u v = C v u := fun u v ↦ hB (e u) (e v)
  refine ⟨quadraticChart y e C, quadraticChart_source y e C,
    quadraticChartMap_zero y e C, quadraticChartMap_smooth y e C,
    quadraticChart_inverse_smooth y e C, ?_, ?_, ?_, ?_⟩
  · rw [quadraticChart_coe, (quadraticChartMap_deriv_zero y e C).fderiv]; exact he0
  · rw [quadraticChart_coe, (quadraticChartMap_deriv_zero y e C).fderiv]; exact he1
  · intro i j
    rw [quadraticChart_coe, pullbackMetric_quadratic_zero]
    exact he i j
  · intro u v
    exact quadratic_chart_metric_first_zero g (fderiv ℝ g y) y hd e C hC
      (fun w u v ↦ hc (e w) (e u) (e v)) u v

end
end Yau.Geometry

end OAI
