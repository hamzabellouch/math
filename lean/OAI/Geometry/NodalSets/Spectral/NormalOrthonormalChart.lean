import OAI.Geometry.NodalSets.Charts.MetricConnectionFamilyLemmas
import OAI.Geometry.NodalSets.Elliptic.TaylorPolynomial
import OAI.Geometry.NodalSets.Spectral.OrthonormalMetricFrame

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def frameConnection (B : Coord →L[ℝ] Coord →L[ℝ] Coord) (e : Coord ≃L[ℝ] Coord) :
    Coord →L[ℝ] Coord →L[ℝ] Coord :=
  (((ContinuousLinearMap.compL ℝ Coord Coord Coord).flip e.toContinuousLinearMap).comp B).comp
    e.toContinuousLinearMap

lemma frameConnection_apply (B : Coord →L[ℝ] Coord →L[ℝ] Coord)
    (e : Coord ≃L[ℝ] Coord) (u v : Coord) : frameConnection B e u v = B (e u) (e v) := rfl

theorem positive_coordinate_frame (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hp : ∀ v : Coord, v ≠ 0 → 0 < g v v) (hs : ∀ u v, g u v = g v u) :
    ∃ e : Coord ≃L[ℝ] Coord, ∀ i j : Fin 4,
      g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i = j then 1 else 0 := by
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin 4) ℝ Coord,
      ∀ i j, g (b i) (b j) = if i = j then 1 else 0 := by
    have hdim : Module.finrank ℝ Coord = 4 := Module.finrank_fin_fun (R := ℝ)
    have h := positive_metric_orthonormal_basis g hp hs
    rw [hdim] at h
    exact h
  refine ⟨b.equivFunL.symm, ?_⟩
  intro i j
  have hei (i : Fin 4) : b.equivFunL.symm (Pi.single i 1) = b i := by
    apply b.equivFunL.injective
    rw [b.equivFunL.apply_symm_apply]
    ext k
    simp [Module.Basis.equivFunL, Module.Basis.equivFun, Pi.single_apply, Finsupp.single_apply, eq_comm]
  rw [hei, hei]
  exact hb i j

theorem exists_orthonormal_normal_chart
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
    (y : Coord) (hp : ∀ v : Coord, v ≠ 0 → 0 < g y v v) :
    ∃ F : OpenPartialHomeomorph Coord Coord,
      0 ∈ F.source ∧ F 0 = y ∧ ContDiff ℝ ∞ (F : Coord → Coord) ∧
      ContDiffAt ℝ ∞ F.symm y ∧
      (∀ i j : Fin 4, pullbackMetric g F 0 (Pi.single i 1) (Pi.single j 1) =
        if i = j then 1 else 0) ∧
      ∀ u v, fderiv ℝ (fun x ↦ pullbackMetric g F x u v) 0 = 0 := by
  have hd := (hg.differentiable (by simp)).differentiableAt.hasFDerivAt (x := y)
  obtain ⟨B, hB, hc⟩ := positive_metric_connection (g y) hp (hs y) (fderiv ℝ g y)
    (metric_derivative_symmetric g (fderiv ℝ g y) y hd hs)
  obtain ⟨e, he⟩ := positive_coordinate_frame (g y) hp (hs y)
  let C := frameConnection B e
  have hC : ∀ u v, C u v = C v u := fun u v ↦ hB (e u) (e v)
  refine ⟨quadraticChart y e C, quadraticChart_source y e C,
    quadraticChartMap_zero y e C, quadraticChartMap_smooth y e C,
    quadraticChart_inverse_smooth y e C, ?_, ?_⟩
  · intro i j
    rw [quadraticChart_coe, pullbackMetric_quadratic_zero]
    exact he i j
  · intro u v
    exact quadratic_chart_metric_first_zero g (fderiv ℝ g y) y hd e C hC
      (fun w u v ↦ hc (e w) (e u) (e v)) u v

end
end Yau.Geometry

end OAI
