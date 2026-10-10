import OAI.Geometry.NodalSets.Charts.ChartedEnvelope
import OAI.Geometry.NodalSets.Elliptic.UniformTripleBounds
import OAI.Geometry.NodalSets.Waves.TripleWaveParameters

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma scalar_chart_covariant_diagonal
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (f : Coord → ℝ) (hf : ContDiff ℝ ∞ f) (y : Coord) (e : Coord ≃L[ℝ] Coord) (v : Coord) :
    iteratedFDeriv ℝ 2 (f ∘ actualMetricChart g y e) 0 (fun _ ↦ v) =
      sourceHessian g f y (e v) (e v) := by
  rw [iteratedFDeriv_two_apply]
  rw [← directional_second (f ∘ actualMetricChart g y e) (hf.comp (quadraticChartMap_smooth _ _ _)) 0 v v]
  rw [show (actualMetricChart g y e : Coord → Coord) = quadraticChartMap y e (actualFrameConnection g y e) from rfl]
  rw [scalar_chart_hessian f hf y e _
    (fun u v ↦ actual_connection_symmetric g hg hs hp y (e u) (e v))]
  rfl

lemma orthonormal_frame_norm_sq (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : Coord ≃L[ℝ] Coord)
    (ho : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) (v : Coord) :
    g (e v) (e v) = ∑ i, (v i)^2 := by
  have hv : e v = ∑ i, v i • e (Pi.single i 1) := by
    conv_lhs => rw [coord_expansion v]
    simp
  conv_lhs => arg 1; rw [hv]
  simp only [map_sum,sum_apply,map_smul,smul_apply,smul_eq_mul]
  simp_rw [frame_pair_coordinate g e ho,e.symm_apply_apply,pow_two]

lemma source_eta_of_adapted_frame
    (g H : Coord →L[ℝ] Coord →L[ℝ] ℝ) (e : Coord ≃L[ℝ] Coord)
    (ho : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (p q : Coord) (a b : ℝ) (ha : a • e (Pi.single 0 1) = p) (hb : b • e (Pi.single 1 1) = q) :
    Yau.contactEta a b (H (e (Pi.single 0 1)) (e (Pi.single 0 1)))
      (H (e (Pi.single 1 1)) (e (Pi.single 1 1))) = sourceDirectionEta g H p q := by
  rw [← ha,← hb]
  simp only [Yau.contactEta,sourceDirectionEta,map_smul,smul_apply,smul_eq_mul,ho,ite_true,mul_one]
  ring

end
end Yau.Geometry

end OAI
