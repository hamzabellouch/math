import OAI.Geometry.NodalSets.Charts.AdaptedChartFamilyLemmas
import OAI.Geometry.NodalSets.Charts.ChartHessianLemmas
import OAI.Geometry.NodalSets.Elliptic.PhaseContactFamily

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def metricGradient (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ) (y : Coord) : Coord :=
  ContinuousLinearMap.inverse (g y) (fderiv ℝ S y)

lemma metricGradient_pair (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    (y : Coord) (hp : ∀ v, v ≠ 0 → 0 < g y v v) (v : Coord) :
    g y (metricGradient g S y) v = fderiv ℝ S y v := by
  have hi : ContinuousLinearMap.inverse (g y) = (positiveMetricEquiv (g y) hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv (g y) hp)
  change positiveMetricEquiv (g y) hp (ContinuousLinearMap.inverse (g y) (fderiv ℝ S y)) v = _
  rw [hi, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

lemma metricGradient_continuous (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ y v, v ≠ 0 → 0 < g y v v)
    (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S) : Continuous (metricGradient g S) :=
  (positive_metric_inverse_continuous g hg.continuous hp).clm_apply
    (hS.continuous_fderiv (by simp))

def sourceHessian (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    (y : Coord) : Coord →L[ℝ] Coord →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ S) y -
    (ContinuousLinearMap.compL ℝ Coord Coord ℝ (fderiv ℝ S y)).comp
      (metricConnection (g y) (fderiv ℝ g y))

lemma sourceHessian_apply (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    (y u v : Coord) : sourceHessian g S y u v =
      fderiv ℝ (fderiv ℝ S) y u v - fderiv ℝ S y (metricConnection (g y) (fderiv ℝ g y) u v) := rfl

lemma directional_second (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S) (y u v : Coord) :
    fderiv ℝ (fun x ↦ fderiv ℝ S x u) y v = fderiv ℝ (fderiv ℝ S) y v u := by
  rw [fderiv_clm_apply]
  · simp
  · exact ((hS.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) y
  · exact differentiableAt_const _

theorem charted_envelope_hessian
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S) (y : Coord) (e : Coord ≃L[ℝ] Coord)
    (i j : Fin 4) :
    envelopeHessian (S ∘ actualMetricChart g y e) i j =
      sourceHessian g S y (e (Pi.single j 1)) (e (Pi.single i 1)) := by
  change fderiv ℝ (fderiv ℝ (S ∘ quadraticChartMap y e (actualFrameConnection g y e))) 0
    (Pi.single j 1) (Pi.single i 1) = _
  rw [← directional_second _ (hS.comp (quadraticChartMap_smooth _ _ _))]
  rw [scalar_chart_hessian S hS y e _
    (fun u v ↦ actual_connection_symmetric g hg hs hp y (e u) (e v))]
  rfl

lemma orthonormal_frame_pair (g : Coord →L[ℝ] Coord →L[ℝ] ℝ) (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i = j then 1 else 0)
    (i : Fin 4) (x : Coord) : g (e (Pi.single i 1)) (e x) = x i := by
  have hx : e x = ∑ j, x j • e (Pi.single j 1) := by
    conv_lhs => rw [coord_expansion x]
    simp
  rw [hx]
  simp [map_sum, he, mul_ite]

theorem charted_envelope_adapted_data
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S) (y : Coord) (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i = j then 1 else 0)
    (q : Coord) (a b : ℝ)
    (ha : a • e (Pi.single 0 1) = metricGradient g S y)
    (hb : b • e (Pi.single 1 1) = q)
    (hstrict : 0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
      sourceHessian g S y q q) :
    (∀ x : Coord, fderiv ℝ (S ∘ actualMetricChart g y e) 0 x = a*x 0) ∧
    0 < a^2*envelopeHessian (S ∘ actualMetricChart g y e) 0 0 +
      b^2*envelopeHessian (S ∘ actualMetricChart g y e) 1 1 := by
  constructor
  · intro x
    rw [show (actualMetricChart g y e : Coord → Coord) =
      quadraticChartMap y e (actualFrameConnection g y e) from rfl, scalar_chart_first S hS]
    change fderiv ℝ S y (e x) = _
    rw [← metricGradient_pair g S y (hp y) (e x), ← ha]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [orthonormal_frame_pair (g y) e he]
  · rw [charted_envelope_hessian g hg hs hp S hS, charted_envelope_hessian g hg hs hp S hS]
    rw [← ha, ← hb] at hstrict
    simp only [map_smul, smul_apply, smul_eq_mul] at hstrict
    nlinarith

variable {T : Type*} [TopologicalSpace T]

lemma envelopeHessian_family_continuous (S : T → Coord → ℝ)
    (hc : Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ 2 (S z.1) z.2)) (i j : Fin 4) :
    Continuous (fun t ↦ envelopeHessian (S t) i j) := by
  have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ Coord) ℝ
    ![Pi.single j 1, Pi.single i 1]).continuous.comp (hc.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : T ↦ (0:Coord)))))
  simpa only [envelopeHessian, Function.comp_def, id_eq, ContinuousMultilinearMap.apply_apply, iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using h

end
end Yau.Geometry

end OAI
