import OAI.Geometry.NodalSets.Elliptic.CorrugationEnvelopeJets
import OAI.Geometry.NodalSets.Elliptic.CorrugationGlobalJets

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped ContDiff Topology
noncomputable section

lemma sourceHessian_add_at (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (S w : Coord → ℝ) {x : Coord} (hS : ContDiffAt ℝ ∞ S x)
    (hw : ContDiffAt ℝ ∞ w x) (u v : Coord) :
    sourceHessian g (S+w) x u v = sourceHessian g S x u v+sourceHessian g w x u v := by
  have hSn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 S y := (hS.of_le (by simp)).eventually (by simp)
  have hwn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 w y := (hw.of_le (by simp)).eventually (by simp)
  have he : fderiv ℝ (S+w) =ᶠ[𝓝 x] fderiv ℝ S+fderiv ℝ w := by
    filter_upwards [hSn,hwn] with y hy hz
    exact fderiv_add (hy.differentiableAt (by simp)) (hz.differentiableAt (by simp))
  rw [sourceHessian_apply,sourceHessian_apply,sourceHessian_apply,he.fderiv_eq,he.self_of_nhds]
  rw [fderiv_add ((hS.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    ((hw.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))]
  simp only [add_apply,Pi.add_apply]
  ring

lemma corrugationPeriodicWell_radius_zero_positive {amp : ℝ} (ha : 0 ≤ amp)
    (z v : ℝ × ℝ) (hr : corrugationCellRadius z = 0) :
    0 ≤ fderiv ℝ (fderiv ℝ (corrugationPeriodicWell amp)) z v v := by
  have hs := (corrugationCellRadius_properties z).2
  rw [hr] at hs
  have h1 : (corrugationCellPoint z).1 = 0 := by nlinarith [sq_nonneg (corrugationCellPoint z).2]
  have h2 : (corrugationCellPoint z).2 = 0 := by nlinarith [sq_nonneg (corrugationCellPoint z).1]
  have hz : corrugationCellPoint z = 0 := Prod.ext h1 h2
  rw [(corrugationPeriodicWell_global_jets amp z).2,hz]
  exact corrugationDiskWell_center_positive ha (1/4) v

lemma corrugated_envelope_global_hessian
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S χ : Coord → ℝ)
    {x : Coord} (hS : ContDiffAt ℝ ∞ S x) (hχ : ContDiff ℝ ∞ χ)
    (amp s : ℝ) {J : ℝ} (hJ : J ≠ 0) (R : ℝ) (a b : Coord →L[ℝ] ℝ)
    (y u v : Coord) :
    sourceHessian g (S+localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x u v =
      sourceHessian g S x u v + s*J*χ (R⁻¹ • (x-y))*
        fderiv ℝ (fderiv ℝ (corrugationPeriodicWell amp)) (corrugationFastMap J a b (x-y))
          (a.prod b u) (a.prod b v) +
      corrugationMetricError g χ (corrugationPeriodicWell amp) s J R a b y x u v := by
  rw [sourceHessian_add_at g S _ hS
    (localizedCorrugation_smooth χ _ hχ (corrugationPeriodicWell_smooth amp) _ _ _ _ _ _).contDiffAt,
    localizedCorrugation_metric_hessian g χ _ hχ (corrugationPeriodicWell_smooth amp) s hJ]
  ring

end
end Yau.Geometry

end OAI
