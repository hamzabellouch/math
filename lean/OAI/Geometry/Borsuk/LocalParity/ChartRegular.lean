import Mathlib
import OAI.Geometry.Borsuk.SphereGeometry.HemisphereChart

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace Topology
open Filter
section ChartRegular
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [FiniteDimensional ℝ W]
omit [CompleteSpace E] [CompleteSpace W] [FiniteDimensional ℝ W] in
lemma hemisphereChart_zero {c : E} (hc : ‖c‖ = 1) (e : W →ₗᵢ[ℝ] E) : hemisphereChart c e 0 = c := by
  simp [hemisphereChart,SimplicialChains.unitRadial,hc]
omit [FiniteDimensional ℝ W] in
lemma hemisphereInverse_self {c : E} (_hc : ‖c‖ = 1) (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0) :
    hemisphereInverse c e c = 0 := by simp [hemisphereInverse,adjoint_normal c e he]
omit [FiniteDimensional ℝ W] in
lemma hemisphereInverse_contDiffAt (w : E) (e : W →ₗᵢ[ℝ] E) {u : E} (hu : ⟪w,u⟫ ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (hemisphereInverse w e) u :=
  ((contDiffAt_const.inner ℝ contDiffAt_id).inv hu).smul e.toContinuousLinearMap.adjoint.contDiff.contDiffAt

omit [FiniteDimensional ℝ W] in
lemma hemisphere_transition_regular {w c : E} (hw : ‖w‖ = 1) (hc : ‖c‖ = 1)
    (e d : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪w,e v⟫ = 0) (hd : ∀ v, ⟪c,d v⟫ = 0)
    (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) (_hds : ∀ u, ⟪c,u⟫ = 0 → ∃ v, d v = u)
    (hwc : 0 < ⟪w,c⟫) (f : E → W) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hr : (fderiv ℝ (fun v => f (hemisphereChart w e v)) (hemisphereInverse w e c)).det ≠ 0) :
    (fderiv ℝ (fun v => f (hemisphereChart c d v)) 0).det ≠ 0 := by
  let T : W → W := fun v => hemisphereInverse w e (hemisphereChart c d v)
  let S : W → W := fun v => hemisphereInverse c d (hemisphereChart w e v)
  let v₀ := hemisphereInverse w e c
  have hTc : T 0 = v₀ := by simp [T,v₀,hemisphereChart_zero hc]
  have hwc' : hemisphereChart w e v₀ = c := hemisphereChart_inverse w e hw he hes hc hwc
  have hT : ContDiffAt ℝ (⊤ : ℕ∞) T 0 :=
    (hemisphereInverse_contDiffAt w e (by simpa only [hemisphereChart_zero hc] using ne_of_gt hwc)).comp 0
      (hemisphereChart_contDiff c d hc hd).contDiffAt
  have hS : ContDiffAt ℝ (⊤ : ℕ∞) S v₀ :=
    (hemisphereInverse_contDiffAt c d (by rw [hwc']; simp [hc])).comp v₀
      (hemisphereChart_contDiff w e hw he).contDiffAt
  have hnear : ∀ᶠ v in 𝓝 (0:W), 0 < ⟪w,hemisphereChart c d v⟫ :=
    (continuous_const.inner (hemisphereChart_contDiff c d hc hd).continuous).continuousAt
      (isOpen_Ioi.mem_nhds (by simpa only [hemisphereChart_zero hc,Set.mem_Ioi] using hwc))
  have hST : (fun v => S (T v)) =ᶠ[𝓝 (0:W)] id := by
    filter_upwards [hnear] with v hv
    dsimp [S,T]
    rw [hemisphereChart_inverse w e hw he hes (hemisphereChart_norm c d hc hd v) hv,
      hemisphereInverse_chart c d hc hd]
  have hdT := hT.differentiableAt (by simp)
  have hdS := hS.differentiableAt (by simp)
  have hdS' : HasFDerivAt S (fderiv ℝ S v₀) (T 0) := by rw [hTc]; exact hdS.hasFDerivAt
  have hcomp : (fderiv ℝ S v₀).comp (fderiv ℝ T 0) = ContinuousLinearMap.id ℝ W :=
    (hdS'.comp 0 hdT.hasFDerivAt).unique ((hasFDerivAt_id (0:W)).congr_of_eventuallyEq hST)
  have hTdet : (fderiv ℝ T 0).det ≠ 0 := by
    have composition_det := congrArg ContinuousLinearMap.det hcomp
    change LinearMap.det ((fderiv ℝ S v₀).toLinearMap.comp (fderiv ℝ T 0).toLinearMap) =
      LinearMap.det (LinearMap.id : W →ₗ[ℝ] W) at composition_det
    rw [LinearMap.det_comp, LinearMap.det_id] at composition_det
    have nonzero_product : (fderiv ℝ S v₀).det * (fderiv ℝ T 0).det ≠ 0 := by
      rw [composition_det]
      exact one_ne_zero
    exact (mul_ne_zero_iff.mp nonzero_product).2
  let g : W → W := fun v => f (hemisphereChart w e v)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (hemisphereChart_contDiff w e hw he)
  have hfg : (fun v => f (hemisphereChart c d v)) =ᶠ[𝓝 (0:W)] (fun v => g (T v)) := by
    filter_upwards [hnear] with v hv
    dsimp [g,T]
    rw [hemisphereChart_inverse w e hw he hes (hemisphereChart_norm c d hc hd v) hv]
  have hgT : HasFDerivAt g (fderiv ℝ g v₀) (T 0) := by
    rw [hTc]
    exact (hg.differentiable (by simp) v₀).hasFDerivAt
  have hfinal := (hgT.comp 0 hdT.hasFDerivAt).congr_of_eventuallyEq hfg
  rw [hfinal.fderiv]
  change LinearMap.det ((fderiv ℝ g v₀).toLinearMap.comp (fderiv ℝ T 0).toLinearMap) ≠ 0
  rw [LinearMap.det_comp]
  exact mul_ne_zero hr hTdet
end ChartRegular
end BorsukNine

end OAI
