import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

namespace OAI

/-! # Testing smoothness in local parameters

A smooth parametrization with invertible derivative supplies local smooth
coordinates, by the ordinary inverse function theorem.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Function
open scoped Manifold Topology ContDiff

variable {V E A M : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

theorem contMDiffAt_of_local_parameterization
    {P : V → M} {x₀ : V} {d : V ≃L[ℝ] E} {f : M → A}
    (hP : ContMDiffAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) ∞ P x₀)
    (hd : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) P x₀ d.toContinuousLinearMap)
    (hfP : ContDiffAt ℝ ∞ (f ∘ P) x₀) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ f (P x₀) := by
  let φ := extChartAt (𝓘(ℝ, E)) (P x₀)
  let Q : V → E := φ ∘ P
  have hφ : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ (P x₀) :=
    contMDiffAt_extChartAt
  have hQ : ContDiffAt ℝ ∞ Q x₀ := (hφ.comp x₀ hP).contDiffAt
  have hchart : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (P x₀)
      (ContinuousLinearMap.id ℝ E) := by
    have hh := hφ.mdifferentiableAt (by simp) |>.hasMFDerivAt
    apply hh.congr_mfderiv
    change mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) (P x₀)) (P x₀) = _
    rw [mfderiv_extChartAt_self]
    rfl
  have hQd : HasFDerivAt Q d.toContinuousLinearMap x₀ := by
    have hh : HasFDerivAt Q ((ContinuousLinearMap.id ℝ E).comp d.toContinuousLinearMap) x₀ :=
      (hchart.comp x₀ hd).hasFDerivAt
    simpa only [ContinuousLinearMap.id_comp] using hh
  let q : E → V := hQ.localInverse hQd (by simp)
  have hq : ContDiffAt ℝ ∞ q (Q x₀) := hQ.to_localInverse hQd (by simp)
  have hq₀ : q (φ (P x₀)) = x₀ := hQ.localInverse_apply_image hQd (by simp)
  have hright : ∀ᶠ y in 𝓝 (Q x₀), Q (q y) = y :=
    (hQ.hasStrictFDerivAt' hQd (by simp)).eventually_right_inverse
  let r : M → V := q ∘ φ
  have hr : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ r (P x₀) :=
    hq.contMDiffAt.comp (P x₀) hφ
  have hr₀ : r (P x₀) = x₀ := hq₀
  have hPr : ContinuousAt (P ∘ r) (P x₀) :=
    hP.continuousAt.comp_of_eq hr.continuousAt hr₀
  have hsource : ∀ᶠ x in 𝓝 (P x₀), x ∈ φ.source :=
    extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) (P x₀)
  have hPrsource : ∀ᶠ x in 𝓝 (P x₀), P (r x) ∈ φ.source :=
    hPr.preimage_mem_nhds (by
      rw [show (P ∘ r) (P x₀) = P x₀ from congrArg P hr₀]
      exact extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) (P x₀))
  have heq : ∀ᶠ x in 𝓝 (P x₀), P (r x) = x := by
    filter_upwards [hsource, hPrsource, hφ.continuousAt.tendsto.eventually hright] with x hx hPx hQx
    exact φ.injOn hPx hx hQx
  have hresult := hfP.contMDiffAt.comp_of_eq hr hr₀
  apply hresult.congr_of_eventuallyEq
  filter_upwards [heq] with x hx
  exact congrArg f hx.symm

end PolycyclicRecognition

end

end OAI
