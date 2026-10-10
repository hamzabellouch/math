import OAI.GroupTheory.PolycyclicRecognition.Geometry.LocalParameterSmoothness
import Mathlib.Geometry.Manifold.Algebra.LieGroup

namespace OAI

/-! # A smooth local section from an invertible parameter derivative -/

noncomputable section
namespace PolycyclicRecognition
open Set Filter
open scoped Manifold Topology ContDiff

variable {V E M : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

/-- The section is an actual function smooth at the base point, and is a
right inverse on a neighborhood; no global injectivity is required. -/
theorem exists_smooth_local_section
    {P : V → M} {x₀ : V} {d : V ≃L[ℝ] E}
    (hP : ContMDiffAt (𝓘(ℝ,V)) (𝓘(ℝ,E)) ∞ P x₀)
    (hd : HasMFDerivAt (𝓘(ℝ,V)) (𝓘(ℝ,E)) P x₀ d.toContinuousLinearMap) :
    ∃ r : M → V, ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,V)) ∞ r (P x₀) ∧
      r (P x₀) = x₀ ∧ ∀ᶠ x in 𝓝 (P x₀), P (r x) = x := by
  let φ := extChartAt (𝓘(ℝ,E)) (P x₀)
  let Q : V → E := φ ∘ P
  have hφ : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ φ (P x₀) := contMDiffAt_extChartAt
  have hQ : ContDiffAt ℝ ∞ Q x₀ := (hφ.comp x₀ hP).contDiffAt
  have hchart : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) φ (P x₀)
      (ContinuousLinearMap.id ℝ E) := by
    have hh := hφ.mdifferentiableAt (by simp) |>.hasMFDerivAt
    apply hh.congr_mfderiv
    change mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (extChartAt (𝓘(ℝ,E)) (P x₀)) (P x₀) = _
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
  have hr : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,V)) ∞ r (P x₀) :=
    hq.contMDiffAt.comp (P x₀) hφ
  have hr₀ : r (P x₀) = x₀ := hq₀
  refine ⟨r,hr,hr₀,?_⟩
  have hPr : ContinuousAt (P ∘ r) (P x₀) :=
    hP.continuousAt.comp_of_eq hr.continuousAt hr₀
  have hsource : ∀ᶠ x in 𝓝 (P x₀), x ∈ φ.source :=
    extChartAt_source_mem_nhds (I := 𝓘(ℝ,E)) (P x₀)
  have hPrsource : ∀ᶠ x in 𝓝 (P x₀), P (r x) ∈ φ.source :=
    hPr.preimage_mem_nhds (by
      rw [show (P ∘ r) (P x₀) = P x₀ from congrArg P hr₀]
      exact extChartAt_source_mem_nhds (I := 𝓘(ℝ,E)) (P x₀))
  filter_upwards [hsource,hPrsource,hφ.continuousAt.tendsto.eventually hright] with x hx hPx hQx
  exact φ.injOn hPx hx hQx

variable {EW W EY Y : Type*}
  [NormedAddCommGroup EW] [NormedSpace ℝ EW]
  [TopologicalSpace W] [ChartedSpace EW W]
  [NormedAddCommGroup EY] [NormedSpace ℝ EY]
  [TopologicalSpace Y] [ChartedSpace EY Y]

/-- Smoothness in a parameter and local coordinates in the second variable
descends through the actual smooth section. -/
theorem contMDiffAt_from_right_parameters
    {P : V → M} {x₀ : V} {d : V ≃L[ℝ] E} {w₀ : W} {f : W × M → Y}
    (hP : ContMDiffAt (𝓘(ℝ,V)) (𝓘(ℝ,E)) ∞ P x₀)
    (hd : HasMFDerivAt (𝓘(ℝ,V)) (𝓘(ℝ,E)) P x₀ d.toContinuousLinearMap)
    (hf : ContMDiffAt ((𝓘(ℝ,EW)).prod (𝓘(ℝ,V))) (𝓘(ℝ,EY)) ∞
      (fun p : W × V => f (p.1,P p.2)) (w₀,x₀)) :
    ContMDiffAt ((𝓘(ℝ,EW)).prod (𝓘(ℝ,E))) (𝓘(ℝ,EY)) ∞ f (w₀,P x₀) := by
  obtain ⟨r,hr,hr₀,he⟩ := exists_smooth_local_section hP hd
  have hq : ContMDiffAt ((𝓘(ℝ,EW)).prod (𝓘(ℝ,E)))
      ((𝓘(ℝ,EW)).prod (𝓘(ℝ,V))) ∞
      (fun p : W × M => (p.1,r p.2)) (w₀,P x₀) :=
    contMDiffAt_fst.prodMk (hr.comp (w₀,P x₀) contMDiffAt_snd)
  have hh := hf.comp_of_eq hq (Prod.ext rfl hr₀)
  apply hh.congr_of_eventuallyEq
  filter_upwards [continuousAt_snd.tendsto.eventually he] with p hp
  exact congrArg (fun y => f (p.1,y)) hp.symm

section Translation
variable {EG Q : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [TopologicalSpace Q] [ChartedSpace EG Q] [Group Q] [LieGroup (𝓘(ℝ,EG)) ⊤ Q]

/-- Right translation moves smoothness at the identity to every point. -/
theorem contMDiff_of_smooth_mul_right (a : Q × Q → Q)
    (h : ∀ g c, ContMDiffAt ((𝓘(ℝ,EG)).prod (𝓘(ℝ,EG))) (𝓘(ℝ,EG)) ∞
      (fun z : Q × Q => a (z.1,c * z.2)) (g,1)) :
    ContMDiff ((𝓘(ℝ,EG)).prod (𝓘(ℝ,EG))) (𝓘(ℝ,EG)) ∞ a := by
  intro p
  have ht : ContMDiffAt ((𝓘(ℝ,EG)).prod (𝓘(ℝ,EG)))
      ((𝓘(ℝ,EG)).prod (𝓘(ℝ,EG))) ∞
      (fun z : Q × Q => (z.1,p.2⁻¹ * z.2)) p :=
    contMDiffAt_fst.prodMk (contMDiffAt_const.mul contMDiffAt_snd)
  have he : (p.1,p.2⁻¹ * p.2) = (p.1,1) := by rw [inv_mul_cancel]
  have hh := (h p.1 p.2).comp_of_eq ht he
  apply hh.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro z
  change a z = a (z.1,p.2 * (p.2⁻¹ * z.2))
  rw [mul_inv_cancel_left]
end Translation

end PolycyclicRecognition

end

end OAI
