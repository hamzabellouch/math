import OAI.Geometry.SurfaceImmersion.Correction.SmoothParameterIntegral
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace OAI

/-! Parameter integration on an open admissible domain, localized by a smooth cutoff. -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

universe u

namespace ClosedSurfaceR4.SmoothParameterIntegral

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [FiniteDimensional ℝ P] [CompleteSpace E] in
/-- A cutoff supported inside the parameter domain turns a locally smooth
family into a globally smooth family without changing its values near the center. -/
lemma contDiff_supported_smul {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ)) {χ : P → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ S) :
    ContDiff ℝ ∞ (fun z : P × ℝ => χ z.1 • F z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z.1 ∈ S
  · exact (hχ.comp contDiff_fst).contDiffAt.smul
      ((hF z ⟨hz, mem_univ z.2⟩).contDiffAt ((hS.prod isOpen_univ).mem_nhds ⟨hz, mem_univ z.2⟩))
  · have hn : z.1 ∉ tsupport χ := fun h => hz (hsupp h)
    have he : χ =ᶠ[𝓝 z.1] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hn] with p hp
      exact image_eq_zero_of_notMem_tsupport hp
    have he' := he.comp_tendsto (continuous_fst.continuousAt :
      Tendsto Prod.fst (𝓝 z) (𝓝 z.1))
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [he'] with w hw
    exact (congrArg (fun a : ℝ => a • F w) hw).trans (zero_smul ℝ (F w))

omit [CompleteSpace E] in
lemma exists_smooth_extension_near {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ)) {p : P} (hp : p ∈ S) :
    ∃ G : P × ℝ → E, ContDiff ℝ ∞ G ∧
      ∀ᶠ q in 𝓝 p, ∀ t : ℝ, G (q, t) = F (q, t) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS p hp
  let χ : ContDiffBump p := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hsupp : tsupport (χ : P → ℝ) ⊆ S := by
    rw [χ.tsupport_eq]
    exact (closedBall_subset_ball (by change ε / 2 < ε; linarith)).trans hball
  refine ⟨fun z => χ z.1 • F z, contDiff_supported_smul hS hF χ.contDiff hsupp, ?_⟩
  filter_upwards [χ.eventuallyEq_one] with q hq
  intro t
  rw [show χ q = 1 from hq, one_smul]

/-- Smooth parameter integrals require smoothness only over the open parameter
region where the geometric data are admissible. -/
theorem contDiffOn_integral {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ)) (a b : ℝ) :
    ContDiffOn ℝ ∞ (fun p => ∫ t in a..b, F (p, t)) S := by
  apply hS.contDiffOn_iff.mpr
  intro p hp
  obtain ⟨G, hG, he⟩ := exists_smooth_extension_near hS hF hp
  apply (contDiff_integral hG a b).contDiffAt.congr_of_eventuallyEq
  filter_upwards [he] with q hq
  exact intervalIntegral.integral_congr (fun t _ => (hq t).symm)

omit [CompleteSpace E] in
/-- Differentiation under the integral at an admissible parameter. -/
theorem hasFDerivAt_integral_on {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ)) (a b : ℝ) {p : P} (hp : p ∈ S) :
    HasFDerivAt (fun q => ∫ t in a..b, F (q, t))
      (∫ t in a..b, partialDerivative F (p, t)) p := by
  obtain ⟨G, hG, he⟩ := exists_smooth_extension_near hS hF hp
  have hd : (fun t => partialDerivative G (p, t)) =
      fun t => partialDerivative F (p, t) := by
    funext t
    have he' : G =ᶠ[𝓝 (p, t)] F := by
      filter_upwards [(continuous_fst.continuousAt :
        Tendsto Prod.fst (𝓝 (p, t)) (𝓝 p)).eventually he] with z hz
      exact hz z.2
    simp only [partialDerivative, he'.fderiv_eq]
  have h := hasFDerivAt_integral hG a b p
  rw [hd] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [he] with q hq
  exact intervalIntegral.integral_congr (fun t _ => (hq t).symm)

end ClosedSurfaceR4.SmoothParameterIntegral

end

end OAI
