import Mathlib
import OAI.Geometry.SmoothYau.Limits.C1ExtensionNearCompact

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
namespace YauCounterexamples
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma local_integration_by_parts_C1 {O : Set E} (hO : IsOpen O)
    {f F : E → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ O) (hF : ContDiffOn ℝ 1 F O) (v : E) :
    (∫ x in O, f x * fderiv ℝ F x v) = -(∫ x in O, fderiv ℝ f x v * F x) := by
  obtain ⟨H, hH, he⟩ := C1_extension_near_compact hfc hO hfs hF
  have he' (x : E) (hx : x ∈ tsupport f) : F =ᶠ[𝓝 x] H :=
    he.filter_mono (nhds_le_nhdsSet hx)
  have hdf := (hf.fderiv_right (m := 0) (by simp)).clm_apply (contDiff_const (c := v))
  have hdH := (hH.fderiv_right (m := 0) (by simp)).clm_apply (contDiff_const (c := v))
  have h1 (x : E) : f x * fderiv ℝ F x v = f x * fderiv ℝ H x v := by
    by_cases hx : x ∈ tsupport f
    · rw [(he' x hx).fderiv_eq]
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have h2 (x : E) : fderiv ℝ f x v * F x = fderiv ℝ f x v * H x := by
    by_cases hx : x ∈ tsupport f
    · rw [(he' x hx).eq_of_nhds]
    · rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
  simp_rw [h1, h2]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (mt (@hfs x) hx), zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [fderiv_of_notMem_tsupport ℝ (mt (@hfs x) hx)]; simp)]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (hdf.continuous.mul hH.continuous |>.integrable_of_hasCompactSupport
      ((hfc.fderiv_apply ℝ v).mul_right))
    (hf.continuous.mul hdH.continuous |>.integrable_of_hasCompactSupport hfc.mul_right)
    (hf.continuous.mul hH.continuous |>.integrable_of_hasCompactSupport hfc.mul_right)
    (fun x _ => (hf.differentiable (by simp)).differentiableAt)
    (fun x _ => (hH.differentiable (by simp)).differentiableAt)

end YauCounterexamples

end

end OAI
