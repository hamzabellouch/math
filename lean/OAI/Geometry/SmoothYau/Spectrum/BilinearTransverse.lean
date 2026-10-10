import Mathlib

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def bilinearTransverse (G : E →L[ℝ] E →L[ℝ] ℝ) (a : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (G a a)⁻¹ • (G a).smulRight a
lemma bilinearTransverse_apply (G : E →L[ℝ] E →L[ℝ] ℝ) (a b : E) :
    bilinearTransverse G a b = b - ((G a a)⁻¹ * G a b) • a := by
  simp [bilinearTransverse,smul_smul]
lemma bilinearTransverse_kernel (G : E →L[ℝ] E →L[ℝ] ℝ) {a : E} (ha : G a a ≠ 0) :
    bilinearTransverse G a a = 0 := by
  simp [bilinearTransverse_apply,inv_mul_cancel₀ ha]
lemma bilinearTransverse_orthogonal (G : E →L[ℝ] E →L[ℝ] ℝ) {a : E}
    (ha : G a a ≠ 0) (b : E) : G a (bilinearTransverse G a b) = 0 := by
  rw [bilinearTransverse_apply,map_sub,map_smul,smul_eq_mul]
  field_simp
  ring
lemma bilinearTransverse_fixed (G : E →L[ℝ] E →L[ℝ] ℝ) {a b : E}
    (h : G a b = 0) : bilinearTransverse G a b = b := by
  simp [bilinearTransverse_apply,h]
lemma bilinearTransverse_selfAdjoint (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ a b, G a b = G b a) (a b c : E) :
    G (bilinearTransverse G a b) c = G b (bilinearTransverse G a c) := by
  simp only [bilinearTransverse_apply,map_sub,map_smul,sub_apply,
    smul_apply,smul_eq_mul]
  rw [hs b a]; ring
lemma bilinearTransverse_pair (G : E →L[ℝ] E →L[ℝ] ℝ)
    {a : E} (ha : G a a ≠ 0) (b : E) :
    G b (bilinearTransverse G a b) =
      G (bilinearTransverse G a b) (bilinearTransverse G a b) := by
  conv_rhs => lhs; rw [bilinearTransverse_apply]
  simp only [map_sub,map_smul,sub_apply,smul_apply,
    smul_eq_mul,bilinearTransverse_orthogonal G ha b,mul_zero,sub_zero]
lemma bilinearTransverse_trace [FiniteDimensional ℝ E] (G : E →L[ℝ] E →L[ℝ] ℝ) {a : E} (ha : G a a ≠ 0) :
    LinearMap.trace ℝ E (bilinearTransverse G a).toLinearMap =
      (Module.finrank ℝ E : ℝ) - 1 := by
  change LinearMap.trace ℝ E ((LinearMap.id : E →ₗ[ℝ] E) -
    (G a a)⁻¹ • (G a).toLinearMap.smulRight a) = _
  rw [map_sub,map_smul,LinearMap.trace_id,LinearMap.trace_smulRight,smul_eq_mul]
  change (Module.finrank ℝ E : ℝ) - (G a a)⁻¹ * G a a = _
  rw [inv_mul_cancel₀ ha]
def bilinearPinning (G : E →L[ℝ] E →L[ℝ] ℝ) (a b : E) : E →L[ℝ] E :=
  let p := bilinearTransverse G a b
  (G p).smulRight p - (G p p / 2) • bilinearTransverse G a
lemma bilinearPinning_selfAdjoint (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ a b, G a b = G b a) (a b v w : E) :
    G (bilinearPinning G a b v) w = G v (bilinearPinning G a b w) := by
  simp only [bilinearPinning,sub_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,map_sub,map_smul,smul_eq_mul]
  rw [bilinearTransverse_selfAdjoint G hs a v w,hs v (bilinearTransverse G a b)]
  ring
lemma bilinearPinning_kernel (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ a b, G a b = G b a) {a : E} (ha : G a a ≠ 0) (b : E) :
    bilinearPinning G a b a = 0 := by
  simp only [bilinearPinning,sub_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [hs,bilinearTransverse_orthogonal G ha,bilinearTransverse_kernel G ha]
  simp
lemma bilinearPinning_trace [FiniteDimensional ℝ E] (G : E →L[ℝ] E →L[ℝ] ℝ) {a : E} (ha : G a a ≠ 0)
    (b : E) (hd : Module.finrank ℝ E = 3) :
    LinearMap.trace ℝ E (bilinearPinning G a b).toLinearMap = 0 := by
  change LinearMap.trace ℝ E ((G (bilinearTransverse G a b)).toLinearMap.smulRight _ -
    (G _ _ / 2) • (bilinearTransverse G a).toLinearMap) = _
  rw [map_sub,map_smul,LinearMap.trace_smulRight,bilinearTransverse_trace G ha,hd]
  norm_num
lemma bilinearPinning_quadratic (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ a b, G a b = G b a) {a : E} (ha : G a a ≠ 0) (b : E) :
    G b (bilinearPinning G a b b) =
      (G (bilinearTransverse G a b) (bilinearTransverse G a b))^2 / 2 := by
  simp only [bilinearPinning,sub_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,map_sub,map_smul,smul_eq_mul]
  rw [hs (bilinearTransverse G a b) b,bilinearTransverse_pair G ha]
  ring
end YauCounterexamples

end

end OAI
