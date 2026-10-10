import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples
variable {𝕜 P E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup P] [Module 𝕜 P]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  (B : P →ₗ[𝕜] P →ₗ[𝕜] F) (e : P →ₗ[𝕜] E) (hd : DenseRange e)
  (C : ℝ) (hb : ∀ p q, ‖B p q‖ ≤ C * ‖e p‖ * ‖e q‖)

def partialBilinearExtension : P →ₗ[𝕜] (E →L[𝕜] F) where
  toFun p := (B p).extendOfNorm e
  map_add' p q := by
    ext x
    exact congrFun (hd.equalizer (by fun_prop) (by fun_prop) (by
      funext r
      change (B (p + q)).extendOfNorm e (e r) =
        (B p).extendOfNorm e (e r) + (B q).extendOfNorm e (e r)
      rw [LinearMap.extendOfNorm_eq hd ⟨C * ‖e (p + q)‖, hb (p + q)⟩,
        LinearMap.extendOfNorm_eq hd ⟨C * ‖e p‖, hb p⟩,
        LinearMap.extendOfNorm_eq hd ⟨C * ‖e q‖, hb q⟩]
      simp)) x
  map_smul' c p := by
    ext x
    exact congrFun (hd.equalizer (by fun_prop) (by fun_prop) (by
      funext r
      change (B (c • p)).extendOfNorm e (e r) = c • (B p).extendOfNorm e (e r)
      rw [LinearMap.extendOfNorm_eq hd ⟨C * ‖e (c • p)‖, hb (c • p)⟩,
        LinearMap.extendOfNorm_eq hd ⟨C * ‖e p‖, hb p⟩]
      simp)) x

lemma partialBilinearExtension_apply (p q : P) :
    partialBilinearExtension B e hd C hb p (e q) = B p q :=
  LinearMap.extendOfNorm_eq hd ⟨C * ‖e p‖, hb p⟩ q

lemma norm_partialBilinearExtension_le (hC : 0 ≤ C) (p : P) :
    ‖partialBilinearExtension B e hd C hb p‖ ≤ C * ‖e p‖ :=
  LinearMap.opNorm_extendOfNorm_le hd (mul_nonneg hC (norm_nonneg _)) (hb p)

def bilinearExtension : E →L[𝕜] E →L[𝕜] F :=
  (partialBilinearExtension B e hd C hb).extendOfNorm e

lemma bilinearExtension_apply (hC : 0 ≤ C) (p q : P) :
    bilinearExtension B e hd C hb (e p) (e q) = B p q := by
  rw [bilinearExtension, LinearMap.extendOfNorm_eq hd
    ⟨C, norm_partialBilinearExtension_le B e hd C hb hC⟩]
  exact partialBilinearExtension_apply B e hd C hb p q

lemma norm_bilinearExtension_le (hC : 0 ≤ C) :
    ‖bilinearExtension B e hd C hb‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le hd hC
    (norm_partialBilinearExtension_le B e hd C hb hC)

lemma bilinearExtension_bound (hC : 0 ≤ C) (u v : E) :
    ‖bilinearExtension B e hd C hb u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  have h := (bilinearExtension B e hd C hb u).le_opNorm v
  have h' := (bilinearExtension B e hd C hb).le_opNorm u
  exact h.trans (mul_le_mul_of_nonneg_right
    (h'.trans (mul_le_mul_of_nonneg_right (norm_bilinearExtension_le B e hd C hb hC)
      (norm_nonneg u))) (norm_nonneg v))
end YauCounterexamples

end

end OAI
