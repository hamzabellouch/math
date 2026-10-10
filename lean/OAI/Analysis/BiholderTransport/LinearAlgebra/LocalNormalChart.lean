import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma positive_bilinear_nonneg (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ v : E, v ≠ 0 → 0 < g v v) (v : E) : 0 ≤ g v v := by
  by_cases hv : v = 0
  · simp only [hv,map_zero,le_refl]
  · exact (hg v hv).le

lemma positive_bilinear_cauchy_schwarz (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ v : E, v ≠ 0 → 0 < g v v)
    (hsym : ∀ u v, g u v = g v u) (u v : E) :
    (g u v)^2 ≤ g u u * g v v := by
  by_cases hv : v = 0
  · simp only [hv,map_zero,mul_zero,zero_pow,le_refl,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
  have hgv : 0 < g v v := hg v hv
  have h := positive_bilinear_nonneg g hg ((g v v) • u - (g u v) • v)
  simp only [map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul] at h
  rw [hsym v u] at h
  have hmul : 0 ≤ g v v * (g u u * g v v - (g u v)^2) := by nlinarith [h]
  have hsub : 0 ≤ g u u * g v v - (g u v)^2 := (mul_nonneg_iff_of_pos_left hgv).mp hmul
  linarith

lemma positive_bilinear_abs_le (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ v : E, v ≠ 0 → 0 < g v v)
    (hsym : ∀ u v, g u v = g v u) (u v : E) :
    |g u v| ≤ Real.sqrt (g u u) * Real.sqrt (g v v) := by
  have hu := positive_bilinear_nonneg g hg u
  have hv := positive_bilinear_nonneg g hg v
  have h := positive_bilinear_cauchy_schwarz g hg hsym u v
  have hsq : (Real.sqrt (g u u) * Real.sqrt (g v v))^2 = g u u * g v v := by
    rw [mul_pow,Real.sq_sqrt hu,Real.sq_sqrt hv]
  have hn : 0 ≤ Real.sqrt (g u u) * Real.sqrt (g v v) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [sq_abs (g u v)]

end WeakMTWTransport

open MeasureTheory
open scoped ContDiff ENNReal

end

end OAI
