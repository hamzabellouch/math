import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def iterateAverage (f : E → E) (N : ℕ) (x : E) : E :=
  ((N+1 : ℂ)⁻¹) • ∑ j ∈ Finset.range (N+1), f^[j] x

lemma analyticOnNhd_iterate {S : Set E} {f : E → E}
    (hf : AnalyticOnNhd ℂ f S) (hm : MapsTo f S S) (j : ℕ) :
    AnalyticOnNhd ℂ f^[j] S := by
  induction j with
  | zero => exact analyticOnNhd_id
  | succ j hj =>
    rw [Function.iterate_succ]
    exact hj.comp hf hm

lemma iterateAverage_analytic {S : Set E} {f : E → E}
    (hf : AnalyticOnNhd ℂ f S) (hm : MapsTo f S S) (N : ℕ) :
    AnalyticOnNhd ℂ (iterateAverage f N) S := by
  apply AnalyticOnNhd.const_smul
  apply Finset.analyticOnNhd_fun_sum
  intro j _
  exact analyticOnNhd_iterate hf hm j

lemma iterateAverage_bound {S : Set E} {f : E → E} (hm : MapsTo f S S)
    {M : ℝ} (hb : ∀ x ∈ S, ‖x‖ ≤ M) (N : ℕ) {x : E} (hx : x ∈ S) :
    ‖iterateAverage f N x‖ ≤ M := by
  have hn : (N+1 : ℝ) ≠ 0 := by positivity
  calc
    ‖iterateAverage f N x‖ = (N+1 : ℝ)⁻¹ * ‖∑ j ∈ Finset.range (N+1), f^[j] x‖ := by
      rw [iterateAverage,norm_smul,norm_inv]
      rw [show (N : ℂ)+1 = ((N+1 : ℕ) : ℂ) by simp only [Nat.cast_add, Nat.cast_one],
        Complex.norm_natCast]
      simp only [Nat.cast_add,Nat.cast_one]
    _ ≤ (N+1 : ℝ)⁻¹ * ∑ j ∈ Finset.range (N+1), ‖f^[j] x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (N+1 : ℝ)⁻¹ * ∑ _j ∈ Finset.range (N+1), M := by
      gcongr with j _
      exact hb _ ((hm.iterate j) hx)
    _ = M := by simp [hn]

lemma iterateAverage_deriv_fixed {f : E → E} {p : E}
    (hp : f p = p) (hd : HasFDerivAt f (1 : E →L[ℂ] E) p) (N : ℕ) :
    HasFDerivAt (iterateAverage f N) (1 : E →L[ℂ] E) p := by
  have h : ∀ j : ℕ, HasFDerivAt f^[j] (1 : E →L[ℂ] E) p := fun j => by
    simpa using hd.iterate hp j
  have ha := (HasFDerivAt.sum (fun j (_hj : j ∈ Finset.range (N+1)) => h j)).const_smul
    ((N+1 : ℂ)⁻¹)
  have hnC : (N : ℂ)+1 ≠ 0 := by exact_mod_cast (show (N : ℝ)+1 ≠ 0 by positivity)
  simp only [Finset.sum_const,Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ,
    Nat.cast_add,Nat.cast_one,smul_smul,inv_mul_cancel₀ hnC,one_smul] at ha
  convert ha using 1
  ext x
  simp only [iterateAverage,Pi.smul_apply,Finset.sum_apply]

lemma iterateAverage_coboundary (f : E → E) (N : ℕ) (x : E) :
    iterateAverage f N (f x)-iterateAverage f N x =
      (N+1 : ℂ)⁻¹ • (f^[N+1] x-x) := by
  simp only [iterateAverage,← smul_sub,← Finset.sum_sub_distrib]
  congr 1
  have he : ∀ j, f^[j] (f x) = f^[j+1] x := fun j => (Function.iterate_succ_apply f j x).symm
  simp only [he]
  exact Finset.sum_range_sub (fun j => f^[j] x) (N+1)

end Release061

end

end OAI
