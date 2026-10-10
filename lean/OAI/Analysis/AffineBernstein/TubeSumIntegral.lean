import Mathlib
import OAI.Analysis.AffineBernstein.TubeCompactIntegral

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S]
  [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]

lemma tubeIntegral_sum {J : Type*} (t : Finset J) {M : S × E → ℝ} {f : J → S × E → ℝ}
    {σ : S → ℝ} {D : Set S} (hσ : Continuous σ) (hc : HasCompactSupport σ)
    (hsD : tsupport σ ⊆ D) (hM : ContinuousOn M (tubeOpenSet D))
    (hf : ∀ j ∈ t, ContinuousOn (f j) (tubeOpenSet D)) :
    tubeIntegral μ M σ (fun q => ∑ j ∈ t, f j q) = ∑ j ∈ t, tubeIntegral μ M σ (f j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [tubeIntegral]
  | @insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    rw [tubeIntegral_add hσ hc hsD hM (hf a (Finset.mem_insert_self _ _))
      (continuousOn_finsetSum _ fun j hj => hf j (Finset.mem_insert_of_mem hj))]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma tubeIntegral_mono_sq {M f g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσ : Continuous σ) (hc : HasCompactSupport σ) (hsD : tsupport σ ⊆ D)
    (hM : ContinuousOn M (tubeOpenSet D)) (hf : ContinuousOn f (tubeOpenSet D))
    (hg : ContinuousOn g (tubeOpenSet D))
    (hpos : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ M (s,e))
    (hfg : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → f (s,e) ≤ g (s,e)) :
    tubeIntegral μ M (fun s => σ s^2) f ≤ tubeIntegral μ M (fun s => σ s^2) g := by
  apply integral_mono_ae (integrable_tube_compact_sq hσ hc hsD hM hf)
    (integrable_tube_compact_sq hσ hc hsD hM hg)
  apply Filter.Eventually.of_forall
  intro q
  by_cases hs : q.1 ∈ tsupport σ
  · exact mul_le_mul_of_nonneg_left (hfg q.1 (hsD hs) q.2 (mem_sphere_zero_iff_norm.1 q.2.property))
      (mul_nonneg (hpos q.1 (hsD hs) q.2 (mem_sphere_zero_iff_norm.1 q.2.property)) (sq_nonneg _))
  · simp [image_eq_zero_of_notMem_tsupport hs]

end AffineBernstein
end

end OAI
