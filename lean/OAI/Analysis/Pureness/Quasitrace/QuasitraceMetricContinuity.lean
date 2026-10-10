import OAI.Analysis.Pureness.Quasitrace.QuasitraceDistance

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (T : CuntzPureness.PositiveQuasitrace D)

lemma metricSize_le_norm (x : D) : T.metricSize x ≤ ‖x‖^(2/3:ℝ)*T.metricSize 1 := by
  simpa only [mul_one] using T.metricSize_mul_le_left x 1

lemma metricSize_continuous : Continuous T.metricSize := by
  have hc : Continuous (fun x : D => (⟨star x*x,star_mul_self_nonneg x⟩ : Positive D)) := by
    fun_prop
  exact (Real.continuous_rpow_const (by positivity : 0 ≤ (3:ℝ)⁻¹)).comp (T.continuous.comp hc)

lemma distance_continuous : Continuous (fun p : D × D => T.distance p.1 p.2) :=
  T.metricSize_continuous.comp (continuous_fst.sub continuous_snd)

lemma exists_norm_delta (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x : D, ‖x‖ < δ → T.metricSize x < ε := by
  have hc := T.metricSize_continuous.continuousAt (x := 0)
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ,hδ,h⟩ := hc ε hε
  refine ⟨δ,hδ,fun x hx => ?_⟩
  have ht := h (by simpa only [dist_zero_right] using hx)
  simpa only [T.metricSize_zero,Real.dist_eq,sub_zero,abs_of_nonneg (T.metricSize_nonneg _)] using ht

lemma metricSize_smul_le (c : ℂ) (x : D) :
    T.metricSize (c • x) ≤ ‖c‖^(2/3:ℝ)*T.metricSize x := by
  rcases subsingleton_or_nontrivial D with hD | hD
  · let := hD
    rw [Subsingleton.elim x 0,smul_zero,T.metricSize_zero,mul_zero]
  let := hD
  rw [Algebra.smul_def]
  exact (T.metricSize_mul_le_left _ _).trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (norm_nonneg _) (by simp : ‖algebraMap ℂ D c‖ ≤ ‖c‖) (by norm_num))
    (T.metricSize_nonneg _))
lemma distance_smul_le (c : ℂ) (x y : D) :
    T.distance (c • x) (c • y) ≤ ‖c‖^(2/3:ℝ)*T.distance x y := by
  simpa only [distance,smul_sub] using T.metricSize_smul_le c (x-y)
end CuntzPureness.PositiveQuasitrace

end

end OAI
