import OAI.Analysis.Pureness.Comparison.SpectralIntegration
import OAI.Analysis.Pureness.Comparison.SpectralSplitting
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI
open scoped ENNReal
open MeasureTheory Filter Topology
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

noncomputable def supportCutoff (n : ℕ) (t : ℝ) : ℝ := min (((n : ℝ) + 1) * max t 0) 1

lemma supportCutoff_continuous (n : ℕ) : Continuous (supportCutoff n) := by
  unfold supportCutoff
  fun_prop

lemma supportCutoff_bounds (n : ℕ) (t : ℝ) :
    0 ≤ supportCutoff n t ∧ supportCutoff n t ≤ 1 := by
  unfold supportCutoff
  exact ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩

@[simp] lemma supportCutoff_zero (n : ℕ) : supportCutoff n 0 = 0 := by simp [supportCutoff]

lemma supportCutoff_le_indicator (n : ℕ) (t : ℝ) :
    supportCutoff n t ≤ if 0 < t then 1 else 0 := by
  by_cases ht : 0 < t
  · simpa only [ite_eq_left ht] using (supportCutoff_bounds n t).2
  · simp [supportCutoff, ht, max_eq_right (le_of_not_gt ht)]

lemma supportCutoff_tendsto (t : ℝ) :
    Tendsto (fun n => supportCutoff n t) atTop (𝓝 (if 0 < t then 1 else 0)) := by
  by_cases ht : 0 < t
  · rw [ite_eq_left ht]
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / t)
    have hNt : 1 < (N : ℝ) * t := (div_lt_iff₀ ht).mp hN
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hlarge : 1 ≤ ((n : ℝ) + 1) * t := by nlinarith
    simp [supportCutoff, max_eq_left ht.le, min_eq_right hlarge]
  · rw [ite_eq_right ht]
    have heq : (fun n => supportCutoff n t) = fun _ => 0 := by
      funext n
      simp [supportCutoff, max_eq_right (le_of_not_gt ht)]
    rw [heq]
    exact tendsto_const_nhds

noncomputable def supportApprox (a : A) (n : ℕ) : A := cfc (supportCutoff n) a

lemma supportApprox_nonneg (a : A) (n : ℕ) : 0 ≤ supportApprox a n := by
  apply cfc_nonneg
  intro t ht
  exact (supportCutoff_bounds n t).1

omit [PartialOrder A] [StarOrderedRing A] in
lemma supportApprox_norm_le_one (a : A) (n : ℕ) : ‖supportApprox a n‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro t ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg (supportCutoff_bounds n t).1]
    using (supportCutoff_bounds n t).2

lemma supportApprox_mem {a : A} (ha : 0 ≤ a) (n : ℕ) :
    supportApprox a n ∈ hereditaryCorner a ha :=
  cfc_mem_hereditaryCorner ha _ (supportCutoff_continuous n) (supportCutoff_zero n)

theorem TracialState.supportApprox_trace_tendsto (τ : TracialState A)
    {a : A} (ha : 0 ≤ a) :
    Tendsto (fun n => (τ.toPositiveLinearMap (supportApprox a n)).re) atTop
      (𝓝 (τ.spectralSupportMass a ha).toReal) := by
  let μ := τ.spectralMeasure a ha.isSelfAdjoint
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := supportCutoff) (f := fun t => if 0 < t then 1 else 0) (fun _ => 1)
    (fun n => (supportCutoff_continuous n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (supportCutoff_bounds n t).1]
        using (supportCutoff_bounds n t).2)
    (Eventually.of_forall supportCutoff_tendsto)
  rw [integral_strictCut] at h
  simp only [μ, τ.integral_spectralMeasure a ha.isSelfAdjoint _ (supportCutoff_continuous _)] at h
  exact h

theorem TracialState.supportApprox_trace_le (τ : TracialState A)
    {a : A} (ha : 0 ≤ a) (n : ℕ) :
    (τ.toPositiveLinearMap (supportApprox a n)).re ≤ (τ.spectralSupportMass a ha).toReal := by
  let μ := τ.spectralMeasure a ha.isSelfAdjoint
  have h := integral_mono_ae
    (τ.integrable_spectralMeasure a ha.isSelfAdjoint _ (supportCutoff_continuous n))
    (integrable_strictCut μ 0) (Eventually.of_forall (supportCutoff_le_indicator n))
  rw [integral_strictCut, τ.integral_spectralMeasure _ _ _ (supportCutoff_continuous n)] at h
  exact h
end CuntzComparison

end OAI
