import OAI.Analysis.Pureness.Comparison.MatrixRankApproximation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace OAI
open MeasureTheory Filter Topology
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma positive_root_tendsto {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => t ^ (1 / ((n : ℝ) + 1))) atTop
      (𝓝 (if 0 < t then 1 else 0)) := by
  by_cases ht0 : t = 0
  · simp only [ht0, lt_self_iff_false, ite_false]
    have hz : (fun n : ℕ => (0 : ℝ) ^ (1 / ((n : ℝ) + 1))) = fun _ => 0 := by
      funext n
      exact Real.zero_rpow (by positivity)
    rw [hz]
    exact tendsto_const_nhds
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    rw [ite_eq_left htpos]
    have h := (Real.continuousAt_const_rpow ht0).tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [Function.comp_def, Real.rpow_zero] using h

lemma positive_root_bound {t R : ℝ} (ht : 0 ≤ t) (hR : t ≤ R) (n : ℕ) :
    ‖t ^ (1 / ((n : ℝ) + 1))‖ ≤ max R 1 := by
  have hp : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  have hp1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht _)]
  by_cases ht1 : t ≤ 1
  · exact (Real.rpow_le_one ht ht1 hp).trans (le_max_right _ _)
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge ht1) hp1
    rw [Real.rpow_one] at h
    exact h.trans (hR.trans (le_max_left _ _))

theorem TracialState.root_trace_tendsto (τ : TracialState A) {a : A} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (τ.toPositiveLinearMap (CFC.rpow a (1 / ((n : ℝ) + 1)))).re)
      atTop (𝓝 (τ.spectralSupportMass a ha).toReal) := by
  have h01 : (0 : A) ≠ 1 := by
    intro h
    have hz : (0 : ℂ) = 1 := by simpa [τ.normalized] using congrArg τ.toPositiveLinearMap h
    exact zero_ne_one hz
  let : Nontrivial A := ⟨⟨0, 1, h01⟩⟩
  let μ := τ.spectralMeasure a ha.isSelfAdjoint
  have hf (n : ℕ) : Continuous (fun t : ℝ => t ^ (1 / ((n : ℝ) + 1))) :=
    Real.continuous_rpow_const (by positivity)
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n t => t ^ (1 / ((n : ℝ) + 1)))
    (f := fun t => if 0 < t then 1 else 0) (fun _ => max ‖a‖ 1)
    (fun n => (hf n).aestronglyMeasurable) (integrable_const _)
    (fun n => ?_) ?_
  · rw [integral_strictCut] at h
    simp only [μ, τ.integral_spectralMeasure a ha.isSelfAdjoint _ (hf _)] at h
    simpa only [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real ha, TracialState.spectralSupportMass] using h
  · filter_upwards [τ.ae_mem_spectrum a ha.isSelfAdjoint] with t ht
    exact positive_root_bound (spectrum_nonneg_of_nonneg ha ht)
      ((Real.le_norm_self t).trans (spectrum.norm_le_norm_of_mem ht)) n
  · filter_upwards [τ.ae_mem_spectrum a ha.isSelfAdjoint] with t ht
    exact positive_root_tendsto (spectrum_nonneg_of_nonneg ha ht)

theorem TracialState.matrix_root_trace_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (τ : TracialState A) {M : CStarMatrix ι ι A} (hM : 0 ≤ M) :
    Tendsto (fun n : ℕ => (τ.matrixTraceLinear (CFC.rpow M (1 / ((n : ℝ) + 1)))).re)
      atTop (𝓝 (τ.matrixSupportMass M hM).toReal) := by
  have h := (τ.normalizedMatrixTrace.root_trace_tendsto hM).const_mul (Fintype.card ι : ℝ)
  simp only [τ.normalizedMatrixTrace_scale] at h
  simp only [TracialState.matrixSupportMass, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  convert h using 1; rfl

theorem exists_thin_full_root_rank_element [IsSimpleCStarAlgebra A]
    (hinfinite : ¬ FiniteDimensional ℂ A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ e : A, 0 ≤ e ∧ e ≠ 0 ∧ ‖e‖ = 1 ∧
      closure (finiteSandwichIdeal e : Set A) = Set.univ ∧
      ∀ τ : TracialState A, ∃ r : ℝ,
        Tendsto (fun n : ℕ => (τ.toPositiveLinearMap
          (CFC.rpow e (1 / ((n : ℝ) + 1)))).re) atTop (𝓝 r) ∧ r < δ := by
  obtain ⟨e, he, hen, henorm, hefull, hsmall⟩ :=
    exists_thin_full_spectral_element hinfinite hδ
  exact ⟨e, he, hen, henorm, hefull, fun τ =>
    ⟨(τ.spectralSupportMass e he).toReal, τ.root_trace_tendsto he, hsmall τ⟩⟩

theorem exists_matrix_root_rank_approximation [IsSimpleCStarAlgebra A]
    (hinfinite : ¬ FiniteDimensional ℂ A) {b : A} (hb : 0 ≤ b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, ∃ M : CStarMatrix (Fin (k + 1)) (Fin (k + 1)) A, 0 ≤ M ∧
      ∀ τ : TracialState A, ∃ r : ℝ,
        Tendsto (fun n : ℕ => (τ.matrixTraceLinear (CFC.rpow M (1 / ((n : ℝ) + 1)))).re)
          atTop (𝓝 r) ∧ (τ.toPositiveLinearMap b).re - δ < r ∧ r ≤ (τ.toPositiveLinearMap b).re := by
  obtain ⟨k, M, hM, hbound⟩ := exists_matrix_rank_approximation hinfinite hb hδ
  exact ⟨k, M, hM, fun τ => ⟨(τ.matrixSupportMass M hM).toReal,
    τ.matrix_root_trace_tendsto hM, hbound τ⟩⟩
end CuntzComparison

end OAI
