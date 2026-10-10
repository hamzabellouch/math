import OAI.Analysis.LpDimension.LogLimits

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace
universe u

namespace SubpolynomialLp

/-- The universal coordinate dimension bounds and their logarithmic limits. -/
theorem source_main (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2) :
    (∀ D : ℝ, 1 < D → ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      GoodDimension.{u} p n D (dimension.{u} p n D) ∧
      Real.log (n : ℝ) / Real.log (1 + 2 * D) ≤ (dimension.{u} p n D : ℝ) ∧
      (dimension.{u} p n D : ℝ) ≤ Real.exp (C * Real.log (n : ℝ) ^ gamma p)) ∧
    (∀ n : ℕ, 9 ≤ n →
      GoodDimension.{u} p n 1 (dimension.{u} p n 1) ∧
      ((n - 1) / 4) ^ 2 ≤ dimension.{u} p n 1 ∧
      dimension.{u} p n 1 ≤ n.choose 2) ∧
    (∀ D : ℝ, 1 ≤ D →
      Tendsto (fun n : ℕ => Real.log (dimension.{u} p n D : ℝ) / Real.log (n : ℝ))
        atTop (𝓝 (if 1 < D then 0 else 2))) := by
  have hupper : ∀ D : ℝ, 1 < D → ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      (dimension.{u} p n D : ℝ) ≤ Real.exp (C * Real.log (n : ℝ) ^ gamma p) := by
    intro D hD
    rcases lt_or_gt_of_ne hp2 with hlt|hgt
    · simpa only [gamma,ite_eq_left hlt] using below_main_upper.{u} p D hp hlt hD
    · simpa only [gamma,ite_eq_right (not_lt.mpr hgt.le)] using above_main_upper.{u} p D hgt hD
  refine ⟨?_,fun n hn => exact_dimension_bounds p hp hp2 n hn,?_⟩
  · intro D hD
    obtain ⟨C,hC⟩ := hupper D hD
    exact ⟨C,fun n hn => ⟨dimension_good p hp n hn D hD.le,
      dimension_packing_lower p hp n hn D hD.le,hC n hn⟩⟩
  · intro D hD
    by_cases hD1 : 1 < D
    · rw [ite_eq_left hD1]
      obtain ⟨C,hC⟩ := hupper D hD1
      have hγ : gamma p < 1 := by
        unfold gamma
        split_ifs
        · linarith
        · have hh : 0 < 2/p := by positivity
          linarith
      apply subpower_log_limit (fun n => dimension.{u} p n D) C (gamma p) hγ
      · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
        have hl := dimension_packing_lower.{u} p hp n hn D hD
        have hn1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
        have hdpos : (0:ℝ) < dimension.{u} p n D :=
          lt_of_lt_of_le (div_pos (Real.log_pos hn1) (Real.log_pos (by linarith))) hl
        exact_mod_cast hdpos
      · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
        exact hC n hn
    · have hDeq : D=1 := by linarith
      subst D
      simpa only [lt_self_iff_false,ite_false] using exact_dimension_log_limit.{u} p hp hp2

end SubpolynomialLp

end

end OAI
