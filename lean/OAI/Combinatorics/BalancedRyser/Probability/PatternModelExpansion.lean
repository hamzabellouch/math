import OAI.Combinatorics.BalancedRyser.Probability.PatternModelCancellation

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModelMoments

variable (P : PatternModel)

lemma centered_product_integrable (K : Finset P.Color) (x : P.Sample)
    (n : ℕ) (a : Fin n → P.Label) :
    Integrable (fun ω => ∏ j, (P.indicator (a j) (P.fixCoordinates K x ω) -
      P.fixedExpectation K x (P.indicator (a j)))) P.measure := by
  let : IsProbabilityMeasure P.measure := by
    unfold PatternModel.measure
    infer_instance
  have hm (j : Fin n) : Measurable (fun ω =>
      P.indicator (a j) (P.fixCoordinates K x ω) -
        P.fixedExpectation K x (P.indicator (a j))) :=
    ((PatternProof.measurable_indicator P (a j)).comp
      (PatternProof.measurable_fixedCoordinates P K x)).sub_const _
  apply Integrable.of_bound
    (Finset.measurable_fun_prod _ (fun j _ => hm j)).aestronglyMeasurable 1
  filter_upwards with ω
  rw [Real.norm_eq_abs, Finset.abs_prod]
  apply Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
  intro j _
  have hi := PatternProof.indicator_mem_Icc P (a j) (P.fixCoordinates K x ω)
  have hmean := PatternProof.fixedExpectation_indicator_mem_Icc P K x (a j)
  exact abs_le.mpr ⟨by linarith [hi.1, hi.2, hmean.1, hmean.2],
    by linarith [hi.1, hi.2, hmean.1, hmean.2]⟩

lemma fixedExpectation_count_eq_sum (K : Finset P.Color) (x : P.Sample) :
    P.fixedExpectation K x P.count =
      ∑ a, P.fixedExpectation K x (P.indicator a) := by
  let : IsProbabilityMeasure P.measure := by
    unfold PatternModel.measure
    infer_instance
  unfold PatternModel.fixedExpectation PatternModel.count
  exact integral_finsetSum _ (fun a _ =>
    Integrable.of_mem_Icc 0 1
      (((PatternProof.measurable_indicator P a).comp
        (PatternProof.measurable_fixedCoordinates P K x)).aemeasurable)
      (Filter.Eventually.of_forall (fun ω =>
        PatternProof.indicator_mem_Icc P a (P.fixCoordinates K x ω))))

theorem centered_moment_expansion (K : Finset P.Color) (x : P.Sample) (s : ℕ) :
    P.fixedExpectation K x
      (fun ω => |P.count ω - P.fixedExpectation K x P.count| ^ (2 * s)) =
      ∑ a : Fin (2 * s) → P.Label, P.fixedExpectation K x
        (fun ω => ∏ j, (P.indicator (a j) ω -
          P.fixedExpectation K x (P.indicator (a j)))) := by
  classical
  have hcenter (ω : P.Sample) :
      P.count ω - P.fixedExpectation K x P.count =
        ∑ a, (P.indicator a ω - P.fixedExpectation K x (P.indicator a)) := by
    rw [fixedExpectation_count_eq_sum, Finset.sum_sub_distrib]
    rfl
  have habs (z : ℝ) : |z| ^ (2 * s) = z ^ (2 * s) := by
    rw [pow_mul, pow_mul, sq_abs]
  simp_rw [habs, hcenter, Fintype.sum_pow]
  unfold PatternModel.fixedExpectation
  exact integral_finsetSum _ (fun a _ => centered_product_integrable P K x (2 * s) a)

attribute [local instance] Classical.propDecidable

def noIsolated (K : Finset P.Color) {n : ℕ} (a : Fin n → P.Label) : Prop :=
  ∀ i, ∃ j, j ≠ i ∧
    ((P.support (a j) \ K) ∩ (P.support (a i) \ K)).Nonempty

theorem centered_moment_le_noIsolated (K : Finset P.Color) (x : P.Sample) (s : ℕ) :
    P.fixedExpectation K x
      (fun ω => |P.count ω - P.fixedExpectation K x P.count| ^ (2 * s)) ≤
      ∑ a : Fin (2 * s) → P.Label,
        if noIsolated P K a then
          P.fixedExpectation K x (fun ω => ∏ j,
            (P.indicator (a j) ω + P.fixedExpectation K x (P.indicator (a j))))
        else 0 := by
  classical
  rw [centered_moment_expansion]
  apply Finset.sum_le_sum
  intro a _
  by_cases hno : noIsolated P K a
  · rw [ite_eq_left hno]
    exact (le_abs_self _).trans
      (PatternProof.abs_fixedExpectation_centered_prod_le P K x (2 * s) a)
  · rw [ite_eq_right hno]
    have hiso : ∃ i, ∀ j, j ≠ i →
        ¬ ((P.support (a j) \ K) ∩ (P.support (a i) \ K)).Nonempty := by
      simpa only [noIsolated, not_forall, not_exists, not_and] using hno
    obtain ⟨i, hi⟩ := hiso
    have hdisj (j : Fin (2 * s)) (hij : i ≠ j) :
        Disjoint (P.support (a i) \ K) (P.support (a j) \ K) := by
      apply Finset.disjoint_left.mpr
      intro c hci hcj
      exact hi j hij.symm ⟨c, Finset.mem_inter.mpr ⟨hcj, hci⟩⟩
    rw [PatternProof.fixedExpectation_centered_prod_eq_zero P K x (2 * s) a i hdisj]

end Balanced.PatternModelMoments

end OAI
