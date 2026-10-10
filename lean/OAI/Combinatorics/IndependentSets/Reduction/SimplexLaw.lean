import Mathlib
import OAI.Combinatorics.IndependentSets.Geometry.NoUniformlyBadFinitePatterns
import OAI.Combinatorics.IndependentSets.Repetition.FiniteGame

namespace OAI

namespace LargeIndependentSets
open MeasureTheory
open scoped BigOperators
open scoped Classical

noncomputable def simplexLaw {J : Type*} [Fintype J] [MeasurableSpace J]
    (q : J → ℝ) (hq : q ∈ finiteProbabilitySimplex J) : ProbabilityMeasure J := by
  let p : PMF J := PMF.ofFintype (fun j => ENNReal.ofReal (q j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hq.1 j), hq.2, ENNReal.ofReal_one])
  exact ⟨p.toMeasure, inferInstance⟩

lemma simplexLaw_apply_real {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (q : J → ℝ) (hq : q ∈ finiteProbabilitySimplex J)
    (E : Set J) :
    (simplexLaw q hq E : ℝ) = ∑ j, if j ∈ E then q j else 0 := by
  classical
  have hn : ∀ j, 0 ≤ if j ∈ E then q j else 0 := by
    intro j; split_ifs; exact hq.1 j; rfl
  have he : (simplexLaw q hq : Measure J) E =
      ENNReal.ofReal (∑ j, if j ∈ E then q j else 0) := by
    change (PMF.ofFintype (fun j => ENNReal.ofReal (q j)) _).toMeasure E = _
    rw [PMF.toMeasure_apply_fintype, ENNReal.ofReal_sum_of_nonneg (fun j _ => hn j)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Set.indicator_apply, PMF.ofFintype_apply]
    split_ifs <;> simp
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  change ENNReal.toReal ((simplexLaw q hq : Measure J) E) = _
  rw [he, ENNReal.toReal_ofReal (Finset.sum_nonneg (fun j _ => hn j))]

theorem real_pattern_alignment (s d : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ r ≥ s, ∃ p : (Fin s ↪o Fin r) → ℝ, p ∈ finiteProbabilitySimplex (Fin s ↪o Fin r) ∧
      ∀ C : ListPattern s d (Fin r),
        ∑ e, p e * (if ¬GoodPatternOn (C.restrict e) Finset.univ then 1 else 0) ≤ ξ := by
  classical
  by_contra h
  push Not at h
  apply no_uniformly_bad_finite_patterns hξ
  intro r hr
  have : Nonempty (Fin s ↪o Fin r) := ⟨Fin.castLEOrderEmb hr⟩
  obtain ⟨q, hq, hbad⟩ := finite_minimax_counterstatement
    (fun (e : Fin s ↪o Fin r) (C : ListPattern s d (Fin r)) =>
      if ¬GoodPatternOn (C.restrict e) Finset.univ then (1 : ℝ) else 0) ξ (h r hr)
  refine ⟨simplexLaw q hq, ?_⟩
  intro e
  rw [simplexLaw_apply_real]
  have hb := hbad e
  simp only [mul_ite, mul_one, mul_zero] at hb
  refine hb.le.trans (Finset.sum_le_sum fun pattern _ => ?_)
  by_cases hgood : GoodPatternOn (pattern.restrict e) Finset.univ <;> simp [hgood]

end LargeIndependentSets

end OAI
