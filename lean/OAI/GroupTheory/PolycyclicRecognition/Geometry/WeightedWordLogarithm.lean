import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedWordSubalgebra

namespace OAI

/-! # The universal logarithm preserves the scalar/word grading -/

noncomputable section
namespace PolycyclicRecognition

variable (c n : ℕ)

theorem weightedWordSubalgebra_aeval {a : TruncatedWords c n}
    (ha : a ∈ weightedWordSubalgebra c n) (p : Polynomial ℚ) :
    Polynomial.aeval a p ∈ weightedWordSubalgebra c n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact (weightedWordSubalgebra c n).add_mem hp hq
  | monomial k q =>
    rw [Polynomial.aeval_monomial]
    exact (weightedWordSubalgebra c n).mul_mem
      ((weightedWordSubalgebra c n).algebraMap_mem q)
      ((weightedWordSubalgebra c n).pow_mem ha k)

theorem weightedWordSubalgebra_exp_parameter_letter (i : Fin n) :
    IsNilpotent.exp (truncatedScalarParameter c • truncatedWordLetter c n i) ∈
      weightedWordSubalgebra c n := by
  have hn : (truncatedScalarParameter c • truncatedWordLetter c n i) ^ (c + 1) = 0 := by
    rw [smul_pow, truncatedScalarParameter_pow, zero_smul]
  rw [← nilpotentPowerSeriesEval_exp _ c hn]
  exact weightedWordSubalgebra_aeval c n (weightedWordSubalgebra_parameter_letter c n i) _

theorem weightedWordSubalgebra_exponentialProduct :
    truncatedWordExponentialProduct c n ∈ weightedWordSubalgebra c n := by
  apply (weightedWordSubalgebra c n).toSubmonoid.list_prod_mem
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact weightedWordSubalgebra_exp_parameter_letter c n i

theorem weightedWordLogarithm_mem :
    truncatedWordLogarithm c n ∈ weightedWordSpan c n := by
  exact weightedWordSubalgebra_aeval c n
    ((weightedWordSubalgebra c n).sub_mem (weightedWordSubalgebra_exponentialProduct c n)
      (weightedWordSubalgebra c n).one_mem) _

end PolycyclicRecognition

end

end OAI
