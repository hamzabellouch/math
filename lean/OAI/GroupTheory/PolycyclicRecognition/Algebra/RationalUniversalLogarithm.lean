import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedWordSubalgebra

namespace OAI

/-! # The rational polynomial underlying the universal truncated logarithm -/

noncomputable section
namespace PolycyclicRecognition

variable (c n : ℕ)

def weightedWordHom : FreeMonoid (Fin n) →* TruncatedWords c n where
  toFun := weightedWord c n
  map_one' := weightedWord_one c n
  map_mul' := weightedWord_mul c n

def rationalWordWeight : RationalWords n →ₐ[ℚ] TruncatedWords c n :=
  MonoidAlgebra.lift ℚ _ _ (weightedWordHom c n)

theorem rationalWordWeight_single (w : FreeMonoid (Fin n)) (q : ℚ) :
    rationalWordWeight c n (MonoidAlgebra.single w q) = q • weightedWord c n w := by
  rw [rationalWordWeight, MonoidAlgebra.lift_single]
  rfl

theorem rationalWordWeight_letter (i : Fin n) :
    rationalWordWeight c n (rationalWordLetter i) =
      truncatedScalarParameter c • truncatedWordLetter c n i := by
  rw [rationalWordLetter, rationalWordWeight_single, one_smul]
  simp [weightedWord, FreeMonoid.length, truncatedWordLetter]

def rationalWordExponential (i : Fin n) : RationalWords n :=
  Polynomial.aeval (rationalWordLetter i) (PowerSeries.trunc (c + 1) (PowerSeries.exp ℚ))

def rationalExponentialProduct : RationalWords n :=
  (List.ofFn (rationalWordExponential c n)).prod

def rationalUniversalLogarithm : RationalWords n :=
  finiteNilpotentLog (c + 1) (rationalExponentialProduct c n - 1)

theorem rationalWordWeight_exponential (i : Fin n) :
    rationalWordWeight c n (rationalWordExponential c n i) =
      IsNilpotent.exp (truncatedScalarParameter c • truncatedWordLetter c n i) := by
  rw [rationalWordExponential, ← Polynomial.aeval_algHom_apply, rationalWordWeight_letter]
  exact nilpotentPowerSeriesEval_exp _ c (by rw [smul_pow, truncatedScalarParameter_pow, zero_smul])

theorem rationalWordWeight_exponentialProduct :
    rationalWordWeight c n (rationalExponentialProduct c n) = truncatedWordExponentialProduct c n := by
  simp only [rationalExponentialProduct, map_list_prod, List.map_ofFn, Function.comp_def,
    rationalWordWeight_exponential, truncatedWordExponentialProduct]

theorem rationalWordWeight_universalLogarithm :
    rationalWordWeight c n (rationalUniversalLogarithm c n) = truncatedWordLogarithm c n := by
  rw [rationalUniversalLogarithm, finiteNilpotentLog, ← Polynomial.aeval_algHom_apply,
    map_sub, rationalWordWeight_exponentialProduct, map_one]
  rfl

end PolycyclicRecognition

end

end OAI
