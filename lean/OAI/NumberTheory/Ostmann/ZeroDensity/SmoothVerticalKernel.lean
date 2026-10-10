import Mathlib.MeasureTheory.Integral.DominatedConvergence
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothMellinInversion
import OAI.NumberTheory.Ostmann.Characters.CharacterRightHalfPlane

namespace OAI

/-! # The absolutely convergent vertical kernel before contour shifting -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators

noncomputable def primeMellinLine (t : ℝ) : ℂ := 2 + (t : ℂ) * Complex.I

@[simp] theorem primeMellinLine_re (t : ℝ) : (primeMellinLine t).re = 2 := by
  simp [primeMellinLine]

@[fun_prop] theorem primeMellinLine_continuous : Continuous primeMellinLine := by
  unfold primeMellinLine
  fun_prop

noncomputable def primeVerticalWeight (X t : ℝ) : ℂ :=
  (X : ℂ) ^ primeMellinLine t * primeMeanMellin (primeMellinLine t)

theorem primeVerticalWeight_continuous (X : ℝ) (hX : 0 < X) :
    Continuous (primeVerticalWeight X) := by
  apply Continuous.mul
  · exact (show Continuous primeMellinLine by fun_prop).const_cpow
      (.inl (by exact_mod_cast hX.ne'))
  · exact primeMeanMellin_differentiable.continuous.comp (by fun_prop)

theorem primeVerticalWeight_norm (X t : ℝ) (hX : 0 < X) :
    ‖primeVerticalWeight X t‖ = X ^ 2 * ‖primeMeanMellin (primeMellinLine t)‖ := by
  rw [primeVerticalWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp only [primeMellinLine_re, Real.rpow_two]

theorem primeVerticalWeight_integrable (X : ℝ) (hX : 0 < X) :
    Integrable (primeVerticalWeight X) := by
  have hm : Integrable (fun t => primeMeanMellin (primeMellinLine t)) :=
    primeMeanMellin_verticalIntegrable
  apply (hm.norm.const_mul (X ^ 2)).mono'
    (primeVerticalWeight_continuous X hX).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => (primeVerticalWeight_norm X t hX).le)

noncomputable def characterMangoldtCoefficient (χ : PrimitiveComplexCharacter) (n : ℕ) : ℂ :=
  χ.character (n : ZMod χ.modulus) * (ArithmeticFunction.vonMangoldt n : ℂ)

theorem characterMangoldtCoefficient_summable (χ : PrimitiveComplexCharacter) :
    LSeriesSummable (characterMangoldtCoefficient χ) 2 :=
  DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.character (by norm_num)

theorem characterMangoldt_term_norm (χ : PrimitiveComplexCharacter) (n : ℕ) (t : ℝ) :
    ‖LSeries.term (characterMangoldtCoefficient χ) (primeMellinLine t) n‖ =
      ‖LSeries.term (characterMangoldtCoefficient χ) 2 n‖ := by
  simp [LSeries.norm_term_eq, primeMellinLine_re]

theorem characterMangoldt_term_continuous (χ : PrimitiveComplexCharacter) (n : ℕ) :
    Continuous (fun t => LSeries.term (characterMangoldtCoefficient χ) (primeMellinLine t) n) := by
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero]
    exact continuous_const
  · simp only [LSeries.term_of_ne_zero hn]
    exact continuous_const.div ((show Continuous primeMellinLine by fun_prop).const_cpow
      (.inl (by exact_mod_cast hn))) (fun _ => Complex.cpow_ne_zero_iff.mpr
        (.inl (by exact_mod_cast hn)))

/-- Termwise inversion, including the zero coefficient at n=0. -/
theorem characterMangoldt_term_inversion (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (n : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, LSeries.term (characterMangoldtCoefficient χ) (primeMellinLine t) n *
        primeVerticalWeight X t) =
      characterMangoldtCoefficient χ n * (primeMeanTest (n / X) : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp [characterMangoldtCoefficient]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hkernel (t : ℝ) :
      LSeries.term (characterMangoldtCoefficient χ) (primeMellinLine t) n *
        primeVerticalWeight X t = characterMangoldtCoefficient χ n *
          (((n : ℝ) / X : ℝ) : ℂ) ^ (-primeMellinLine t) * primeMeanMellin (primeMellinLine t) := by
    rw [LSeries.term_of_ne_zero hn, primeVerticalWeight, Complex.cpow_neg,
      Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hnR.le hX.le, inv_div]
    push_cast
    ring
  simp_rw [hkernel, mul_assoc]
  rw [integral_const_mul]
  have hinv := primeMeanTest_mellin_inversion ((n : ℝ) / X) (div_pos hnR hX)
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ,
    (((n : ℝ) / X : ℝ) : ℂ) ^ (-primeMellinLine t) * primeMeanMellin (primeMellinLine t)) = _ at hinv
  rw [← hinv]
  ring

end Ostmann

end OAI
