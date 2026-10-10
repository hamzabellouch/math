import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedWordSubstitution

namespace OAI

/-! # Exponential and logarithm identities under nilpotent substitution -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A] {c n : ℕ} (X : Fin n → A)
  (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0)

include hX

omit [Algebra ℚ A] in
theorem nilpotent_word_letter_pow (i : Fin n) : X i ^ (c + 1) = 0 := by
  have hlen (k : ℕ) : (FreeMonoid.of i ^ k).length = k := by
    induction k with
    | zero => simp
    | succ k hk => simp only [pow_succ, FreeMonoid.length_mul, FreeMonoid.length_of, hk]
  have h := hX (FreeMonoid.of i ^ (c + 1)) (by rw [hlen]; omega)
  simpa using h

theorem weightedWordSubstitution_pow {a : TruncatedWords c n}
    (ha : a ∈ weightedWordSubalgebra c n) (k : ℕ) :
    weightedWordSubstitution X (a ^ k) = weightedWordSubstitution X a ^ k := by
  induction k with
  | zero => simpa only [pow_zero] using weightedWordSubstitution_one X hX
  | succ k hk =>
    rw [pow_succ a k, weightedWordSubstitution_mul X hX
      ((weightedWordSubalgebra c n).pow_mem ha k) ha, hk,
      pow_succ (weightedWordSubstitution X a) k]

theorem weightedWordSubstitution_aeval {a : TruncatedWords c n}
    (ha : a ∈ weightedWordSubalgebra c n) (p : Polynomial ℚ) :
    weightedWordSubstitution X (Polynomial.aeval a p) =
      Polynomial.aeval (weightedWordSubstitution X a) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial k q =>
    simp only [Polynomial.aeval_monomial, ← Algebra.smul_def, map_smul,
      weightedWordSubstitution_pow X hX ha]

theorem weightedWordSubstitution_parameter_letter (i : Fin n) :
    weightedWordSubstitution X (truncatedScalarParameter c • truncatedWordLetter c n i) = X i := by
  have h : truncatedScalarParameter c • truncatedWordLetter c n i =
      weightedWord c n (FreeMonoid.of i) := by
    simp [truncatedWordLetter, weightedWord, FreeMonoid.length]
  rw [h, weightedWordSubstitution_weightedWord X hX]
  simp

theorem weightedWordSubstitution_exp_letter (i : Fin n) :
    weightedWordSubstitution X
      (IsNilpotent.exp (truncatedScalarParameter c • truncatedWordLetter c n i)) =
        IsNilpotent.exp (X i) := by
  have hn : (truncatedScalarParameter c • truncatedWordLetter c n i) ^ (c + 1) = 0 := by
    rw [smul_pow, truncatedScalarParameter_pow, zero_smul]
  rw [← nilpotentPowerSeriesEval_exp _ c hn]
  change weightedWordSubstitution X (Polynomial.aeval _ _) = _
  rw [weightedWordSubstitution_aeval X hX (weightedWordSubalgebra_parameter_letter c n i),
    weightedWordSubstitution_parameter_letter X hX]
  exact nilpotentPowerSeriesEval_exp _ c (nilpotent_word_letter_pow X hX i)

theorem weightedWordSubstitution_list_prod (L : List (TruncatedWords c n))
    (hL : ∀ a ∈ L, a ∈ weightedWordSubalgebra c n) :
    weightedWordSubstitution X L.prod = (L.map (weightedWordSubstitution X)).prod := by
  induction L with
  | nil => exact weightedWordSubstitution_one X hX
  | cons a L ih =>
    have ht : ∀ b ∈ L, b ∈ weightedWordSubalgebra c n :=
      fun b hb => hL b (List.mem_cons_of_mem a hb)
    rw [List.prod_cons, List.map_cons, List.prod_cons,
      weightedWordSubstitution_mul X hX (hL a (List.mem_cons_self ..))
        ((weightedWordSubalgebra c n).toSubmonoid.list_prod_mem ht), ih ht]

theorem weightedWordSubstitution_exponentialProduct :
    weightedWordSubstitution X (truncatedWordExponentialProduct c n) =
      (List.ofFn (fun i => IsNilpotent.exp (X i))).prod := by
  rw [truncatedWordExponentialProduct, weightedWordSubstitution_list_prod X hX]
  · simp only [List.map_ofFn, Function.comp_def, weightedWordSubstitution_exp_letter X hX]
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact weightedWordSubalgebra_exp_parameter_letter c n i

end PolycyclicRecognition

end

end OAI
