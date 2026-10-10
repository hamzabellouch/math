import OAI.NumberTheory.TwoPoint.Bounds.MatrixAction

namespace OAI

/-! Four bounded quadratic tests recover an arbitrary complex bilinear test. -/

namespace TwoPointCorrelations

open scoped ComplexConjugate

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def halfPair (u v : E) (z : ℂ) : E := (2 : ℂ)⁻¹ • (u + z • v)

theorem complex_polarization_four (T : E →L[ℂ] E) (u v : E) :
    inner ℂ u (T v) =
      inner ℂ (halfPair u v 1) (T (halfPair u v 1)) -
      inner ℂ (halfPair u v (-1)) (T (halfPair u v (-1))) -
      Complex.I * inner ℂ (halfPair u v Complex.I) (T (halfPair u v Complex.I)) +
      Complex.I * inner ℂ (halfPair u v (-Complex.I)) (T (halfPair u v (-Complex.I))) := by
  simp only [halfPair, map_smul, map_add, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
    map_inv₀, map_ofNat, map_neg, Complex.conj_I, one_smul, neg_smul]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem complex_polarization_norm (T : E →L[ℂ] E) (u v : E) :
    ‖inner ℂ u (T v)‖ ≤
      ‖inner ℂ (halfPair u v 1) (T (halfPair u v 1))‖ +
      ‖inner ℂ (halfPair u v (-1)) (T (halfPair u v (-1)))‖ +
      ‖inner ℂ (halfPair u v Complex.I) (T (halfPair u v Complex.I))‖ +
      ‖inner ℂ (halfPair u v (-Complex.I)) (T (halfPair u v (-Complex.I)))‖ := by
  rw [complex_polarization_four]
  calc
    _ ≤ ‖inner ℂ (halfPair u v 1) (T (halfPair u v 1)) -
        inner ℂ (halfPair u v (-1)) (T (halfPair u v (-1))) -
        Complex.I * inner ℂ (halfPair u v Complex.I) (T (halfPair u v Complex.I))‖ +
        ‖Complex.I * inner ℂ (halfPair u v (-Complex.I)) (T (halfPair u v (-Complex.I)))‖ :=
      norm_add_le _ _
    _ ≤ (‖inner ℂ (halfPair u v 1) (T (halfPair u v 1)) -
        inner ℂ (halfPair u v (-1)) (T (halfPair u v (-1)))‖ +
        ‖Complex.I * inner ℂ (halfPair u v Complex.I) (T (halfPair u v Complex.I))‖) +
        ‖Complex.I * inner ℂ (halfPair u v (-Complex.I)) (T (halfPair u v (-Complex.I)))‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ _ := by
      simp only [norm_mul, Complex.norm_I, one_mul]
      linarith [norm_sub_le
        (inner ℂ (halfPair u v 1) (T (halfPair u v 1)))
        (inner ℂ (halfPair u v (-1)) (T (halfPair u v (-1))))]

end Hilbert

noncomputable def halfPairFunction {α : Type*} (f g : α → ℂ) (z : ℂ) : α → ℂ :=
  fun x => (f x + z * g x) / 2

lemma halfPairFunction_norm_le {α : Type*} (f g : α → ℂ) (z : ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1) (hz : ‖z‖ ≤ 1) (x : α) :
    ‖halfPairFunction f g z x‖ ≤ 1 := by
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [halfPairFunction, norm_div, htwo]
  apply (div_le_one (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    ‖f x + z * g x‖ ≤ ‖f x‖ + ‖z * g x‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add (hf x) (by rw [norm_mul]; exact
      (mul_le_mul hz (hg x) (norm_nonneg _) zero_le_one).trans_eq (by ring))
    _ = 2 := by norm_num

end TwoPointCorrelations

end OAI
