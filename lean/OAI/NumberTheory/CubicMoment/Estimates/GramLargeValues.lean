import OAI.NumberTheory.CubicMoment.Estimates.CubicMomentGram

namespace OAI

/-!
# Large values from the cubic Gram bound

Eliminating the row count from the square root preserves the saving in
the near-orthogonality argument. No large-value estimate is assumed.
-/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma gram_scalar_large_values {R L E A B : ℝ}
    (hR : 0 ≤ R) (hE : 0 ≤ E) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : R*L^2 ≤ E*(A + Real.sqrt (R*B))) :
    R*L^4 ≤ 2*E*A*L^2 + E^2*B := by
  have hs := Real.sq_sqrt (mul_nonneg hR hB)
  have hs0 := Real.sqrt_nonneg (R*B)
  by_cases hsmall : R*L^2 ≤ E*A
  · have hmul := mul_le_mul_of_nonneg_right hsmall (sq_nonneg L)
    have ha := mul_nonneg (mul_nonneg hE hA) (sq_nonneg L)
    nlinarith [mul_nonneg (sq_nonneg E) hB]
  · have hdiff : 0 ≤ R*L^2-E*A := by linarith
    have hupper : R*L^2-E*A ≤ E*Real.sqrt (R*B) := by nlinarith
    have hsquare := pow_le_pow_left₀ hdiff hupper 2
    have hraw : R*(R*L^4-2*E*A*L^2-E^2*B) ≤ 0 := by
      nlinarith [sq_nonneg (E*A)]
    rcases hR.eq_or_lt with hr | hr
    · have hz : R = 0 := hr.symm
      rw [hz, zero_mul]
      exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hE) hA)
        (sq_nonneg L)) (mul_nonneg (sq_nonneg E) hB)
    · exact le_of_not_gt (fun hbad => (not_lt_of_ge hraw)
        (mul_pos hr (by linarith)))

/-- All rows exceeding `L` force an explicit cardinality bound. This
is the finite large-value inequality needed before taking exponents. -/
theorem cubic_gram_large_value_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (Q N : Finset Eisenstein) (P Z L E : ℝ) (v : Eisenstein → ℂ),
      1 ≤ P → 1 ≤ Z → 0 < L → 0 ≤ E →
      (∀ p ∈ Q, gramDyad P p) →
      (∀ n ∈ N, primary n ∧ norm n ≤ Z) →
      (∑ n ∈ N, ‖v n‖^2) ≤ E →
      (∀ p ∈ Q, L ≤ ‖∑ n ∈ N, v n*cubicSymbol p n‖) →
      (Q.card : ℝ)*L^4 ≤ 2*E*(D*Z)*L^2 +
        E^2*(C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ))) := by
  obtain ⟨C,D,hC,hD,hgram⟩ := cubic_moment_gram_bound hε
  refine ⟨C,D,hC,hD,?_⟩
  intro Q N P Z L E v hP hZ hL hE hQ hN henergy hlarge
  have hlow : (Q.card : ℝ)*L^2 ≤ ∑ p ∈ Q, ‖∑ n ∈ N, v n*cubicSymbol p n‖^2 := by
    calc
      _ = ∑ _p ∈ Q, L^2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun p hp => pow_le_pow_left₀ hL.le (hlarge p hp) 2)
  apply gram_scalar_large_values (Nat.cast_nonneg _) hE (by positivity) (by positivity)
  have hmono := mul_le_mul_of_nonneg_left henergy
    (show 0 ≤ D*Z + Real.sqrt ((Q.card : ℝ)*
      (C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ)))) from by positivity)
  exact hlow.trans ((hgram Q N P Z v hP hZ hQ hN).trans
    (by simpa only [mul_comm E] using hmono))

end CubicFirstMoment

end

end OAI
