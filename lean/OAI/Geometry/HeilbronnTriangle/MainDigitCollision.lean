import OAI.Geometry.HeilbronnTriangle.MainDigitLaw
import OAI.Geometry.HeilbronnTriangle.DigitBadTripleAverage

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT Problem355.heilbronnM

namespace Problem355.MainDigitLaw

open Parameters FiniteFieldLabels
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {r : ℕ} [Fact r.Prime] [Fintype (Label r)]

def tripleDivisor (D : PrimeParameterData heilbronnK r)
    (s : Fin 3 → Latent r) : ℝ :=
  (D.B : ℝ) ^ (smith D (DigitColumnLaw.tripleEquiv s).1
    (DigitColumnLaw.tripleEquiv s).2).b

def hasRepeatedLabel (s : Fin 3 → Latent r) : Prop :=
  (s 0).1 = (s 1).1 ∨ (s 0).1 = (s 2).1 ∨ (s 1).1 = (s 2).1

omit [Fintype (Label r)] in
lemma tripleDivisor_nonneg (D : PrimeParameterData heilbronnK r)
    (s : Fin 3 → Latent r) : 0 ≤ tripleDivisor D s := by
  unfold tripleDivisor
  positivity

theorem expectation_le_six_div_pow
    (D : PrimeParameterData heilbronnK r)
    (p : (Fin 3 → Latent r) → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ s, p s ≤ A * tripleDivisor D s)
    (hzero : ∀ s, ¬ hasRepeatedLabel s → p s = 0) :
    (∑ s : Fin 3 → Latent r,
      ConditionalSamples.productWeight (DigitColumnLaw.uniformWeight (Latent r)) s *
        p s) ≤ 6 * A / (r : ℝ) ^ 41 := by
  classical
  have h := DigitColumnLaw.bad_triple_expectation_le
    (fun labels f => (D.B : ℝ) ^ (smith D labels f).b) p A hA
    (conditional_moment D)
    (by intro labels f; exact hbound (DigitColumnLaw.tripleEquiv.symm (labels, f)))
    (by
      intro s h01 h02 h12
      apply hzero s
      simp only [hasRepeatedLabel, not_or]
      exact ⟨h01, h02, h12⟩)
  have hcard : Fintype.card (Label r) = r ^ 41 := by
    rw [← Nat.card_eq_fintype_card, card_label]
    rfl
  simpa only [hcard, Nat.cast_pow] using h

theorem collision_moment_le_six_div_pow
    (D : PrimeParameterData heilbronnK r) :
    (∑ s : Fin 3 → Latent r,
      ConditionalSamples.productWeight (DigitColumnLaw.uniformWeight (Latent r)) s *
        (if hasRepeatedLabel s then tripleDivisor D s else 0)) ≤
      6 / (r : ℝ) ^ 41 := by
  classical
  have h := expectation_le_six_div_pow D
    (fun s => if hasRepeatedLabel s then tripleDivisor D s else 0) 1
    (by norm_num)
    (by
      intro s
      split_ifs
      · simp only [one_mul, le_refl]
      · simpa only [one_mul] using tripleDivisor_nonneg D s)
    (by intro s hs; simp only [ite_eq_right hs])
  simpa only [mul_one] using h

end Problem355.MainDigitLaw

end

end OAI
