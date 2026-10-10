import OAI.Algebra.DepthFive.FourPathLocal
import OAI.Algebra.DepthFive.ShiftedOccupation

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace LocalMoments

def operatorSign (derivative : Bool) : ℤ := if derivative then -1 else 1

/-- An invalid shifted coordinate forces the relevant local table factor to vanish. -/
lemma localPolynomial_zero_of_negative {σ : Type*} [DecidableEq σ]
    (derivative : Bool) (M : σ → ℕ) (p q r x : σ)
    (hneg : (M x : ℤ) + operatorSign derivative *
      ((if x = p then 1 else 0) - (if x = q then 1 else 0)) < 0) :
    localPolynomial derivative M p q r = 0 := by
  by_cases hpq : p = q
  · subst q
    simp at hneg
    omega
  · cases derivative
    · have hMq : M q = 0 := by
        by_cases hxq : x = q
        · subst x
          simp [operatorSign, Ne.symm hpq] at hneg
          omega
        · by_cases hxp : x = p
          · subst x
            simp [operatorSign, hpq] at hneg
            omega
          · simp [operatorSign, hxp, hxq] at hneg
            omega
      simp [localPolynomial, hpq, hMq]
    · have hMp : M p = 0 := by
        by_cases hxp : x = p
        · subst x
          simp [operatorSign, hpq] at hneg
          omega
        · by_cases hxq : x = q
          · subst x
            simp [operatorSign, Ne.symm hpq] at hneg
            omega
          · simp [operatorSign, hxp, hxq] at hneg
            omega
      simp [localPolynomial, hpq, hMp]

/-- An invalid source in any layer annihilates the complete four-path table product. -/
lemma localPolynomial_product_zero_of_negative {ι σ : Type*}
    [DecidableEq σ] (layers : Finset ι) (derivative : ι → Bool)
    (M : ι × σ → ℕ) (p q r : ι → σ) (t : ι) (a : σ)
    (ht : t ∈ layers)
    (hneg : ShiftedOccupation.signedSource M (operatorSign ∘ derivative) p q (t, a) < 0) :
    (∏ j ∈ layers, localPolynomial (derivative j) (fun b => M (j, b)) (p j) (q j) (r j)) = 0 := by
  apply Finset.prod_eq_zero ht
  apply localPolynomial_zero_of_negative (derivative t) (fun b => M (t, b))
    (p t) (q t) (r t) a
  exact hneg

/-- The global table vanishes whenever no natural shifted source exists. -/
lemma localPolynomial_product_zero_of_no_source {ι σ : Type*}
    [Fintype ι] [DecidableEq σ] (derivative : ι → Bool)
    (M : ι × σ → ℕ) (p q r : ι → σ)
    (hbad : ¬ ∃ N : ι × σ → ℕ, ∀ x, (N x : ℤ) =
      ShiftedOccupation.signedSource M (operatorSign ∘ derivative) p q x) :
    (∏ j : ι, localPolynomial (derivative j) (fun b => M (j, b)) (p j) (q j) (r j)) = 0 := by
  rw [ShiftedOccupation.exists_source_iff] at hbad
  push Not at hbad
  obtain ⟨⟨t, a⟩, hneg⟩ := hbad
  exact localPolynomial_product_zero_of_negative Finset.univ derivative M p q r t a
    (Finset.mem_univ _) hneg

end LocalMoments
end Problem335

end

end OAI
