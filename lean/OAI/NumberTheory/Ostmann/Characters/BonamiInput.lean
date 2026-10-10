import OAI.NumberTheory.Ostmann.Characters.BonamiTensor

namespace OAI

/-! # Discharge of the published Bonami input

The finite even-moment specialization is proved here from the elementary
two-point inequality and finite convexity. No infinite-product theorem is
needed for the application.
-/

namespace Ostmann

open Finset
open scoped Classical BigOperators

noncomputable def boolFinsetEquiv (α : Type*) [Fintype α] :
    (α → Bool) ≃ Finset α where
  toFun b := univ.filter fun i => b i = true
  invFun Q i := decide (i ∈ Q)
  left_inv b := by
    funext i
    cases h : b i <;> simp [h]
  right_inv Q := by ext i; simp

theorem booleanPolynomial_eq_rademacher {P : Finset ℕ}
    (a : Finset P → ℝ) (ε : P → Bool) :
    booleanPolynomial (fun b => a (boolFinsetEquiv P b)) ε =
      ∑ Q : Finset P, a Q * rademacherMonomial Q ε := by
  unfold booleanPolynomial
  calc
    _ = ∑ b : P → Bool, a (boolFinsetEquiv P b) *
        rademacherMonomial (boolFinsetEquiv P b) ε := by
      simp only [finite_univ_canonical]
      apply sum_congr rfl
      intro b hb
      congr 1
      simp only [boolFinsetEquiv, Equiv.coe_fn_mk, rademacherMonomial, prod_filter]
      simp only [finite_univ_canonical]
    _ = _ := by
      simpa only [finite_univ_canonical] using
        (boolFinsetEquiv P).sum_comp (fun Q => a Q * rademacherMonomial Q ε)

theorem booleanEnergy_eq_finset {α : Type*} [Fintype α]
    (r : ℝ) (a : Finset α → ℝ) :
    booleanEnergy r (fun b => a (boolFinsetEquiv α b)) =
      ∑ Q : Finset α, r ^ Q.card * (a Q) ^ 2 := by
  unfold booleanEnergy
  calc
    _ = ∑ b : α → Bool, r ^ (boolFinsetEquiv α b).card *
        (a (boolFinsetEquiv α b)) ^ 2 := by
      apply sum_congr rfl
      intro b hb
      congr 1
      rw [← prod_const]
      simp only [boolFinsetEquiv, Equiv.coe_fn_mk, prod_filter]
    _ = _ := by
      simpa only [finite_univ_canonical] using
        (boolFinsetEquiv α).sum_comp (fun Q => r ^ Q.card * (a Q) ^ 2)

/-- The exact `p=2`, `q=2l` finite-cube specialization of Bonami is proved. -/
theorem publishedBonamiBound : PublishedBonamiBound := by
  intro P l hl a
  have h := booleanPolynomial_moment l hl P (fun b => a (boolFinsetEquiv P b))
  simp only [booleanMoment, booleanPolynomial_eq_rademacher, booleanEnergy_eq_finset] at h
  have hc : 0 < (Fintype.card (P → Bool) : ℝ) := by exact_mod_cast Fintype.card_pos
  simp only [Fintype.card, finite_univ_canonical] at h hc ⊢
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hc.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hh

end Ostmann

end OAI
