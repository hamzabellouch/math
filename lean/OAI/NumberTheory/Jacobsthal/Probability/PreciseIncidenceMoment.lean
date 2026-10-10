import OAI.NumberTheory.Jacobsthal.Estimates.FactorDividesAbscissa

namespace OAI

namespace Erdos970

section

namespace ErdosLineCollision
open ErdosInverseIncidence
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem precise_multiplicity_square_upper {α β : Type*} (A : Finset α) (Q : Finset β)
    (R : α → β → Prop) (K : ℝ) (hK : 0 ≤ K)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      ((Q.filter (fun p => R a p ∧ R b p)).card : ℝ) ≤ K) :
    (∑ p ∈ Q,(multiplicity A R p)^2) ≤
      (∑ p ∈ Q,multiplicity A R p)+K*(A.card : ℝ)^2 := by
  rw [multiplicity_square_sum,multiplicity_sum]
  calc
    _ ≤ ∑ a ∈ A,∑ b ∈ A,((if b=a then (degree Q R a : ℝ) else 0)+K) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      by_cases hab : b=a
      · subst b
        simp only [and_self,degree]
        exact le_add_of_nonneg_right hK
      · rw [ite_eq_right hab,zero_add]
        exact hpair a ha b hb (Ne.symm hab)
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.sum_const,nsmul_eq_mul]
      have he : (∑ a ∈ A,if a ∈ A then (degree Q R a : ℝ) else 0) =
          ∑ a ∈ A,(degree Q R a : ℝ) := by simp
      rw [he]
      ring

theorem precise_incidence_cauchy {α β : Type*} (A : Finset α) (Q : Finset β)
    (R : α → β → Prop) (K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hQ : (Q.card : ℝ) ≤ B)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      ((Q.filter (fun p => R a p ∧ R b p)).card : ℝ) ≤ K) :
    (∑ p ∈ Q,multiplicity A R p)^2 ≤
      B*(K*(A.card : ℝ)^2+∑ p ∈ Q,multiplicity A R p) := by
  have hcs : (∑ p ∈ Q,multiplicity A R p)^2 ≤ (Q.card : ℝ)*(∑ p ∈ Q,(multiplicity A R p)^2) := by
    simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq Q (fun _ => (1 : ℝ)) (multiplicity A R)
  have hup := precise_multiplicity_square_upper A Q R K hK hpair
  calc
    _ ≤ (Q.card : ℝ)*(∑ p ∈ Q,(multiplicity A R p)^2) := hcs
    _ ≤ B*(∑ p ∈ Q,(multiplicity A R p)^2) := mul_le_mul_of_nonneg_right hQ
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ ≤ B*((∑ p ∈ Q,multiplicity A R p)+K*(A.card : ℝ)^2) := mul_le_mul_of_nonneg_left hup hB
    _ = _ := by ring

end ErdosLineCollision

end

end Erdos970

end OAI
