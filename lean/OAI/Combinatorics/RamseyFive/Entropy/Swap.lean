import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.Map

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

noncomputable def swap (p : Law (α × β)) : Law (β × α) where
  mass z := p (z.2,z.1)
  nonneg z := p.nonneg _
  sum_one := by rw [Fintype.sum_prod_type,Finset.sum_comm,←Fintype.sum_prod_type]; exact p.sum_one

@[simp] lemma swap_mass (p : Law (α × β)) (b : β) (a : α) : swap p (b,a)=p (a,b) := rfl
@[simp] lemma first_swap (p : Law (α × β)) : first (swap p)=second p := by
  apply Law.ext
  rfl

lemma mass_eq_second_mul_fiber (p : Law (α × β)) (a : α) (b : β) :
    p (a,b)=second p b*fiber (swap p) b a := by
  simpa only [first_swap,swap_mass] using mass_eq_first_mul_fiber (swap p) b a

theorem product_crossed_expectation (p : Law (α × β)) (q : Law (γ × δ))
    (F : α → β → γ → δ → ℝ) :
    (∑ z : (α × β) × (γ × δ),product p q z*F z.1.1 z.1.2 z.2.1 z.2.2)=
      ∑ a,∑ y,(first p a*second q y)*
        (∑ b,∑ c,(fiber p a b*fiber (swap q) y c)*F a b c y) := by
  simp only [Fintype.sum_prod_type]
  change (∑ a,∑ b,∑ c,∑ y,p (a,b)*q (c,y)*F a b c y)=_
  apply Finset.sum_congr rfl
  intro a _
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [mass_eq_first_mul_fiber p a b,mass_eq_second_mul_fiber q c y]
  ring

theorem zero_joint_event_product (p : Law (α × β)) (E : Finset (α × β))
    (hzero : ∑ z∈E,p z=0) :
    (∑ z∈E,product (first p) (second p) z)≤
      2*(entropy (first p)+entropy (second p)-entropy p) := by
  have h := event_comparison p (product (first p) (second p)) (ac_product p) E
  rw [hzero,add_zero,mutual_information] at h
  exact h
end SharpRamseyFive.FiniteEntropy

end OAI
