import OAI.Combinatorics.ContingencyTables.Transport.RationalWalks

namespace OAI

/-! # Adaptive completion errors add once per actual transition -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {α β : Type*} [Fintype α] [Fintype β]

theorem variation_bind_two (p q : RationalLaw α) (K L : α → RationalLaw β) :
    variation (bindLaw p K) (bindLaw q L) ≤
      variation p q+∑ x,p.mass x*variation (K x) (L x) := by
  have hpoint (x : α) (y : β) :
      |p.mass x*(K x).mass y-q.mass x*(L x).mass y| ≤
        p.mass x*|(K x).mass y-(L x).mass y|+|p.mass x-q.mass x| *(L x).mass y := by
    calc
      _ = |p.mass x*((K x).mass y-(L x).mass y)+(p.mass x-q.mass x)*(L x).mass y| := by
        congr 1
        ring
      _ ≤ |p.mass x*((K x).mass y-(L x).mass y)|+|(p.mass x-q.mass x)*(L x).mass y| :=
        abs_add_le _ _
      _ = _ := by
        rw [abs_mul,abs_mul,abs_of_nonneg (p.nonnegative x),abs_of_nonneg ((L x).nonnegative y)]
  have hsum :
      (∑ y,|∑ x,(p.mass x*(K x).mass y-q.mass x*(L x).mass y)|) ≤
      (∑ x,|p.mass x-q.mass x|)+∑ x,p.mass x*(∑ y,|(K x).mass y-(L x).mass y|) := by
    calc
      _ ≤ ∑ y,∑ x,|p.mass x*(K x).mass y-q.mass x*(L x).mass y| :=
        Finset.sum_le_sum (fun y _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ y,∑ x,(p.mass x*|(K x).mass y-(L x).mass y|+
          |p.mass x-q.mass x| *(L x).mass y) :=
        Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun x _ => hpoint x y))
      _ = _ := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_add_distrib,← Finset.mul_sum,(L _).total,mul_one]
        ring
  unfold variation
  change (∑ y,|(∑ x,p.mass x*(K x).mass y)-(∑ x,q.mass x*(L x).mass y)|)/2 ≤ _
  simp_rw [← Finset.sum_sub_distrib]
  have hh := div_le_div_of_nonneg_right hsum (show (0:ℚ) ≤ 2 by norm_num)
  convert hh using 1
  simp only [add_div,Finset.sum_div,mul_div_assoc]

theorem variation_bind_uniform (p q : RationalLaw α) (K L : α → RationalLaw β)
    (η : ℚ) (hη : ∀ x,variation (K x) (L x) ≤ η) :
    variation (bindLaw p K) (bindLaw q L) ≤ variation p q+η := by
  calc
    _ ≤ variation p q+∑ x,p.mass x*variation (K x) (L x) := variation_bind_two p q K L
    _ ≤ variation p q+∑ x,p.mass x*η := by
      apply add_le_add_right
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hη x) (p.nonnegative x))
    _ = _ := by rw [← Finset.sum_mul,p.total,one_mul]

variable [DecidableEq α]

/-- The common state may depend on earlier randomness. Only the uniform
one-step bound is used; the approximating chain need not be reversible. -/
theorem walkLaw_variation (K L : α → RationalLaw α) (η : ℚ)
    (hη : ∀ x,variation (K x) (L x) ≤ η) (a : α) (n : ℕ) :
    variation (walkLaw K a n) (walkLaw L a n) ≤ n*η := by
  induction n with
  | zero => simp [walkLaw,variation]
  | succ n ih =>
    change variation (bindLaw (walkLaw K a n) K) (bindLaw (walkLaw L a n) L) ≤ _
    calc
      _ ≤ variation (walkLaw K a n) (walkLaw L a n)+η := variation_bind_uniform _ _ K L η hη
      _ ≤ (n:ℚ)*η+η := add_le_add_left ih η
      _ = _ := by push_cast; ring

theorem walkLaw_terminal_variation (K L : α → RationalLaw α)
    (F G : α → RationalLaw β) (η : ℚ)
    (hη : ∀ x,variation (K x) (L x) ≤ η)
    (hterminal : ∀ x,variation (F x) (G x) ≤ η) (a : α) (n : ℕ) :
    variation (bindLaw (walkLaw K a n) F) (bindLaw (walkLaw L a n) G) ≤ (n+1)*η := by
  calc
    _ ≤ variation (walkLaw K a n) (walkLaw L a n)+η := variation_bind_uniform _ _ F G η hterminal
    _ ≤ (n:ℚ)*η+η := add_le_add_left (walkLaw_variation K L η hη a n) η
    _ = _ := by ring

end ContingencyTables.FirstSuccess

end OAI
