import OAI.Probability.ClassicalON.LatticeModes

namespace OAI

noncomputable section
open scoped BigOperators
namespace ClassicalON

theorem dyadic_inverse_square_sum (k : ℕ) :
    (∑ p : DyadicFreq k, (1/(dyadicRadius p:ℝ))^2) ≤ 3*(k:ℝ) := by
  rw [Fintype.sum_sigma]
  calc _ ≤ ∑ j : Fin k, (3:ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          simp only [dyadicRadius, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hr : (0:ℝ) < (2^j.val:ℕ) := by positivity
          have hc : (Fintype.card (Fin (2^j.val) × Fin (2*2^j.val+1)):ℝ) ≤ 3*((2^j.val:ℕ):ℝ)^2 := by
            exact_mod_cast (dyadic_shell_card_bounds j.val).2
          calc _ ≤ (3*((2^j.val:ℕ):ℝ)^2)*(1/((2^j.val:ℕ):ℝ))^2 :=
                mul_le_mul_of_nonneg_right hc (sq_nonneg _)
               _ = 3 := by field_simp
       _ = _ := by simp; ring

theorem sum_dyadic_ratio_lower (k i : ℕ) :
    (∑ j ∈ Finset.range k, if j ≤ i then (2:ℝ)^j/2^i else 0) ≤ 2 := by
  classical
  rw [← Finset.sum_filter]
  have hs : (Finset.range k).filter (fun j => j ≤ i) ⊆ Finset.range (i+1) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    omega
  calc _ ≤ ∑ j ∈ Finset.range (i+1), (2:ℝ)^j/2^i :=
          Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
       _ ≤ 2 := by
          rw [← Finset.sum_div]
          have hh := geom_sum_mul (2:ℝ) (i+1)
          have hp : (0:ℝ) < 2^i := by positivity
          rw [div_le_iff₀ hp]
          simp only [show (2:ℝ)-1=1 by norm_num, mul_one,
            pow_succ] at hh
          linarith

theorem dyadic_min_ratio_sum (k : ℕ) :
    (∑ i : Fin k, ∑ j : Fin k, min ((2:ℝ)^i.val/2^j.val) (2^j.val/2^i.val)) ≤ 4*(k:ℝ) := by
  classical
  have point (i j : Fin k) : min ((2:ℝ)^i.val/2^j.val) (2^j.val/2^i.val) ≤
      (if j.val ≤ i.val then (2:ℝ)^j.val/2^i.val else 0)+
      (if i.val ≤ j.val then (2:ℝ)^i.val/2^j.val else 0) := by
    by_cases h : j.val ≤ i.val
    · rw [ite_eq_left h]
      exact (min_le_right _ _).trans (le_add_of_nonneg_right (by split_ifs <;> positivity))
    · have hh : i.val ≤ j.val := by omega
      rw [ite_eq_right h, ite_eq_left hh, zero_add]
      exact min_le_left _ _
  have hs : (∑ i : Fin k, ∑ j : Fin k, if j.val ≤ i.val then (2:ℝ)^j.val/2^i.val else 0) ≤ 2*(k:ℝ) := by
    calc _ ≤ ∑ _i : Fin k, (2:ℝ) := by
            apply Finset.sum_le_sum
            intro i _
            rw [← Finset.sum_range (fun j => if j ≤ i.val then (2:ℝ)^j/2^i.val else 0)]
            exact sum_dyadic_ratio_lower k i.val
         _ = _ := by simp; ring
  calc _ ≤ ∑ i : Fin k, ∑ j : Fin k,
          ((if j.val ≤ i.val then (2:ℝ)^j.val/2^i.val else 0)+
           (if i.val ≤ j.val then (2:ℝ)^i.val/2^j.val else 0)) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => point i j
       _ = 2*∑ i : Fin k, ∑ j : Fin k, if j.val ≤ i.val then (2:ℝ)^j.val/2^i.val else 0 := by
          simp only [Finset.sum_add_distrib]
          rw [Finset.sum_comm (f := fun i j : Fin k => if i.val ≤ j.val then (2:ℝ)^i.val/2^j.val else 0)]
          ring
       _ ≤ _ := by linarith

theorem weighted_dyadic_min_pair (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    a^2*b^2*min ((1/a)^3*(1/b)) ((1/b)^3*(1/a)) = min (b/a) (a/b) := by
  rw [mul_min_of_nonneg _ _ (by positivity : (0:ℝ) ≤ a^2*b^2)]
  congr 1 <;> field_simp

theorem dyadic_min_cost_sum (k : ℕ) :
    (∑ p : DyadicFreq k, ∑ q : DyadicFreq k,
      min ((1/(dyadicRadius p:ℝ))^3*(1/(dyadicRadius q:ℝ)))
          ((1/(dyadicRadius q:ℝ))^3*(1/(dyadicRadius p:ℝ)))) ≤ 36*(k:ℝ) := by
  simp only [Fintype.sum_sigma]
  have he : (∑ i : Fin k, ∑ a : Fin (2^i.val) × Fin (2*2^i.val+1),
      ∑ j : Fin k, ∑ b : Fin (2^j.val) × Fin (2*2^j.val+1),
      min ((1/(dyadicRadius ⟨i,a⟩:ℝ))^3*(1/(dyadicRadius ⟨j,b⟩:ℝ)))
          ((1/(dyadicRadius ⟨j,b⟩:ℝ))^3*(1/(dyadicRadius ⟨i,a⟩:ℝ)))) =
      ∑ i : Fin k, ∑ j : Fin k,
      (Fintype.card (Fin (2^i.val) × Fin (2*2^i.val+1)):ℝ)*
      (Fintype.card (Fin (2^j.val) × Fin (2*2^j.val+1)):ℝ)*
      min ((1/(2:ℝ)^i.val)^3*(1/(2:ℝ)^j.val))
          ((1/(2:ℝ)^j.val)^3*(1/(2:ℝ)^i.val)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [dyadicRadius, Nat.cast_pow, Nat.cast_ofNat, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [he]
  calc _ ≤ ∑ i : Fin k, ∑ j : Fin k, 9*min ((2:ℝ)^i.val/2^j.val) (2^j.val/2^i.val) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          have hi : (Fintype.card (Fin (2^i.val) × Fin (2*2^i.val+1)):ℝ) ≤ 3*((2:ℝ)^i.val)^2 := by
            exact_mod_cast (dyadic_shell_card_bounds i.val).2
          have hj : (Fintype.card (Fin (2^j.val) × Fin (2*2^j.val+1)):ℝ) ≤ 3*((2:ℝ)^j.val)^2 := by
            exact_mod_cast (dyadic_shell_card_bounds j.val).2
          calc _ ≤ (3*((2:ℝ)^i.val)^2)*(3*((2:ℝ)^j.val)^2)*
                min ((1/(2:ℝ)^i.val)^3*(1/(2:ℝ)^j.val)) ((1/(2:ℝ)^j.val)^3*(1/(2:ℝ)^i.val)) := by
                  gcongr
               _ = _ := by
                  rw [show (3*((2:ℝ)^i.val)^2)*(3*((2:ℝ)^j.val)^2) = 9*(((2:ℝ)^i.val)^2*((2:ℝ)^j.val)^2) by ring,
                    mul_assoc, weighted_dyadic_min_pair _ _ (by positivity) (by positivity), min_comm]
       _ ≤ _ := by
          simp only [← Finset.mul_sum]
          have hs := dyadic_min_ratio_sum k
          linarith

end ClassicalON

end

end OAI
