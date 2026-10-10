import OAI.Probability.SignedSweeps.BudgetBounds

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma descFactorial_exp_lower {a h : ℕ} (ha : 0 < a) (hh : h ≤ a) :
    (a : ℝ) ^ h * Real.exp (-2 * (h : ℝ)) ≤ (a.descFactorial h : ℝ) := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  by_cases hsmall : 2 * h ≤ a
  · have hsub : (a : ℝ) / 2 ≤ ((a + 1 - h : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      have : (2 : ℝ) * h ≤ a := by exact_mod_cast hsmall
      linarith
    have hexp : Real.exp (-2) ≤ (1 : ℝ) / 2 := by
      rw [Real.exp_neg]
      have he : 2 ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) he
    calc
      _ = ((a : ℝ) * Real.exp (-2)) ^ h := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
      _ ≤ ((a : ℝ) / 2) ^ h :=
        pow_le_pow_left₀ (by positivity)
          (by simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hexp hap.le) h
      _ ≤ (((a + 1 - h : ℕ) : ℝ)) ^ h := pow_le_pow_left₀ (by positivity) hsub h
      _ ≤ _ := by exact_mod_cast Nat.pow_sub_le_descFactorial a h
  · have hlarge : a ≤ 2 * h := by omega
    have hf : ((a - h).factorial : ℝ) ≤ (a : ℝ) ^ (a - h) := by
      exact_mod_cast (Nat.factorial_le_pow (a - h)).trans
        (Nat.pow_le_pow_left (Nat.sub_le a h) (a - h))
    have hfac : ((a - h).factorial : ℝ) * (a.descFactorial h : ℝ) = (a.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hh
    have he : (a : ℝ) ^ a ≤ Real.exp a * (a.factorial : ℝ) := by
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < a.factorial)).mp
        (Real.pow_div_factorial_le_exp (a : ℝ) hap.le a)
    have h₁ : (a : ℝ) ^ (a - h) * (a : ℝ) ^ h ≤
        (a : ℝ) ^ (a - h) * (Real.exp a * (a.descFactorial h : ℝ)) := by
      calc
        _ = (a : ℝ) ^ a := by rw [← pow_add, Nat.sub_add_cancel hh]
        _ ≤ Real.exp a * (a.factorial : ℝ) := he
        _ = Real.exp a * (((a - h).factorial : ℝ) * (a.descFactorial h : ℝ)) := by rw [hfac]
        _ ≤ Real.exp a * ((a : ℝ) ^ (a - h) * (a.descFactorial h : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hf (by positivity)) (by positivity)
        _ = _ := by ring
    have h₂ := le_of_mul_le_mul_left h₁ (pow_pos hap (a - h))
    calc
      _ ≤ (a : ℝ) ^ h * Real.exp (-(a : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        have : (a : ℝ) ≤ 2 * h := by exact_mod_cast hlarge
        linarith
      _ ≤ (Real.exp a * (a.descFactorial h : ℝ)) * Real.exp (-(a : ℝ)) :=
        mul_le_mul_of_nonneg_right h₂ (by positivity)
      _ = _ := by rw [Real.exp_neg]; field_simp

lemma descFactorial_inv_upper {a h : ℕ} (ha : 0 < a) (hh : h ≤ a) :
    (a.descFactorial h : ℝ)⁻¹ ≤ ((a : ℝ) ^ h)⁻¹ * Real.exp (2 * (h : ℝ)) := by
  have hf : (0 : ℝ) < a.descFactorial h := by
    exact_mod_cast Nat.descFactorial_pos.mpr hh
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  calc
    _ ≤ ((a : ℝ) ^ h * Real.exp (-2 * (h : ℝ)))⁻¹ :=
      (inv_le_inv₀ hf (by positivity)).mpr (descFactorial_exp_lower ha hh)
    _ = _ := by
      rw [mul_inv_rev, ← Real.exp_neg, mul_comm, show -(-2 * (h : ℝ)) = 2 * h by ring]

lemma occupancy_col_le {s m l : ℕ} (z : HolePlacement s m l) (j : Fin m) :
    (occupancy (fun i => (z.1 i).2) j).val ≤ s := by
  classical
  change (Finset.univ.filter (fun i => (z.1 i).2 = j)).card ≤ s
  calc
    _ ≤ (Finset.univ : Finset (Fin s)).card := ?_
    _ = s := by simp
  
  refine Finset.card_le_card_of_injOn (fun i => (z.1 i).1) (by simp) ?_
  intro i hi k hk heq
  apply z.2
  exact Prod.ext heq ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hk).2.symm)

lemma occupancy_row_le {s m l : ℕ} (z : HolePlacement s m l) (j : Fin s) :
    (occupancy (fun i => (z.1 i).1) j).val ≤ m := by
  classical
  change (Finset.univ.filter (fun i => (z.1 i).1 = j)).card ≤ m
  calc
    _ ≤ (Finset.univ : Finset (Fin m)).card := ?_
    _ = m := by simp
  
  refine Finset.card_le_card_of_injOn (fun i => (z.1 i).2) (by simp) ?_
  intro i hi k hk heq
  apply z.2
  exact Prod.ext ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hk).2.symm) heq

def holePrefactor {s m l : ℕ} (z : HolePlacement s m l) : ℝ :=
  (∏ j : Fin m, (s.descFactorial (occupancy (fun i => (z.1 i).2) j).val : ℝ)⁻¹) *
    ∏ j : Fin s, (m.descFactorial (occupancy (fun i => (z.1 i).1) j).val : ℝ)⁻¹

lemma occupancy_factorial_bound {a l q : ℕ} (ha : 0 < a) (f : Fin l → Fin q)
    (hf : ∀ j, (occupancy f j).val ≤ a) :
    (∏ j, (a.descFactorial (occupancy f j).val : ℝ)⁻¹) ≤
      ((a : ℝ) ^ l)⁻¹ * Real.exp (2 * (l : ℝ)) := by
  classical
  refine (Finset.prod_le_prod₀ (fun _ _ => by positivity)
    (fun j _ => descFactorial_inv_upper ha (hf j))).trans_eq ?_
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum,
    occupancy_sum, ← Real.exp_sum, ← Finset.mul_sum, ← Nat.cast_sum, occupancy_sum]

lemma holePrefactor_bound {s m l : ℕ} (hs : 0 < s) (hm : 0 < m)
    (z : HolePlacement s m l) :
    holePrefactor z ≤ (((s * m : ℕ) : ℝ) ^ l)⁻¹ * Real.exp (4 * (l : ℝ)) := by
  unfold holePrefactor
  refine (mul_le_mul
    (occupancy_factorial_bound hs (fun i => (z.1 i).2) (occupancy_col_le z))
    (occupancy_factorial_bound hm (fun i => (z.1 i).1) (occupancy_row_le z))
    (Finset.prod_nonneg (fun _ _ => by positivity)) (by positivity)).trans_eq ?_
  rw [Nat.cast_mul, mul_pow, mul_inv_rev]
  calc
    _ = (((s : ℝ) ^ l)⁻¹ * ((m : ℝ) ^ l)⁻¹) *
        (Real.exp (2 * (l : ℝ)) * Real.exp (2 * (l : ℝ))) := by ring
    _ = _ := by
      rw [← Real.exp_add, show 2 * (l : ℝ) + 2 * l = 4 * l by ring]
      ring

end SignedSweeps
end

end OAI
