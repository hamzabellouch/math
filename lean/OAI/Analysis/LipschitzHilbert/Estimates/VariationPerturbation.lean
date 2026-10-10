import OAI.Analysis.LipschitzHilbert.Estimates.FiniteVariation

namespace OAI

/-! The square-summable error in the smooth/dyadic comparison controls
its entire cubic variation, uniformly in the number of scales. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem cubic_sum_rpow_le_square_sum {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i ^ 3) ^ (2 / 3 : ℝ) ≤ ∑ i, a i ^ 2 := by
  have h := PhaseCombinatorics.sum_powers_exponent_comparison a ha
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3)
  norm_num only [Real.rpow_ofNat] at h
  have hpow := Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => pow_nonneg (ha i) 3)
    h (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ => sq_nonneg (a i))] at hpow
  norm_num at hpow ⊢
  exact hpow

theorem monotone_partition_square_sum {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) (p : Fin (N + 1) → Fin (N + 1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 2) ≤
      4 * ∑ k : Fin (N + 1), ‖F k‖ ^ 2 := by
  classical
  let s := Finset.univ.filter (fun i : Fin N => p i.castSucc < p i.succ)
  have hstep (i j : Fin N) (hij : i < j) : p i.succ ≤ p j.castSucc :=
    hp (by simpa only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] using
      (show i.val + 1 ≤ j.val by omega))
  have hleft : Set.InjOn (fun i : Fin N => p i.castSucc) s := by
    intro i hi j hj heq
    change p i.castSucc = p j.castSucc at heq
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim ((not_lt_of_ge (hstep i j hij)) (by simpa only [heq] using hi'))
    · exact hij
    · exact False.elim ((not_lt_of_ge (hstep j i hij)) (by simpa only [heq] using hj'))
  have hright : Set.InjOn (fun i : Fin N => p i.succ) s := by
    intro i hi j hj heq
    change p i.succ = p j.succ at heq
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim ((not_lt_of_ge (hstep i j hij)) (by simpa only [heq] using hj'))
    · exact hij
    · exact False.elim ((not_lt_of_ge (hstep j i hij)) (by simpa only [heq] using hi'))
  have hsumleft : (∑ i ∈ s, ‖F (p i.castSucc)‖ ^ 2) ≤
      ∑ k : Fin (N + 1), ‖F k‖ ^ 2 :=
    Finset.sum_le_sum_of_injOn (fun i : Fin N => p i.castSucc) hleft
      (Finset.subset_univ _) (fun _ _ => le_rfl) (fun _ _ _ => sq_nonneg _)
  have hsumright : (∑ i ∈ s, ‖F (p i.succ)‖ ^ 2) ≤
      ∑ k : Fin (N + 1), ‖F k‖ ^ 2 :=
    Finset.sum_le_sum_of_injOn (fun i : Fin N => p i.succ) hright
      (Finset.subset_univ _) (fun _ _ => le_rfl) (fun _ _ _ => sq_nonneg _)
  have hrestrict : (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 2) =
      ∑ i ∈ s, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hle : p i.castSucc ≤ p i.succ := hp (Fin.castSucc_le_succ i)
    have heq : p i.castSucc = p i.succ := le_antisymm hle
      (le_of_not_gt (by simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi))
    simp [heq]
  rw [hrestrict]
  calc
    _ ≤ ∑ i ∈ s, 2 * (‖F (p i.succ)‖ ^ 2 + ‖F (p i.castSucc)‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hnorm := norm_sub_le (F (p i.succ)) (F (p i.castSucc))
      have hsquare := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hnorm
      nlinarith [sq_nonneg (‖F (p i.succ)‖ - ‖F (p i.castSucc)‖)]
    _ = 2 * ((∑ i ∈ s, ‖F (p i.succ)‖ ^ 2) +
        ∑ i ∈ s, ‖F (p i.castSucc)‖ ^ 2) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 4 * ∑ k : Fin (N + 1), ‖F k‖ ^ 2 := by linarith

theorem finiteCubicVariation_le_square_energy {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) :
    (finiteCubicVariation F N) ^ (2 / 3 : ℝ) ≤
      4 * ∑ k : Fin (N + 1), ‖F k‖ ^ 2 := by
  classical
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
      ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
  change (Finset.univ.sup' _ _) ^ (2 / 3 : ℝ) ≤ _
  rw [hp]
  by_cases hmono : Monotone p
  · rw [ite_eq_left hmono]
    exact (cubic_sum_rpow_le_square_sum _ (fun _ => norm_nonneg _)).trans
      (monotone_partition_square_sum F N p hmono)
  · rw [ite_eq_right hmono, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)]
    positivity

theorem finiteCubicVariation_add_rpow {E : Type*} [NormedAddCommGroup E]
    (F G : ℕ → E) (N : ℕ) :
    (finiteCubicVariation (fun n => F n + G n) N) ^ (1 / 3 : ℝ) ≤
      (finiteCubicVariation F N) ^ (1 / 3 : ℝ) +
        (finiteCubicVariation G N) ^ (1 / 3 : ℝ) := by
  classical
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
      ∑ i : Fin N, ‖(F (p i.succ) + G (p i.succ)) -
        (F (p i.castSucc) + G (p i.castSucc))‖ ^ 3 else 0)
  change (Finset.univ.sup' _ _) ^ (1 / 3 : ℝ) ≤ _
  rw [hp]
  by_cases hmono : Monotone p
  · rw [ite_eq_left hmono]
    calc
      _ ≤ (∑ i : Fin N, (‖F (p i.succ) - F (p i.castSucc)‖ +
          ‖G (p i.succ) - G (p i.castSucc)‖) ^ 3) ^ (1 / 3 : ℝ) := by
        apply Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity) _ (by norm_num)
        apply Finset.sum_le_sum
        intro i _
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [add_sub_add_comm]
        exact norm_add_le _ _
      _ ≤ (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3) ^ (1 / 3 : ℝ) +
          (∑ i : Fin N, ‖G (p i.succ) - G (p i.castSucc)‖ ^ 3) ^ (1 / 3 : ℝ) := by
        simpa only [Real.rpow_ofNat] using Real.Lp_add_le_of_nonneg
          (Finset.univ : Finset (Fin N)) (by norm_num : (1 : ℝ) ≤ 3)
          (f := fun i => ‖F (p i.succ) - F (p i.castSucc)‖)
          (g := fun i => ‖G (p i.succ) - G (p i.castSucc)‖)
          (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      _ ≤ _ := add_le_add
        (Real.rpow_le_rpow (by positivity) (partition_le_finiteCubicVariation F N p hmono)
          (by norm_num))
        (Real.rpow_le_rpow (by positivity) (partition_le_finiteCubicVariation G N p hmono)
          (by norm_num))
  · rw [ite_eq_right hmono, Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)]
    exact add_nonneg (Real.rpow_nonneg (finiteCubicVariation_nonneg F N) _)
      (Real.rpow_nonneg (finiteCubicVariation_nonneg G N) _)

theorem finiteCubicVariation_add_square {E : Type*} [NormedAddCommGroup E]
    (F G : ℕ → E) (N : ℕ) :
    (finiteCubicVariation (fun n => F n + G n) N) ^ (2 / 3 : ℝ) ≤
      2 * (finiteCubicVariation F N) ^ (2 / 3 : ℝ) +
        2 * (finiteCubicVariation G N) ^ (2 / 3 : ℝ) := by
  have h := finiteCubicVariation_add_rpow F G N
  have hsq := pow_le_pow_left₀ (Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _) h 2
  have heq (a : ℝ) (ha : 0 ≤ a) : (a ^ (1 / 3 : ℝ)) ^ 2 = a ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have hcross := sq_nonneg ((finiteCubicVariation F N) ^ (1 / 3 : ℝ) -
    (finiteCubicVariation G N) ^ (1 / 3 : ℝ))
  rw [sub_sq, heq _ (finiteCubicVariation_nonneg F N),
    heq _ (finiteCubicVariation_nonneg G N)] at hcross
  rw [heq _ (finiteCubicVariation_nonneg _ _)] at hsq
  rw [add_sq, heq _ (finiteCubicVariation_nonneg F N),
    heq _ (finiteCubicVariation_nonneg G N)] at hsq
  linarith

/-- The manuscript's smooth partial sums are a dyadic martingale plus
the square-summable comparison error. No scale-count factor occurs. -/
theorem finiteCubicVariation_comparison {E : Type*} [NormedAddCommGroup E]
    (P M : ℕ → E) (N : ℕ) :
    (finiteCubicVariation P N) ^ (2 / 3 : ℝ) ≤
      2 * (finiteCubicVariation M N) ^ (2 / 3 : ℝ) +
        8 * ∑ k : Fin (N + 1), ‖P k - M k‖ ^ 2 := by
  have heq : (fun n => M n + (P n - M n)) = P := by funext n; abel
  have h := finiteCubicVariation_add_square M (fun n => P n - M n) N
  rw [heq] at h
  exact h.trans (add_le_add le_rfl
    (by linarith [finiteCubicVariation_le_square_energy (fun n => P n - M n) N]))

end LipschitzHilbert

end

end OAI
