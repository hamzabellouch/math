import OAI.NumberTheory.TotientAsymptotic.NormalBandAllocation

namespace OAI

/-!
The unequal-length factor-count argument needed before matching the two
lists in the PPT construction.  A prefix of `j+1` left shifts reaching an
interval cannot be balanced by only `j` right shifts unless that interval
has small double-logarithmic length.  Consequently the required right
index exists before any equal-length `ShiftedPair` is formed.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The right list may have arbitrary length, and its first `j` shifts
need not reach the top of the interval.  Normality's upper bound handles
these truncated intervals. -/
theorem ppt_unequal_normality_gap {k l D E : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (j : Fin k)
    {S U T ε : ℝ} (hS : 1 < S) (hBS : 0 ≤ B S)
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (heq : D*shiftedProduct p = E*shiftedProduct q)
    (hDU : (largestPrimeFactor D : ℝ) ≤ U)
    (hEU : (largestPrimeFactor E : ℝ) ≤ U)
    (hSU : S ≤ U) (hUT : U < T)
    (hε : Real.sqrt (B S*B T) ≤ ε)
    (hpT : ∀ i ≤ j, T ≤ (p i-1 : ℕ))
    (hqsmall : ∀ i : Fin l, j.val ≤ i.val → (largestPrimeFactor (q i-1) : ℝ) ≤ U) :
    B T-B U ≤ (2*(j.val : ℝ)+1)*ε := by
  classical
  have hp0 (i : Fin k) : p i-1 ≠ 0 := by have := (hp i).1.two_le; omega
  have hq0 (i : Fin l) : q i-1 ≠ 0 := by have := (hq i).1.two_le; omega
  have hcount : (∑ i : Fin k, omegaIn (p i-1) U T) =
      ∑ i : Fin l, omegaIn (q i-1) U T := by
    have hh := congrArg (fun n => omegaIn n U T) heq
    unfold shiftedProduct at hh
    rw [omegaIn_mul hD (Finset.prod_ne_zero_iff.mpr (fun i _ => hp0 i)),
      omegaIn_mul hE (Finset.prod_ne_zero_iff.mpr (fun i _ => hq0 i)),
      omegaIn_eq_zero_of_largest_le hDU, omegaIn_eq_zero_of_largest_le hEU,
      zero_add, zero_add] at hh
    simpa only [omegaIn_prod _ _ (fun i _ => hp0 i),
      omegaIn_prod _ _ (fun i _ => hq0 i)] using hh
  have hcountR : (∑ i : Fin k, (omegaIn (p i-1) U T : ℝ)) =
      ∑ i : Fin l, (omegaIn (q i-1) U T : ℝ) := by exact_mod_cast hcount
  have hlo : ((j.val : ℝ)+1)*(B T-B U-ε) ≤
      ∑ i : Fin k, (omegaIn (p i-1) U T : ℝ) := by
    calc
      _ = ∑ _i ∈ Finset.Iic j, (B T-B U-ε) := by simp [Fin.card_Iic]; ring
      _ ≤ ∑ i ∈ Finset.Iic j, (omegaIn (p i-1) U T : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (normality_interval_bounds (hp i) hSU hUT (hpT i (Finset.mem_Iic.mp hi)) hε).1
      _ ≤ ∑ i : Fin k, (omegaIn (p i-1) U T : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => Nat.cast_nonneg _)
  let I : Finset (Fin l) := Finset.univ.filter (fun i => i.val < j.val)
  have hIcard : I.card ≤ j.val := by
    dsimp only [I]
    rw [Fin.card_filter_val_lt]
    exact min_le_right _ _
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans hε
  have hBU : B U ≤ B T := Real.log_le_log (Real.log_pos (hS.trans_le hSU))
    (Real.log_le_log (zero_lt_one.trans (hS.trans_le hSU)) hUT.le)
  have hupper0 : 0 ≤ B T-B U+ε := by linarith
  have hhi : (∑ i : Fin l, (omegaIn (q i-1) U T : ℝ)) ≤
      (j.val : ℝ)*(B T-B U+ε) := by
    calc
      _ = ∑ i ∈ I, (omegaIn (q i-1) U T : ℝ) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        have hji : j.val ≤ i.val := by
          by_contra hh
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
        rw [omegaIn_eq_zero_of_largest_le (hqsmall i hji), Nat.cast_zero]
      _ ≤ ∑ _i ∈ I, (B T-B U+ε) := by
        apply Finset.sum_le_sum
        intro i _
        have hh := normality_band_upper (hq i) hS hBS hSU hUT
        linarith
      _ = (I.card : ℝ)*(B T-B U+ε) := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hIcard) hupper0
  rw [hcountR] at hlo
  nlinarith

/-- A wide enough interval forces a right prime at rank at least `j`.
This proves the existence of that index; it does not assume the two lists
have the same length. -/
theorem ppt_right_index_exists {k l D E : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (j : Fin k)
    {S U T ε : ℝ} (hS : 1 < S) (hBS : 0 ≤ B S)
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (heq : D*shiftedProduct p = E*shiftedProduct q)
    (hDU : (largestPrimeFactor D : ℝ) ≤ U)
    (hEU : (largestPrimeFactor E : ℝ) ≤ U)
    (hSU : S ≤ U) (hUT : U < T)
    (hε : Real.sqrt (B S*B T) ≤ ε)
    (hpT : ∀ i ≤ j, T ≤ (p i-1 : ℕ))
    (hgap : (2*(j.val : ℝ)+1)*ε < B T-B U) :
    j.val < l ∧ ∃ i : Fin l, j.val ≤ i.val ∧ U < (largestPrimeFactor (q i-1) : ℝ) := by
  have hex : ∃ i : Fin l, j.val ≤ i.val ∧ U < (largestPrimeFactor (q i-1) : ℝ) := by
    by_contra hn
    have hsmall (i : Fin l) (hji : j.val ≤ i.val) :
        (largestPrimeFactor (q i-1) : ℝ) ≤ U := by
      exact le_of_not_gt (fun h => hn ⟨i, hji, h⟩)
    exact (not_lt_of_ge (ppt_unequal_normality_gap p q j hS hBS hD hE hp hq heq
      hDU hEU hSU hUT hε hpT hsmall)) hgap
  obtain ⟨i, hji, hi⟩ := hex
  exact ⟨hji.trans_lt i.isLt, i, hji, hi⟩

end TotientAsymptotic

end

end OAI
