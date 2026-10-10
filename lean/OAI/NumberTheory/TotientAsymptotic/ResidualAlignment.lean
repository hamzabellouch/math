import OAI.NumberTheory.TotientAsymptotic.OrderedAlignment

namespace OAI

/-! Alignment of the two ordered lists of largest factors after prefix cancellation. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- Disjoint decreasing bands turn the factor-count argument into an absolute
bound at every paired index. The residual factors are below the lower edge of the prime-factor bands;
this edge may be strictly above the normality parameter, as in the application. -/
theorem ordered_largest_factor_alignment_smooth_cutoff {k D D' : ℕ} (p q : Fin k → ℕ)
    {S Z ε : ℝ} (hSone : 1 < S) (hSZ : S ≤ Z) (hD : D ≠ 0) (hD' : D' ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (heq : D*shiftedProduct p = D'*shiftedProduct q)
    (hDs : (largestPrimeFactor D : ℝ) ≤ Z)
    (hD's : (largestPrimeFactor D' : ℝ) ≤ Z)
    (hS : ∀ i, Z ≤ min (largestPrimeFactor (p i-1) : ℝ)
      (largestPrimeFactor (q i-1) : ℝ))
    (hsep : ∀ i j, i < j →
      max (largestPrimeFactor (p j-1) : ℝ) (largestPrimeFactor (q j-1) : ℝ) ≤
      min (largestPrimeFactor (p i-1) : ℝ) (largestPrimeFactor (q i-1) : ℝ))
    (herr : ∀ i, Real.sqrt (B S * B (max (largestPrimeFactor (p i-1) : ℝ)
      (largestPrimeFactor (q i-1) : ℝ))) ≤ ε) :
    ∀ j, |B (largestPrimeFactor (p j-1))-B (largestPrimeFactor (q j-1))| ≤
      (2*(j.val : ℝ)+1)*ε := by
  have hle (r : Fin k → ℕ) (hr : ∀ i, IsNormalPrime S (r i)) (i : Fin k) :
      (largestPrimeFactor (r i-1) : ℝ) ≤ (r i-1 : ℕ) := by
    have hn : r i-1 ≠ 0 := by have := (hr i).1.two_le; omega
    have : largestPrimeFactor (r i-1) ≤ r i-1 := by
      unfold largestPrimeFactor
      apply max_le (by omega)
      apply Finset.sup_le
      intro a ha
      exact Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors ha)
    exact_mod_cast this
  have hside (r t : Fin k → ℕ) (hr : ∀ i, IsNormalPrime S (r i))
      (ht : ∀ i, IsNormalPrime S (t i)) (E E' : ℕ) (hE : E ≠ 0) (hE' : E' ≠ 0)
      (he : E*shiftedProduct r = E'*shiftedProduct t)
      (hEs : (largestPrimeFactor E : ℝ) ≤ Z)
      (hE's : (largestPrimeFactor E' : ℝ) ≤ Z)
      (hs : ∀ i, Z ≤ min (largestPrimeFactor (r i-1) : ℝ)
        (largestPrimeFactor (t i-1) : ℝ))
      (hord : ∀ i j, i < j →
        max (largestPrimeFactor (r j-1) : ℝ) (largestPrimeFactor (t j-1) : ℝ) ≤
        min (largestPrimeFactor (r i-1) : ℝ) (largestPrimeFactor (t i-1) : ℝ))
      (heps : ∀ i, Real.sqrt (B S * B (max (largestPrimeFactor (r i-1) : ℝ)
        (largestPrimeFactor (t i-1) : ℝ))) ≤ ε)
      (j : Fin k) (hjt : (largestPrimeFactor (t j-1) : ℝ) < largestPrimeFactor (r j-1)) :
      B (largestPrimeFactor (r j-1))-B (largestPrimeFactor (t j-1)) ≤
        (2*(j.val : ℝ)+1)*ε := by
    apply normality_alignment r t j hE hE' hr ht he
      (hEs.trans ((hs j).trans (min_le_right _ _)))
      (hE's.trans ((hs j).trans (min_le_right _ _)))
      (hSZ.trans ((hs j).trans (min_le_right _ _))) hjt
    · simpa only [max_eq_left hjt.le] using heps j
    · intro i hij
      apply le_trans _ (hle r hr i)
      rcases lt_or_eq_of_le hij with hij | rfl
      · exact (le_max_left _ _).trans ((hord i j hij).trans (min_le_left _ _))
      · rfl
    · intro i hij
      exact (le_max_left _ _).trans ((hord i j hij).trans
        ((min_le_right _ _).trans (hle t ht i)))
    · intro i hji
      rcases lt_or_eq_of_le hji with hji | rfl
      · exact (le_max_right _ _).trans ((hord j i hji).trans (min_le_right _ _))
      · rfl
  have hmono {v w : ℝ} (hv : S ≤ v) (hvw : v ≤ w) : B v ≤ B w :=
    Real.log_le_log (Real.log_pos (hSone.trans_le hv))
      (Real.log_le_log (zero_lt_one.trans (hSone.trans_le hv)) hvw)
  intro j
  have hn : 0 ≤ ε := (Real.sqrt_nonneg _).trans (herr j)
  have hbound : 0 ≤ (2*(j.val : ℝ)+1)*ε := by positivity
  rcases lt_trichotomy (largestPrimeFactor (q j-1)) (largestPrimeFactor (p j-1)) with hj | hj | hj
  · have hjR : (largestPrimeFactor (q j-1) : ℝ) < largestPrimeFactor (p j-1) := by exact_mod_cast hj
    have hb := hmono (hSZ.trans ((hS j).trans (min_le_right _ _))) hjR.le
    rw [abs_of_nonneg (sub_nonneg.mpr hb)]
    exact hside p q hp hq D D' hD hD' heq hDs hD's hS hsep herr j hjR
  · simp only [hj, sub_self, abs_zero]
    exact hbound
  · have hjR : (largestPrimeFactor (p j-1) : ℝ) < largestPrimeFactor (q j-1) := by exact_mod_cast hj
    have hb := hmono (hSZ.trans ((hS j).trans (min_le_left _ _))) hjR.le
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hb)]
    exact hside q p hq hp D' D hD' hD heq.symm hD's hDs
      (by simpa only [min_comm] using hS)
      (by simpa only [min_comm, max_comm] using hsep)
      (by simpa only [max_comm] using herr) j hjR

end TotientAsymptotic

end

end OAI
