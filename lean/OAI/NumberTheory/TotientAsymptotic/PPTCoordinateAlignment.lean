import OAI.NumberTheory.TotientAsymptotic.PPTUnequalAlignment

namespace OAI

/-!
Apply the unequal-list count to the actual ordering by prime size.  This
proves existence of a right prime at the required index, and then compares
the largest factors of the two prime predecessors.  The additive `log K`
is the explicit cost of passing from a predecessor to its largest factor
when its total number of prime factors is at most `K`.
-/

noncomputable section

namespace TotientAsymptotic

theorem ppt_ordered_right_index {k l D E : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (j : Fin k)
    {S T ε : ℝ} (hS : 1 < S) (hBS : 0 ≤ B S)
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (hpa : Antitone p) (hqa : Antitone q)
    (heq : D*shiftedProduct p = E*shiftedProduct q)
    (hDS : (largestPrimeFactor D : ℝ) ≤ S)
    (hES : (largestPrimeFactor E : ℝ) ≤ S)
    (hST : S < T) (hTp : T ≤ (p j-1 : ℕ))
    (hε : Real.sqrt (B S*B T) ≤ ε)
    (hgap : (2*(j.val : ℝ)+1)*ε < B T-B S) :
    ∃ hj : j.val < l, S < (q ⟨j.val, hj⟩-1 : ℕ) := by
  have hpT (i : Fin k) (hij : i ≤ j) : T ≤ (p i-1 : ℕ) :=
    hTp.trans (Nat.cast_le.mpr (Nat.sub_le_sub_right (hpa hij) 1))
  obtain ⟨hj, i, hji, hi⟩ := ppt_right_index_exists p q j hS hBS hD hE hp hq heq
    hDS hES le_rfl hST hε hpT hgap
  refine ⟨hj, ?_⟩
  have hqi : q i ≤ q ⟨j.val, hj⟩ := hqa (show (⟨j.val, hj⟩ : Fin l) ≤ i from hji)
  have hqone : 1 ≤ q i-1 := by have := (hq i).1.two_le; omega
  exact (hi.trans_le (Nat.cast_le.mpr (largestPrimeFactor_le_self hqone))).trans_le
    (Nat.cast_le.mpr (Nat.sub_le_sub_right hqi 1))

private theorem ppt_ordered_alignment_side {k l D E : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (j : Fin k) (j' : Fin l)
    (hindex : j.val = j'.val) {S ε K : ℝ}
    (hS : 1 < S) (hBS : 0 ≤ B S) (hK : 0 < K)
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (hpa : Antitone p) (hqa : Antitone q)
    (heq : D*shiftedProduct p = E*shiftedProduct q)
    (hp3 : 3 ≤ p j) (hq3 : 3 ≤ q j')
    (hDS : (largestPrimeFactor D : ℝ) ≤ (q j'-1 : ℕ))
    (hES : (largestPrimeFactor E : ℝ) ≤ (q j'-1 : ℕ))
    (hSsmall : S ≤ (q j'-1 : ℕ))
    (hΩ : ((q j'-1).primeFactorsList.length : ℝ) ≤ K)
    (hε : Real.sqrt (B S*B (largestPrimeFactor (p j-1))) ≤ ε) :
    B (largestPrimeFactor (p j-1))-B (largestPrimeFactor (q j'-1)) ≤
      (2*(j.val : ℝ)+1)*ε+Real.log K := by
  let U : ℝ := (q j'-1 : ℕ)
  let T : ℝ := largestPrimeFactor (p j-1)
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans hε
  have hcoef : 0 ≤ (2*(j.val : ℝ)+1)*ε := by positivity
  have hT : 1 < T := by
    dsimp only [T]
    exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ p j-1 by omega)
  have hpT (i : Fin k) (hij : i ≤ j) : T ≤ (p i-1 : ℕ) := by
    have hsmall : largestPrimeFactor (p j-1) ≤ p j-1 :=
      largestPrimeFactor_le_self (by omega)
    exact Nat.cast_le.mpr (hsmall.trans (Nat.sub_le_sub_right (hpa hij) 1))
  have hqsmall (i : Fin l) (hji : j.val ≤ i.val) :
      (largestPrimeFactor (q i-1) : ℝ) ≤ U := by
    have hqone : 1 ≤ q i-1 := by have := (hq i).1.two_le; omega
    have hqij : q i ≤ q j' := hqa (show j' ≤ i from by change j'.val ≤ i.val; omega)
    exact Nat.cast_le.mpr ((largestPrimeFactor_le_self hqone).trans
      (Nat.sub_le_sub_right hqij 1))
  have hgap : B T-B U ≤ (2*(j.val : ℝ)+1)*ε := by
    by_cases hUT : U < T
    · exact ppt_unequal_normality_gap p q j hS hBS hD hE hp hq heq
        hDS hES hSsmall hUT hε hpT hqsmall
    · have hmono : B T ≤ B U := Real.log_le_log (Real.log_pos hT)
        (Real.log_le_log (zero_lt_one.trans hT) (le_of_not_gt hUT))
      linarith
  have hlower := largest_factor_doubleLog_lower (show 2 ≤ q j'-1 by omega) hK hΩ
  change B T-B (largestPrimeFactor (q j'-1)) ≤ _
  change B U-Real.log K ≤ B (largestPrimeFactor (q j'-1)) at hlower
  linarith

/-- Ordered prime lists need not have equal total lengths.  Once index `j`
exists on both sides, normality aligns their largest predecessor factors
with an explicit additive error. -/
theorem ppt_ordered_coordinate_alignment {k l D E j : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (hjk : j < k) (hjl : j < l)
    {S ε K : ℝ} (hS : 1 < S) (hBS : 0 ≤ B S) (hK : 0 < K)
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (hpa : Antitone p) (hqa : Antitone q)
    (heq : D*shiftedProduct p = E*shiftedProduct q)
    (hp3 : 3 ≤ p ⟨j,hjk⟩) (hq3 : 3 ≤ q ⟨j,hjl⟩)
    (hDS : (largestPrimeFactor D : ℝ) ≤
      min ((p ⟨j,hjk⟩-1 : ℕ) : ℝ) ((q ⟨j,hjl⟩-1 : ℕ) : ℝ))
    (hES : (largestPrimeFactor E : ℝ) ≤
      min ((p ⟨j,hjk⟩-1 : ℕ) : ℝ) ((q ⟨j,hjl⟩-1 : ℕ) : ℝ))
    (hSsmall : S ≤ min ((p ⟨j,hjk⟩-1 : ℕ) : ℝ) ((q ⟨j,hjl⟩-1 : ℕ) : ℝ))
    (hΩp : ((p ⟨j,hjk⟩-1).primeFactorsList.length : ℝ) ≤ K)
    (hΩq : ((q ⟨j,hjl⟩-1).primeFactorsList.length : ℝ) ≤ K)
    (hεp : Real.sqrt (B S*B (largestPrimeFactor (p ⟨j,hjk⟩-1))) ≤ ε)
    (hεq : Real.sqrt (B S*B (largestPrimeFactor (q ⟨j,hjl⟩-1))) ≤ ε) :
    |B (largestPrimeFactor (p ⟨j,hjk⟩-1))-B (largestPrimeFactor (q ⟨j,hjl⟩-1))| ≤
      (2*(j : ℝ)+1)*ε+Real.log K := by
  have hleft := ppt_ordered_alignment_side p q ⟨j,hjk⟩ ⟨j,hjl⟩ rfl hS hBS hK hD hE
    hp hq hpa hqa heq hp3 hq3 (hDS.trans (min_le_right _ _))
    (hES.trans (min_le_right _ _)) (hSsmall.trans (min_le_right _ _)) hΩq hεp
  have hright := ppt_ordered_alignment_side q p ⟨j,hjl⟩ ⟨j,hjk⟩ rfl hS hBS hK hE hD
    hq hp hqa hpa heq.symm hq3 hp3 (hES.trans (min_le_left _ _))
    (hDS.trans (min_le_left _ _)) (hSsmall.trans (min_le_left _ _)) hΩp hεq
  exact abs_le.mpr ⟨by linarith, hleft⟩

/-- Normality supplies the factor-count and square-root error bounds.  The
remaining logarithmic error is explicit after normalization by `B z`. -/
theorem ppt_normalized_coordinate_alignment {k l D E j : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (hjk : j < k) (hjl : j < l)
    {S z : ℝ} (hS : 1 < S) (hBS : 0 ≤ B S) (hBz : 0 < B z) (hSz : S ≤ z)
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (hpa : Antitone p) (hqa : Antitone q)
    (heq : D*shiftedProduct p = E*shiftedProduct q)
    (hp3 : 3 ≤ p ⟨j,hjk⟩) (hq3 : 3 ≤ q ⟨j,hjl⟩)
    (hpz : (p ⟨j,hjk⟩-1 : ℕ) ≤ z) (hqz : (q ⟨j,hjl⟩-1 : ℕ) ≤ z)
    (hDS : (largestPrimeFactor D : ℝ) ≤
      min ((p ⟨j,hjk⟩-1 : ℕ) : ℝ) ((q ⟨j,hjl⟩-1 : ℕ) : ℝ))
    (hES : (largestPrimeFactor E : ℝ) ≤
      min ((p ⟨j,hjk⟩-1 : ℕ) : ℝ) ((q ⟨j,hjl⟩-1 : ℕ) : ℝ))
    (hSsmall : S ≤ min ((p ⟨j,hjk⟩-1 : ℕ) : ℝ) ((q ⟨j,hjl⟩-1 : ℕ) : ℝ)) :
    |B (largestPrimeFactor (p ⟨j,hjk⟩-1))/B z-
      B (largestPrimeFactor (q ⟨j,hjl⟩-1))/B z| ≤
      (2*(j : ℝ)+1)*Real.sqrt (B S/B z)+Real.log (3*B z)/B z := by
  have hBSz : B S ≤ B z := Real.log_le_log (Real.log_pos hS)
    (Real.log_le_log (zero_lt_one.trans hS) hSz)
  have hpred (r : ℕ) (hr : 3 ≤ r) (hrz : (r-1 : ℕ) ≤ z) : B (r-1 : ℕ) ≤ B z := by
    have hr1 : (1 : ℝ) < (r-1 : ℕ) := by exact_mod_cast (show 1 < r-1 by omega)
    exact Real.log_le_log (Real.log_pos hr1)
      (Real.log_le_log (zero_lt_one.trans hr1) hrz)
  have hlarge (r : ℕ) (hr : 3 ≤ r) (hrz : (r-1 : ℕ) ≤ z) :
      B (largestPrimeFactor (r-1)) ≤ B z := by
    have hl1 : (1 : ℝ) < largestPrimeFactor (r-1) := by
      exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ r-1 by omega)
    apply Real.log_le_log (Real.log_pos hl1)
    apply Real.log_le_log (zero_lt_one.trans hl1)
    exact (Nat.cast_le.mpr (largestPrimeFactor_le_self (by omega))).trans hrz
  have hΩp := normality_total_uniform (hp ⟨j,hjk⟩) hS hBS hBSz (hpred _ hp3 hpz)
  have hΩq := normality_total_uniform (hq ⟨j,hjl⟩) hS hBS hBSz (hpred _ hq3 hqz)
  have hεp := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hlarge _ hp3 hpz) hBS)
  have hεq := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hlarge _ hq3 hqz) hBS)
  have hraw := ppt_ordered_coordinate_alignment p q hjk hjl hS hBS
    (show 0 < 3*B z by positivity) hD hE hp hq hpa hqa heq hp3 hq3
    hDS hES hSsmall hΩp hΩq hεp hεq
  have hsqrt : Real.sqrt (B S*B z)/B z = Real.sqrt (B S/B z) := by
    calc
      _ = Real.sqrt (B S)*(Real.sqrt (B z)/B z) := by
        rw [Real.sqrt_mul hBS]
        ring
      _ = Real.sqrt (B S)*(Real.sqrt (B z))⁻¹ := by rw [Real.sqrt_div_self]
      _ = _ := by rw [Real.sqrt_div hBS, div_eq_mul_inv]
  calc
    _ = |B (largestPrimeFactor (p ⟨j,hjk⟩-1))-
        B (largestPrimeFactor (q ⟨j,hjl⟩-1))|/B z := by
      rw [← sub_div, abs_div, abs_of_pos hBz]
    _ ≤ ((2*(j : ℝ)+1)*Real.sqrt (B S*B z)+Real.log (3*B z))/B z :=
      div_le_div_of_nonneg_right hraw hBz.le
    _ = _ := by rw [add_div, mul_div_assoc, hsqrt]

end TotientAsymptotic

end

end OAI
