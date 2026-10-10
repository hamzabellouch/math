import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

section

/-!
Finite threshold-overlap estimates used in the Dinur--Steurer argument.
These statements are numerical inequalities, not parallel-repetition premises.
The Boolean gate keeps the constraint predicate inside the overlap energy.
Weights need not be normalized: a finite auxiliary measure is permitted.
-/

namespace UniqueGamesTheorem.Repetition.Analytic

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

def quadraticMass (w f g : ι → ℝ) : ℝ :=
  ∑ i, w i * ((f i) ^ 2 + (g i) ^ 2) / 2

def gatedCorrelation (w f g : ι → ℝ) (gate : ι → Bool) : ℝ :=
  ∑ i, if gate i then w i * f i * g i else 0

def gatedMinimum (w f g : ι → ℝ) (gate : ι → Bool) : ℝ :=
  ∑ i, if gate i then w i * min ((f i) ^ 2) ((g i) ^ 2) else 0

def gatedMaximum (w f g : ι → ℝ) (gate : ι → Bool) : ℝ :=
  ∑ i, if gate i then w i * max ((f i) ^ 2) ((g i) ^ 2) else 0

theorem quadraticMass_nonnegative (w f g : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ quadraticMass w f g := by
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (mul_nonneg (hw i) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    (by norm_num)

theorem gatedCorrelation_nonnegative (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    0 ≤ gatedCorrelation w f g gate := by
  apply Finset.sum_nonneg
  intro i _
  split
  · exact mul_nonneg (mul_nonneg (hw i) (hf i)) (hg i)
  · exact le_rfl

theorem gatedCorrelation_le_mass (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) : gatedCorrelation w f g gate ≤ quadraticMass w f g := by
  apply Finset.sum_le_sum
  intro i _
  split
  · have hfg : f i * g i ≤ ((f i) ^ 2 + (g i) ^ 2) / 2 := by
      nlinarith [sq_nonneg (f i - g i)]
    simpa only [← mul_assoc, mul_div_assoc] using mul_le_mul_of_nonneg_left hfg (hw i)
  · exact div_nonneg (mul_nonneg (hw i) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (by norm_num)

theorem gatedMinimum_nonnegative (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ gatedMinimum w f g gate := by
  apply Finset.sum_nonneg
  intro i _
  split
  · exact mul_nonneg (hw i) (le_min (sq_nonneg _) (sq_nonneg _))
  · exact le_rfl

theorem gatedMinimum_le_mass (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) : gatedMinimum w f g gate ≤ quadraticMass w f g := by
  apply Finset.sum_le_sum
  intro i _
  split
  · have hmin : min ((f i) ^ 2) ((g i) ^ 2) ≤ ((f i) ^ 2 + (g i) ^ 2) / 2 := by
      have h₁ := min_le_left ((f i) ^ 2) ((g i) ^ 2)
      have h₂ := min_le_right ((f i) ^ 2) ((g i) ^ 2)
      linarith
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hmin (hw i)
  · exact div_nonneg (mul_nonneg (hw i) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (by norm_num)

theorem gatedMinimum_add_maximum_le (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    gatedMinimum w f g gate + gatedMaximum w f g gate ≤ 2 * quadraticMass w f g := by
  unfold gatedMinimum gatedMaximum quadraticMass
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : gate i = true
  · simp only [hi, ↓reduceIte]
    have h := min_add_max ((f i) ^ 2) ((g i) ^ 2)
    rw [← mul_add, h]
    ring_nf
    exact le_rfl
  · simp only [hi, Bool.false_eq_true, ↓reduceIte, zero_add]
    have := hw i
    positivity

/-- A gated finite Cauchy--Schwarz estimate. This is the algebraic heart of
the threshold-rounding inequality, with no independence assumption. -/
theorem gatedCorrelation_sq_le_min_mul_max (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    gatedCorrelation w f g gate ^ 2 ≤
      gatedMinimum w f g gate * gatedMaximum w f g gate := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _
    split
    · exact mul_nonneg (hw i) (le_min (sq_nonneg _) (sq_nonneg _))
    · exact le_rfl
  · intro i _
    split
    · exact mul_nonneg (hw i) ((sq_nonneg (f i)).trans (le_max_left _ _))
    · exact le_rfl
  · intro i _
    by_cases hi : gate i = true
    · simp only [hi, ↓reduceIte]
      rcases le_total ((f i) ^ 2) ((g i) ^ 2) with h | h
      · rw [min_eq_left h, max_eq_right h]
        ring_nf
        exact le_rfl
      · rw [min_eq_right h, max_eq_left h]
        ring_nf
        exact le_rfl
    · simp [hi]

theorem gatedCorrelation_sq_le_min_quadratic (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    gatedCorrelation w f g gate ^ 2 ≤
      gatedMinimum w f g gate *
        (2 * quadraticMass w f g - gatedMinimum w f g gate) := by
  have hmax := gatedMinimum_add_maximum_le w f g gate hw
  have hmin := gatedMinimum_nonnegative w f g gate hw
  exact (gatedCorrelation_sq_le_min_mul_max w f g gate hw).trans
    (mul_le_mul_of_nonneg_left (by linarith) hmin)

/-- Sharp homogeneous Cheeger form. The expression under the square root
is nonnegative by the preceding proved inequality. -/
theorem gatedMinimum_cheeger (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    quadraticMass w f g -
        Real.sqrt (quadraticMass w f g ^ 2 - gatedCorrelation w f g gate ^ 2) ≤
      gatedMinimum w f g gate := by
  have h := gatedCorrelation_sq_le_min_quadratic w f g gate hw
  have hsq : (quadraticMass w f g - gatedMinimum w f g gate) ^ 2 ≤
      quadraticMass w f g ^ 2 - gatedCorrelation w f g gate ^ 2 := by
    nlinarith
  have hsqrt := Real.le_sqrt_of_sq_le hsq
  linarith

/-- The near-perfect form suffices for alphabet-independent repetition.
The total squared mass may be at most one, rather than exactly one. -/
theorem gatedMinimum_near_one (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) {η : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hmass : quadraticMass w f g ≤ 1)
    (hcorrelation : 1 - η ≤ gatedCorrelation w f g gate) :
    1 - Real.sqrt (2 * η) ≤ gatedMinimum w f g gate := by
  have hmin := gatedMinimum_nonnegative w f g gate hw
  have h := gatedCorrelation_sq_le_min_quadratic w f g gate hw
  have hcorr : 0 ≤ gatedCorrelation w f g gate := by linarith
  have hsqcorr : (1 - η) ^ 2 ≤ gatedCorrelation w f g gate ^ 2 := by
    nlinarith
  have hupper : gatedMinimum w f g gate *
      (2 * quadraticMass w f g - gatedMinimum w f g gate) ≤
      gatedMinimum w f g gate * (2 - gatedMinimum w f g gate) := by
    apply mul_le_mul_of_nonneg_left _ hmin
    linarith
  have hsq : (1 - gatedMinimum w f g gate) ^ 2 ≤ 2 * η := by
    nlinarith [sq_nonneg η]
  have hsqrt := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hη)
  nlinarith [Real.sqrt_nonneg (2 * η)]

/-- Unit-mass form for the joint question-pair and auxiliary-coordinate law. -/
theorem gatedMinimum_unit_mass (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hmass : quadraticMass w f g = 1) :
    1 - Real.sqrt (2 * (1 - gatedCorrelation w f g gate)) ≤
      gatedMinimum w f g gate := by
  have hc₀ := gatedCorrelation_nonnegative w f g gate hw hf hg
  have hc₁ := gatedCorrelation_le_mass w f g gate hw
  rw [hmass] at hc₁
  apply gatedMinimum_near_one w f g gate hw
  · linarith
  · linarith
  · exact hmass.le
  · linarith

end
end UniqueGamesTheorem.Repetition.Analytic

end

section

/-!
Scalar parameter selection for the v2 repetition rate.

These results concern powers of real numbers only. In particular, they do not
assert a parallel-repetition theorem for games. The exponent depends only on
the gap and the desired error; no alphabet or logical dimension occurs here.
-/

namespace UniqueGamesTheorem.Repetition

/-- The scalar rate appearing in the alphabet-independent repetition estimate. -/
noncomputable def dsRate (gap : ℝ) : ℝ := 1 - gap ^ 2 / 16

theorem dsRate_nonneg {gap : ℝ} (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1) :
    0 ≤ dsRate gap := by
  dsimp [dsRate]
  nlinarith

theorem dsRate_lt_one {gap : ℝ} (hgap : 0 < gap) : dsRate gap < 1 := by
  dsimp [dsRate]
  nlinarith [sq_pos_of_pos hgap]

/-- A scalar contraction admits a strictly positive exponent for every positive
target error. This lemma makes no assertion about any game value. -/
theorem exists_positive_power_lt {rate error : ℝ}
    (hrate₀ : 0 ≤ rate) (hrate₁ : rate < 1) (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ rate ^ n < error := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hrate₀ hrate₁
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds herror)).exists
  refine ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), ?_⟩
  calc
    rate ^ (n + 1) = rate ^ n * rate := pow_succ _ _
    _ ≤ rate ^ n := mul_le_of_le_one_right (pow_nonneg hrate₀ n) hrate₁.le
    _ < error := hn

/-- Select the repetition count before choosing any alphabet. -/
theorem exists_dsRate_pow_le {gap error : ℝ}
    (hgap₀ : 0 < gap) (hgap₁ : gap < 1) (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ dsRate gap ^ n ≤ error := by
  obtain ⟨n, hn, hbound⟩ := exists_positive_power_lt
    (dsRate_nonneg hgap₀.le hgap₁.le) (dsRate_lt_one hgap₀) herror
  exact ⟨n, hn, hbound.le⟩

theorem dsRate_one_div_eight_hundred :
    dsRate (1 / 800) = 1 - (1 : ℝ) / 10240000 := by
  norm_num [dsRate]

theorem dsRate_one_div_fifteen :
    dsRate (1 / 15) = 1 - (1 : ℝ) / 3600 := by
  norm_num [dsRate]

/-- The final soundness exponent depends only on `error`, even when the later
construction chooses its alphabet after this exponent. -/
theorem exists_final_repetition_count {error : ℝ} (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ (1 - (1 : ℝ) / 10240000) ^ n ≤ error := by
  simpa only [dsRate_one_div_eight_hundred] using
    exists_dsRate_pow_le (gap := (1 / 800 : ℝ)) (by norm_num) (by norm_num) herror

/-- The preliminary constant-gap specialization of the same scalar rate. -/
theorem exists_preliminary_repetition_count {error : ℝ} (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ (1 - (1 : ℝ) / 3600) ^ n ≤ error := by
  simpa only [dsRate_one_div_fifteen] using
    exists_dsRate_pow_le (gap := (1 / 15 : ℝ)) (by norm_num) (by norm_num) herror

end UniqueGamesTheorem.Repetition

end

end OAI
