import OAI.Analysis.KadisonKastler.WordBounds

namespace OAI

/-!
# Numerical constants for the free projection-word estimates

These are the scalar closing estimates in §3. The norm bounds for the
individual operator cuts enter as explicit hypotheses; no free-word
operator estimate is assumed as a published theorem.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

def freeWordH (r : ℕ) : ℝ :=
  1 + ∑ l ∈ Ico 1 r, (r.choose l : ℝ) * (2 * l + 1)

def freeWordJ (r : ℕ) : ℝ :=
  (r + 1 : ℝ) * Real.sqrt (r.factorial : ℝ) + (r.factorial : ℝ) * freeWordH r

def freeWordC (r : ℕ) : ℝ :=
  (r.factorial : ℝ) * (2 * r + 1 + freeWordH r)

theorem one_le_freeWordH (r : ℕ) : 1 ≤ freeWordH r := by
  have hs : 0 ≤ ∑ l ∈ Ico 1 r, (r.choose l : ℝ) * (2 * l + 1) :=
    sum_nonneg (fun _ _ => by positivity)
  unfold freeWordH
  linarith

theorem freeWordJ_nonneg (r : ℕ) : 0 ≤ freeWordJ r := by
  have hH := one_le_freeWordH r
  unfold freeWordJ
  positivity

theorem freeWordC_pos (r : ℕ) : 0 < freeWordC r := by
  have hH := one_le_freeWordH r
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  unfold freeWordC
  positivity

theorem sqrt_pow_succ_split {d : ℝ} (hd : 0 ≤ d) {r : ℕ} (hr : 1 ≤ r) :
    Real.sqrt (d ^ r) = Real.sqrt (d ^ (r - 1)) * Real.sqrt d := by
  conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
  exact Real.sqrt_mul (pow_nonneg hd _) d

theorem sqrt_pow_mono {d : ℝ} (hd : 1 ≤ d) {l r : ℕ} (hlr : l ≤ r) :
    Real.sqrt (d ^ l) ≤ Real.sqrt (d ^ r) :=
  Real.sqrt_le_sqrt (pow_le_pow_right₀ hd hlr)

/-- The bound for one centered word, after absorbing the cuts without
preservation into the common denominator. -/
theorem single_centered_word_constant {d : ℝ} (hd : 1 ≤ d) (l : ℕ) {B : ℝ}
    (hB : B ≤ (l : ℝ) / Real.sqrt (d ^ (l - 1)) +
      (l + 1 : ℝ) / Real.sqrt (d ^ l)) :
    B ≤ (2 * l + 1 : ℝ) / Real.sqrt (d ^ (l - 1)) := by
  have hp : 0 < Real.sqrt (d ^ (l - 1)) := Real.sqrt_pos.mpr (pow_pos (by linarith) _)
  have hden := sqrt_pow_mono hd (Nat.sub_le l 1)
  have ht : (l + 1 : ℝ) / Real.sqrt (d ^ l) ≤
      (l + 1 : ℝ) / Real.sqrt (d ^ (l - 1)) :=
    div_le_div_of_nonneg_left (by positivity) hp hden
  calc
    B ≤ (l : ℝ) / Real.sqrt (d ^ (l - 1)) +
        (l + 1 : ℝ) / Real.sqrt (d ^ (l - 1)) := hB.trans (add_le_add le_rfl ht)
    _ = _ := by ring

/-- Removing at least one centered letter supplies the extra inverse
square root needed by the scalar-restoration estimate. -/
theorem restored_scalar_denominator {d : ℝ} (hd : 1 ≤ d) {l r : ℕ}
    (hl : 1 ≤ l) (hlr : l < r) :
    Real.sqrt (d ^ r) ≤ d ^ (r - l) * Real.sqrt (d ^ (l - 1)) := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (pow_nonneg (by linarith) _),
    Real.sq_sqrt (pow_nonneg (by linarith) _), ← pow_mul, ← pow_add]
  apply pow_le_pow_right₀ hd
  omega

theorem restored_scalar_term {d : ℝ} (hd : 1 ≤ d) {l r : ℕ}
    (hl : 1 ≤ l) (hlr : l < r) :
    (2 * l + 1 : ℝ) / (d ^ (r - l) * Real.sqrt (d ^ (l - 1))) ≤
      (2 * l + 1 : ℝ) / Real.sqrt (d ^ r) := by
  apply div_le_div_of_nonneg_left (by positivity)
    (Real.sqrt_pos.mpr (pow_pos (by linarith) _))
  exact restored_scalar_denominator hd hl hlr

def scalarRestorationBound (r : ℕ) (d : ℝ) : ℝ :=
  (r.factorial : ℝ) * (1 / d ^ r +
    ∑ l ∈ Ico 1 r, (r.choose l : ℝ) *
      ((2 * l + 1 : ℝ) / (d ^ (r - l) * Real.sqrt (d ^ (l - 1)))))

/-- Summing all proper centered subwords gives precisely the manuscript's
constant `r! H_r`, including the entirely scalar term. -/
theorem scalarRestorationBound_le {d : ℝ} (hd : 1 ≤ d) (r : ℕ) :
    scalarRestorationBound r d ≤ (r.factorial : ℝ) * freeWordH r / Real.sqrt (d ^ r) := by
  have hdp : 0 < d ^ r := pow_pos (by linarith) _
  have hsqrt : Real.sqrt (d ^ r) ≤ d ^ r := by
    apply (Real.sqrt_le_iff).mpr
    have hpow : 1 ≤ d ^ r := one_le_pow₀ hd
    exact ⟨hdp.le, by nlinarith⟩
  have hscalar : 1 / d ^ r ≤ 1 / Real.sqrt (d ^ r) :=
    div_le_div_of_nonneg_left zero_le_one (Real.sqrt_pos.mpr hdp) hsqrt
  have hsum : (∑ l ∈ Ico 1 r, (r.choose l : ℝ) *
      ((2 * l + 1 : ℝ) / (d ^ (r - l) * Real.sqrt (d ^ (l - 1))))) ≤
      ∑ l ∈ Ico 1 r, (r.choose l : ℝ) * ((2 * l + 1 : ℝ) / Real.sqrt (d ^ r)) := by
    apply sum_le_sum
    intro l hl
    exact mul_le_mul_of_nonneg_left
      (restored_scalar_term hd (mem_Ico.mp hl).1 (mem_Ico.mp hl).2) (Nat.cast_nonneg _)
  unfold scalarRestorationBound
  calc
    _ ≤ (r.factorial : ℝ) * (1 / Real.sqrt (d ^ r) +
        ∑ l ∈ Ico 1 r, (r.choose l : ℝ) * ((2 * l + 1 : ℝ) / Real.sqrt (d ^ r))) :=
      mul_le_mul_of_nonneg_left (add_le_add hscalar hsum) (Nat.cast_nonneg _)
    _ = _ := by
      unfold freeWordH
      simp_rw [← mul_div_assoc]
      rw [← sum_div, ← add_div]
      ring

/-- The term containing `J_r` fits into one copy of the target scale. -/
theorem freeWordJ_remainder_le {d : ℝ} (hd : 1 ≤ d) {r : ℕ} (hr : 1 ≤ r)
    (hJ : freeWordJ r ^ 2 ≤ ((r - 1).factorial : ℝ) * d) :
    freeWordJ r / Real.sqrt (d ^ r) ≤
      Real.sqrt ((r - 1).factorial : ℝ) / Real.sqrt (d ^ (r - 1)) := by
  have hdpos : 0 < d := by linarith
  have hroot : freeWordJ r ≤ Real.sqrt ((r - 1).factorial : ℝ) * Real.sqrt d := by
    apply (sq_le_sq₀ (freeWordJ_nonneg r) (by positivity)).mp
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hdpos.le] using hJ
  rw [sqrt_pow_succ_split hdpos.le hr]
  calc
    _ ≤ (Real.sqrt ((r - 1).factorial : ℝ) * Real.sqrt d) /
        (Real.sqrt (d ^ (r - 1)) * Real.sqrt d) :=
      div_le_div_of_nonneg_right hroot (by positivity)
    _ = _ := by
      have hds : Real.sqrt d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdpos)
      have hdp : Real.sqrt (d ^ (r - 1)) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr (pow_pos hdpos _))
      field_simp

/-- The preservation cuts contribute at most six target units; the
nonpreservation cuts and scalar restoration contribute at most one. -/
theorem distinct_freeWord_constant {d : ℝ} (hd : 1 ≤ d) {r : ℕ} (hr : 1 ≤ r)
    (hrd : 5 * (r : ℝ) ≤ d)
    (hJ : freeWordJ r ^ 2 ≤ ((r - 1).factorial : ℝ) * d)
    {P N R B : ℝ}
    (hP : P ≤ (1 + r / d) *
      (Real.sqrt ((r - 1).factorial : ℝ) / Real.sqrt (d ^ (r - 1))) *
      (∑ p ∈ range r, 1 / Real.sqrt ((r - 1).choose p : ℝ)))
    (hN : N ≤ (r + 1 : ℝ) * Real.sqrt (r.factorial : ℝ) / Real.sqrt (d ^ r))
    (hR : R ≤ (r.factorial : ℝ) * freeWordH r / Real.sqrt (d ^ r))
    (hB : B ≤ P + N + R) :
    B ≤ 7 * Real.sqrt ((r - 1).factorial : ℝ) / Real.sqrt (d ^ (r - 1)) := by
  let b := Real.sqrt ((r - 1).factorial : ℝ) / Real.sqrt (d ^ (r - 1))
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hdpos : 0 < d := by linarith
  have hsum : (∑ p ∈ range r, 1 / Real.sqrt ((r - 1).choose p : ℝ)) ≤ 5 := by
    simpa only [Nat.sub_add_cancel hr] using sum_inv_sqrt_choose_le_five (r - 1)
  have hP' : P ≤ 6 * b := by
    have hratio : 5 * (1 + (r : ℝ) / d) ≤ 6 := by
      have hh : (5 * (r : ℝ)) / d ≤ 1 := (div_le_one hdpos).mpr hrd
      rw [mul_div_assoc] at hh
      linarith
    calc
      P ≤ (1 + r / d) * b * 5 :=
        hP.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
      _ = (5 * (1 + r / d)) * b := by ring
      _ ≤ 6 * b := mul_le_mul_of_nonneg_right hratio hb
  have hNR : N + R ≤ b := by
    calc
      N + R ≤ ((r + 1 : ℝ) * Real.sqrt (r.factorial : ℝ) +
          (r.factorial : ℝ) * freeWordH r) / Real.sqrt (d ^ r) := by
        simpa only [add_div] using add_le_add hN hR
      _ ≤ b := freeWordJ_remainder_le hd hr hJ
  calc
    B ≤ 7 * b := by linarith
    _ = _ := by dsimp [b]; ring

/-- Repeated-label words use the single-word estimate for each of at
most `r!` summands; their constant is independent of the matrix size. -/
theorem repeated_freeWord_constant {d : ℝ} (hd : 1 ≤ d) (r : ℕ) {P R B : ℝ}
    (hP : P ≤ (r.factorial : ℝ) * (2 * r + 1 : ℝ) / Real.sqrt (d ^ (r - 1)))
    (hR : R ≤ (r.factorial : ℝ) * freeWordH r / Real.sqrt (d ^ r))
    (hB : B ≤ P + R) : B ≤ freeWordC r / Real.sqrt (d ^ (r - 1)) := by
  have hR' : R ≤ (r.factorial : ℝ) * freeWordH r / Real.sqrt (d ^ (r - 1)) := by
    apply hR.trans
    apply div_le_div_of_nonneg_left
      (mul_nonneg (Nat.cast_nonneg _) ((one_le_freeWordH r).trans' zero_le_one))
      (Real.sqrt_pos.mpr (pow_pos (by linarith) _))
    exact sqrt_pow_mono hd (Nat.sub_le r 1)
  calc
    B ≤ (r.factorial : ℝ) * (2 * r + 1 : ℝ) / Real.sqrt (d ^ (r - 1)) +
        (r.factorial : ℝ) * freeWordH r / Real.sqrt (d ^ (r - 1)) :=
      hB.trans (add_le_add hP hR')
    _ = _ := by unfold freeWordC; ring

/-- A convenient integral threshold, larger than the one displayed in
the manuscript, that keeps the distinct-label constant equal to seven. -/
def freeWordThreshold (r : ℕ) : ℕ := ⌈5 * (r : ℝ) + freeWordJ r ^ 2 + 1⌉₊

theorem freeWordThreshold_conditions {r d : ℕ} (h : freeWordThreshold r ≤ d) :
    (1 : ℝ) ≤ d ∧ 5 * (r : ℝ) ≤ d ∧
      freeWordJ r ^ 2 ≤ ((r - 1).factorial : ℝ) * d := by
  have hc0 : 5 * (r : ℝ) + freeWordJ r ^ 2 + 1 ≤ (freeWordThreshold r : ℝ) :=
    Nat.le_ceil _
  have hcd : (freeWordThreshold r : ℝ) ≤ d := by exact_mod_cast h
  have hc := hc0.trans hcd
  have hfac : (1 : ℝ) ≤ (r - 1).factorial := by
    exact_mod_cast Nat.factorial_pos (r - 1)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hd : (1 : ℝ) ≤ d := by nlinarith [sq_nonneg (freeWordJ r)]
  refine ⟨hd, by nlinarith [sq_nonneg (freeWordJ r)], ?_⟩
  have hJd : freeWordJ r ^ 2 ≤ d := by nlinarith
  exact hJd.trans (by nlinarith)

/-- The complete scalar closing step, starting from the three cut
estimates and the explicit integer threshold. -/
theorem distinct_freeWord_constant_of_threshold {r d : ℕ} (hr : 1 ≤ r)
    (hd : freeWordThreshold r ≤ d) {P N R B : ℝ}
    (hP : P ≤ (1 + (r : ℝ) / d) *
      (Real.sqrt ((r - 1).factorial : ℝ) / Real.sqrt ((d : ℝ) ^ (r - 1))) *
      (∑ p ∈ range r, 1 / Real.sqrt ((r - 1).choose p : ℝ)))
    (hN : N ≤ (r + 1 : ℝ) * Real.sqrt (r.factorial : ℝ) / Real.sqrt ((d : ℝ) ^ r))
    (hR : R ≤ scalarRestorationBound r d) (hB : B ≤ P + N + R) :
    B ≤ 7 * Real.sqrt ((r - 1).factorial : ℝ) / Real.sqrt ((d : ℝ) ^ (r - 1)) := by
  obtain ⟨hd1, hdr, hdJ⟩ := freeWordThreshold_conditions hd
  exact distinct_freeWord_constant hd1 hr hdr hdJ hP hN
    (hR.trans (scalarRestorationBound_le hd1 r)) hB

theorem exists_uniform_freeWordThreshold (N : ℕ) :
    ∃ D : ℕ, 0 < D ∧ ∀ r ≤ N, freeWordThreshold r ≤ D := by
  refine ⟨(∑ r ∈ range (N + 1), freeWordThreshold r) + 1, by omega, ?_⟩
  intro r hr
  have ht : freeWordThreshold r ≤ ∑ s ∈ range (N + 1), freeWordThreshold s :=
    single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr (by omega))
  exact ht.trans (by omega)

end

end KadisonKastler

end OAI
