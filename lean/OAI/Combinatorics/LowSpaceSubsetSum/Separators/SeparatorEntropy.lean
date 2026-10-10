import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Entropy
import Mathlib.Analysis.Convex.Deriv

namespace OAI

/-!
# The sharp separator entropy estimate

This is the exact estimate `sep:sharp` in the manuscript. No positive
exponential error is inserted: the maximum is exactly `1 - h(1/4)`.
We use its natural-log expansion and an algebraic certificate for the
sign of the second derivative.
-/

namespace LowSpaceSubsetSum

noncomputable def separatorAlpha : ℝ := Real.logb 2 3

def separatorX (k : ℝ) : ℝ := 1 - k

noncomputable def separatorY (k : ℝ) : ℝ :=
  1 / 4 + (separatorAlpha - 1) * (k - 1 / 4)

noncomputable def separatorZ (k : ℝ) : ℝ :=
  (2 + separatorAlpha) / 4 - separatorAlpha * k

noncomputable def separatorW (k : ℝ) : ℝ :=
  separatorAlpha / 4 - (separatorAlpha - 1) * k

noncomputable def separatorEntropy (k : ℝ) : ℝ :=
  separatorX k * binaryEntropy (separatorY k / separatorX k) -
    (1 / 2) * binaryEntropy (2 * separatorY k)

noncomputable def separatorLogEntropy (k : ℝ) : ℝ :=
  separatorX k * Real.log (separatorX k) -
    separatorZ k * Real.log (separatorZ k) -
    (1 / 2) * Real.log (1 / 2) + separatorW k * Real.log (separatorW k)

private noncomputable def separatorLogDeriv (k : ℝ) : ℝ :=
  -Real.log (separatorX k) + separatorAlpha * Real.log (separatorZ k) -
    (separatorAlpha - 1) * Real.log (separatorW k)

private noncomputable def separatorLogDeriv2 (k : ℝ) : ℝ :=
  1 / separatorX k - separatorAlpha ^ 2 / separatorZ k +
    (separatorAlpha - 1) ^ 2 / separatorW k

theorem separatorAlpha_bounds : 1 < separatorAlpha ∧ separatorAlpha < 2 := by
  constructor
  · have h := Real.logb_lt_logb (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
      (by norm_num : 0 < (2 : ℝ)) (by norm_num : (2 : ℝ) < 3)
    simpa only [separatorAlpha, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h
  · have h := Real.logb_lt_logb (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
      (by norm_num : 0 < (3 : ℝ)) (by norm_num : (3 : ℝ) < 2 ^ 2)
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
    norm_num at h
    exact h

theorem separatorZ_eq (k : ℝ) : separatorZ k = separatorX k - separatorY k := by
  unfold separatorZ separatorX separatorY
  ring

theorem separatorW_eq (k : ℝ) : separatorW k = 1 / 2 - separatorY k := by
  unfold separatorW separatorY
  ring

private theorem separator_positive {k : ℝ} (hk : k ∈ Set.Icc (1 / 6) (1 / 3)) :
    0 < separatorX k ∧ 0 < separatorY k ∧ 0 < separatorZ k ∧ 0 < separatorW k := by
  obtain ⟨ha1, ha2⟩ := separatorAlpha_bounds
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have hprod := mul_le_mul_of_nonneg_left hk.2 (show 0 ≤ separatorAlpha by linarith)
  have hprod' := mul_le_mul_of_nonneg_left hk.2 (show 0 ≤ separatorAlpha - 1 by linarith)
  have hprod0 := mul_nonneg (show 0 ≤ separatorAlpha - 1 by linarith) hk0
  have hy : separatorY k = (2 - separatorAlpha) / 4 + (separatorAlpha - 1) * k := by
    unfold separatorY
    ring
  unfold separatorX separatorZ separatorW
  rw [hy]
  constructor
  · linarith [hk.2]
  constructor
  · linarith
  constructor <;> linarith

private theorem hasDerivAt_separatorX (k : ℝ) : HasDerivAt separatorX (-1) k := by
  convert! (hasDerivAt_id k).const_sub 1 using 1

private theorem hasDerivAt_separatorZ (k : ℝ) : HasDerivAt separatorZ (-separatorAlpha) k := by
  convert! ((hasDerivAt_id k).const_mul separatorAlpha).const_sub
    ((2 + separatorAlpha) / 4) using 1
  simp

private theorem hasDerivAt_separatorW (k : ℝ) :
    HasDerivAt separatorW (-(separatorAlpha - 1)) k := by
  convert! ((hasDerivAt_id k).const_mul (separatorAlpha - 1)).const_sub
    (separatorAlpha / 4) using 1
  simp

private theorem hasDerivAt_separatorLogEntropy {k : ℝ}
    (hk : k ∈ Set.Icc (1 / 6) (1 / 3)) :
    HasDerivAt separatorLogEntropy (separatorLogDeriv k) k := by
  obtain ⟨hx, _, hz, hw⟩ := separator_positive hk
  have hX := (Real.hasDerivAt_mul_log (ne_of_gt hx)).comp k (hasDerivAt_separatorX k)
  have hZ := (Real.hasDerivAt_mul_log (ne_of_gt hz)).comp k (hasDerivAt_separatorZ k)
  have hW := (Real.hasDerivAt_mul_log (ne_of_gt hw)).comp k (hasDerivAt_separatorW k)
  convert ((hX.sub hZ).sub_const ((1 / 2) * Real.log (1 / 2))).add hW using 1
  · rfl
  · unfold separatorLogDeriv
    ring

private theorem hasDerivAt_separatorLogDeriv {k : ℝ}
    (hk : k ∈ Set.Icc (1 / 6) (1 / 3)) :
    HasDerivAt separatorLogDeriv (separatorLogDeriv2 k) k := by
  obtain ⟨hx, _, hz, hw⟩ := separator_positive hk
  have hX := (hasDerivAt_separatorX k).log (ne_of_gt hx)
  have hZ := (hasDerivAt_separatorZ k).log (ne_of_gt hz)
  have hW := (hasDerivAt_separatorW k).log (ne_of_gt hw)
  convert (hX.neg.add (hZ.const_mul separatorAlpha)).sub
    (hW.const_mul (separatorAlpha - 1)) using 1
  · rfl
  · unfold separatorLogDeriv2
    ring

/-- An exact factorization certifies the sign without any numerical slack. -/
private theorem separatorLogDeriv2_neg {k : ℝ}
    (hk : k ∈ Set.Icc (1 / 6) (1 / 3)) : separatorLogDeriv2 k < 0 := by
  obtain ⟨ha1, ha2⟩ := separatorAlpha_bounds
  obtain ⟨hx, _, hz, hw⟩ := separator_positive hk
  have hterm1 : 8 * separatorAlpha * (separatorAlpha - 1) * (k - 1 / 2) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · positivity
    · linarith [hk.2]
  have hterm2 : (separatorAlpha - 2) * (5 * separatorAlpha - 4) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by linarith)
  have hfactor : separatorLogDeriv2 k =
      (8 * separatorAlpha * (separatorAlpha - 1) * (k - 1 / 2) +
        (separatorAlpha - 2) * (5 * separatorAlpha - 4)) /
      (16 * separatorX k * separatorZ k * separatorW k) := by
    unfold separatorLogDeriv2
    field_simp [ne_of_gt hx, ne_of_gt hz, ne_of_gt hw]
    unfold separatorX separatorZ separatorW
    ring
  rw [hfactor]
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

theorem separatorLogEntropy_concaveOn :
    ConcaveOn ℝ (Set.Icc (1 / 6) (1 / 3)) separatorLogEntropy := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (f' := separatorLogDeriv) (f'' := separatorLogDeriv2)
  · have hcontinuous : Continuous separatorLogEntropy := by
      unfold separatorLogEntropy separatorX separatorZ separatorW
      fun_prop
    exact hcontinuous.continuousOn
  · intro k hk
    exact (hasDerivAt_separatorLogEntropy (interior_subset hk)).hasDerivWithinAt
  · intro k hk
    exact (hasDerivAt_separatorLogDeriv (interior_subset hk)).hasDerivWithinAt
  · intro k hk
    exact (separatorLogDeriv2_neg (interior_subset hk)).le

private theorem separatorLogDeriv_quarter : separatorLogDeriv (1 / 4) = 0 := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  have hX : separatorX (1 / 4) = 3 / 4 := by norm_num [separatorX]
  have hZ : separatorZ (1 / 4) = 1 / 2 := by unfold separatorZ; ring
  have hW : separatorW (1 / 4) = 1 / 4 := by unfold separatorW; ring
  unfold separatorLogDeriv
  rw [hX, hZ, hW, Real.log_div (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), Real.log_one, hlog4]
  unfold separatorAlpha Real.logb
  field_simp [hlog2]
  ring

theorem separatorLogEntropy_le_quarter {k : ℝ}
    (hk : k ∈ Set.Icc (1 / 6) (1 / 3)) :
    separatorLogEntropy k ≤ separatorLogEntropy (1 / 4) := by
  have hq : (1 / 4 : ℝ) ∈ Set.Icc (1 / 6) (1 / 3) := by norm_num
  have hd : HasDerivAt separatorLogEntropy 0 (1 / 4) := by
    simpa only [separatorLogDeriv_quarter] using hasDerivAt_separatorLogEntropy hq
  rcases lt_trichotomy k (1 / 4) with hlt | rfl | hgt
  · exact (slope_nonneg_iff_of_le hlt.le).mp
      (separatorLogEntropy_concaveOn.le_slope_of_hasDerivAt hk hq hlt hd)
  · exact le_rfl
  · exact (slope_nonpos_iff_of_le hgt.le).mp
      (separatorLogEntropy_concaveOn.slope_le_of_hasDerivAt hq hk hgt hd)

private theorem binEntropy_perspective {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hyx : y < x) :
    x * Real.binEntropy (y / x) =
      x * Real.log x - y * Real.log y - (x - y) * Real.log (x - y) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hsub : 1 - y / x = (x - y) / x := by field_simp
  unfold Real.binEntropy
  rw [Real.log_inv, Real.log_inv, hsub,
    Real.log_div (ne_of_gt hy) hx0, Real.log_div (ne_of_gt (sub_pos.mpr hyx)) hx0]
  field_simp
  ring

theorem separatorEntropy_eq_logEntropy {k : ℝ}
    (hk : k ∈ Set.Icc (1 / 6) (1 / 3)) :
    separatorEntropy k = separatorLogEntropy k / Real.log 2 := by
  obtain ⟨hx, hy, hz, hw⟩ := separator_positive hk
  have hyx : separatorY k < separatorX k := by linarith [separatorZ_eq k]
  have hyh : separatorY k < 1 / 2 := by linarith [separatorW_eq k]
  have h1 := binEntropy_perspective hx hy hyx
  have h2 := binEntropy_perspective (by norm_num : (0 : ℝ) < 1 / 2) hy hyh
  have hdiv : separatorY k / (1 / 2) = 2 * separatorY k := by ring
  rw [hdiv] at h2
  have hnat : separatorX k * Real.binEntropy (separatorY k / separatorX k) -
      (1 / 2) * Real.binEntropy (2 * separatorY k) = separatorLogEntropy k := by
    rw [h1, h2, ← separatorZ_eq, ← separatorW_eq]
    unfold separatorLogEntropy
    ring
  unfold separatorEntropy binaryEntropy
  rw [← hnat]
  ring

@[simp] theorem separatorEntropy_quarter :
    separatorEntropy (1 / 4) = 1 - binaryEntropy (1 / 4) := by
  have hformula : separatorEntropy (1 / 4) =
      (3 / 4) * binaryEntropy (1 / 3) - 1 / 2 := by
    norm_num [separatorEntropy, separatorX, separatorY]
  rw [hformula, binaryEntropy_quarter_complement]

/-- The manuscript's sharp separator bound, with no positive exponential error. -/
theorem separatorEntropy_le {k : ℝ} (hk : k ∈ Set.Icc (1 / 6) (1 / 3)) :
    separatorEntropy k ≤ 1 - binaryEntropy (1 / 4) := by
  have h := div_le_div_of_nonneg_right (separatorLogEntropy_le_quarter hk)
    (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  rw [← separatorEntropy_eq_logEntropy hk,
    ← separatorEntropy_eq_logEntropy (by norm_num : (1 / 4 : ℝ) ∈ Set.Icc (1 / 6) (1 / 3)),
    separatorEntropy_quarter] at h
  exact h

end LowSpaceSubsetSum

end OAI
