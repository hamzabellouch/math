import OAI.InformationTheory.BooleanNoise.Basic
import OAI.InformationTheory.BooleanNoise.EntropyScalars
import OAI.InformationTheory.BooleanNoise.EntropyBounds
import OAI.InformationTheory.BooleanNoise.InverseRegularity
import OAI.InformationTheory.BooleanNoise.KRegularity
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

theorem pair_mean_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) : a ∈ Set.Ioo (-1) 1 := by
  have ha : |a| < 1 := lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg b)) h
  exact abs_lt.mp ha

theorem pair_add_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) : a + b ∈ Set.Ioo (-1) 1 := by
  exact abs_lt.mp (lt_of_le_of_lt (abs_add_le a b) h)

theorem pair_sub_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) : a - b ∈ Set.Ioo (-1) 1 := by
  exact abs_lt.mp (lt_of_le_of_lt (abs_sub a b) h)

theorem pair_denom_add_pos (a b : ℝ) (h : |a| + |b| < 1) : 0 < 1 + a := by
  have ha := (pair_mean_mem_Ioo a b h).1
  linarith

theorem pair_denom_sub_pos (a b : ℝ) (h : |a| + |b| < 1) : 0 < 1 - a := by
  have ha := (pair_mean_mem_Ioo a b h).2
  linarith

theorem pair_abs_lt_denom_add (a b : ℝ) (h : |a| + |b| < 1) : |b| < 1 + a := by
  linarith [neg_le_abs a]

theorem pair_abs_lt_denom_sub (a b : ℝ) (h : |a| + |b| < 1) : |b| < 1 - a := by
  linarith [le_abs_self a]

private theorem div_mem_Ioo (s b : ℝ) (hs : 0 < s) (hb : |b| < s) :
    b / s ∈ Set.Ioo (-1) 1 := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  constructor
  · apply (lt_div_iff₀ hs).2
    linarith
  · apply (div_lt_iff₀ hs).2
    linarith

theorem pair_ratio_add_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) :
    b / (1 + a) ∈ Set.Ioo (-1) 1 :=
  div_mem_Ioo (1 + a) b (pair_denom_add_pos a b h) (pair_abs_lt_denom_add a b h)

theorem pair_ratio_sub_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) :
    b / (1 - a) ∈ Set.Ioo (-1) 1 :=
  div_mem_Ioo (1 - a) b (pair_denom_sub_pos a b h) (pair_abs_lt_denom_sub a b h)

theorem pair_variance_pos (a b : ℝ) (h : |a| + |b| < 1) : 0 < 1 - a ^ 2 := by
  have hp := mul_pos (pair_denom_add_pos a b h) (pair_denom_sub_pos a b h)
  nlinarith

theorem pair_abs_lt_variance (a b : ℝ) (h : |a| + |b| < 1) :
    |b| < 1 - a ^ 2 := by
  have ha1 : |a| < 1 := lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg b)) h
  have hprod := mul_nonneg (abs_nonneg a) (show 0 ≤ 1 - |a| by linarith)
  nlinarith [sq_abs a]

theorem pair_weighted_sq (a b : ℝ) (h : |a| + |b| < 1) :
    (1 + a) / 2 * (b / (1 + a)) ^ 2 + (1 - a) / 2 * (b / (1 - a)) ^ 2 =
      b ^ 2 / (1 - a ^ 2) := by
  have hp := ne_of_gt (pair_denom_add_pos a b h)
  have hm := ne_of_gt (pair_denom_sub_pos a b h)
  have hv := ne_of_gt (pair_variance_pos a b h)
  field_simp
  ring

theorem pairEntropyGap_eq_psi (a b : ℝ) :
    pairEntropyGap a b = (psi (a + b) + psi (a - b)) / 2 - psi a := by
  unfold pairEntropyGap entropy
  ring

@[simp] theorem pairEntropyGap_zero (a : ℝ) : pairEntropyGap a 0 = 0 := by
  simp [pairEntropyGap]

@[simp] theorem pairDissipation_zero (a : ℝ) : pairDissipation a 0 = 0 := by
  simp [pairDissipation]

theorem pairEntropyGap_neg_right (a b : ℝ) : pairEntropyGap a (-b) = pairEntropyGap a b := by
  change entropy a - (entropy (a - b) + entropy (a - -b)) / 2 = _
  rw [sub_neg_eq_add]
  unfold pairEntropyGap
  ring

private theorem weighted_psi_div (s b : ℝ) (hs : 0 < s) (hb : |b| < s) :
    s / 2 * psi (b / s) =
      (s + b) / 4 * Real.log (s + b) + (s - b) / 4 * Real.log (s - b) -
        s / 2 * Real.log s := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hp : s + b ≠ 0 := ne_of_gt (by linarith)
  have hm : s - b ≠ 0 := ne_of_gt (by linarith)
  have hplus : 1 + b / s = (s + b) / s := by field_simp
  have hminus : 1 - b / s = (s - b) / s := by field_simp
  rw [psi, hplus, hminus, Real.log_div hp hs0, Real.log_div hm hs0]
  field_simp
  ring

theorem pairEntropyGap_weighted (a b : ℝ) (h : |a| + |b| < 1) :
    pairEntropyGap a b =
      (1 + a) / 2 * psi (b / (1 + a)) + (1 - a) / 2 * psi (b / (1 - a)) := by
  rw [weighted_psi_div (1 + a) b (pair_denom_add_pos a b h) (pair_abs_lt_denom_add a b h),
    weighted_psi_div (1 - a) b (pair_denom_sub_pos a b h) (pair_abs_lt_denom_sub a b h)]
  unfold pairEntropyGap entropy psi
  ring_nf

private theorem pair_artanh_eq_log_sub (x : ℝ) (hx : x ∈ Set.Ioo (-1) 1) :
    Real.artanh x = (Real.log (1 + x) - Real.log (1 - x)) / 2 := by
  rw [Real.artanh_eq_half_log ⟨le_of_lt hx.1, le_of_lt hx.2⟩,
    Real.log_div (ne_of_gt (by linarith [hx.1])) (ne_of_gt (by linarith [hx.2]))]
  ring

private theorem artanh_div (s b : ℝ) (hs : 0 < s) (hb : |b| < s) :
    Real.artanh (b / s) = (Real.log (s + b) - Real.log (s - b)) / 2 := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hp : s + b ≠ 0 := ne_of_gt (by linarith)
  have hm : s - b ≠ 0 := ne_of_gt (by linarith)
  have hplus : 1 + b / s = (s + b) / s := by field_simp
  have hminus : 1 - b / s = (s - b) / s := by field_simp
  rw [pair_artanh_eq_log_sub _ (div_mem_Ioo s b hs hb), hplus, hminus,
    Real.log_div hp hs0, Real.log_div hm hs0]
  ring

theorem pairDissipation_weighted (a b : ℝ) (h : |a| + |b| < 1) :
    pairDissipation a b =
      (1 + a) / 2 * (b / (1 + a) * Real.artanh (b / (1 + a))) +
        (1 - a) / 2 * (b / (1 - a) * Real.artanh (b / (1 - a))) := by
  have hp : 1 + a ≠ 0 := ne_of_gt (pair_denom_add_pos a b h)
  have hm : 1 - a ≠ 0 := ne_of_gt (pair_denom_sub_pos a b h)
  rw [pairDissipation, pair_artanh_eq_log_sub _ (pair_add_mem_Ioo a b h),
    pair_artanh_eq_log_sub _ (pair_sub_mem_Ioo a b h),
    artanh_div (1 + a) b (pair_denom_add_pos a b h) (pair_abs_lt_denom_add a b h),
    artanh_div (1 - a) b (pair_denom_sub_pos a b h) (pair_abs_lt_denom_sub a b h)]
  field_simp
  ring_nf

theorem pairDissipation_nonneg (a b : ℝ) (h : |a| + |b| < 1) :
    0 ≤ pairDissipation a b := by
  unfold pairDissipation
  by_cases hb : 0 ≤ b
  · apply mul_nonneg (by positivity)
    apply sub_nonneg.mpr
    exact Real.artanh_le_artanh (pair_sub_mem_Ioo a b h).1
      (pair_add_mem_Ioo a b h).2 (by linarith)
  · apply mul_nonneg_of_nonpos_of_nonpos (by linarith)
    apply sub_nonpos.mpr
    exact Real.artanh_le_artanh (pair_add_mem_Ioo a b h).1
      (pair_sub_mem_Ioo a b h).2 (by linarith)

theorem pairEntropyGap_nonneg (a b : ℝ) (h : |a| + |b| < 1) :
    0 ≤ pairEntropyGap a b := by
  rw [pairEntropyGap_weighted a b h]
  exact add_nonneg
    (mul_nonneg (by linarith [pair_denom_add_pos a b h]) (psi_nonneg _))
    (mul_nonneg (by linarith [pair_denom_sub_pos a b h]) (psi_nonneg _))

theorem pairEntropyGap_div_variance_nonneg (a b : ℝ) (h : |a| + |b| < 1) :
    0 ≤ pairEntropyGap a b / (1 - a ^ 2) :=
  div_nonneg (pairEntropyGap_nonneg a b h) (le_of_lt (pair_variance_pos a b h))

theorem pairEntropyGap_lt_ell (a b : ℝ) (h : |a| + |b| < 1) :
    pairEntropyGap a b < ell := by
  rw [pairEntropyGap_weighted a b h]
  calc
    _ < (1 + a) / 2 * ell + (1 - a) / 2 * ell :=
      add_lt_add
        (mul_lt_mul_of_pos_left (psi_lt_ell (pair_ratio_add_mem_Ioo a b h))
          (by linarith [pair_denom_add_pos a b h]))
        (mul_lt_mul_of_pos_left (psi_lt_ell (pair_ratio_sub_mem_Ioo a b h))
          (by linarith [pair_denom_sub_pos a b h]))
    _ = ell := by ring

theorem pair_entropyAverage_pos (a b : ℝ) (h : |a| + |b| < 1) :
    0 < (entropy (a + b) + entropy (a - b)) / 2 := by
  have hp := entropy_pos (pair_add_mem_Ioo a b h)
  have hm := entropy_pos (pair_sub_mem_Ioo a b h)
  linarith

theorem pairEntropyGap_lt_entropy (a b : ℝ) (h : |a| + |b| < 1) :
    pairEntropyGap a b < entropy a := by
  unfold pairEntropyGap
  linarith [pair_entropyAverage_pos a b h]

theorem pairEntropyGap_le_quadratic (a b : ℝ) (h : |a| + |b| < 1) :
    pairEntropyGap a b ≤ ell * (b ^ 2 / (1 - a ^ 2)) := by
  calc
    _ = (1 + a) / 2 * psi (b / (1 + a)) +
        (1 - a) / 2 * psi (b / (1 - a)) := pairEntropyGap_weighted a b h
    _ ≤ (1 + a) / 2 * (ell * (b / (1 + a)) ^ 2) +
        (1 - a) / 2 * (ell * (b / (1 - a)) ^ 2) :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (psi_le_ell_mul_sq (le_of_lt (abs_lt.mpr (pair_ratio_add_mem_Ioo a b h))))
          (by linarith [pair_denom_add_pos a b h]))
        (mul_le_mul_of_nonneg_left
          (psi_le_ell_mul_sq (le_of_lt (abs_lt.mpr (pair_ratio_sub_mem_Ioo a b h))))
          (by linarith [pair_denom_sub_pos a b h]))
    _ = ell * ((1 + a) / 2 * (b / (1 + a)) ^ 2 +
        (1 - a) / 2 * (b / (1 - a)) ^ 2) := by ring
    _ = _ := by rw [pair_weighted_sq a b h]

theorem pairEntropyGap_div_variance_lt_ell (a b : ℝ) (h : |a| + |b| < 1) :
    pairEntropyGap a b / (1 - a ^ 2) < ell := by
  have hA := pair_variance_pos a b h
  have hb := pair_abs_lt_variance a b h
  have hprod := mul_pos (show 0 < 1 - a ^ 2 - |b| by linarith)
    (show 0 < 1 - a ^ 2 + |b| by linarith [abs_nonneg b])
  have hsq : b ^ 2 < (1 - a ^ 2) * (1 - a ^ 2) := by nlinarith [sq_abs b]
  have hratio : b ^ 2 / (1 - a ^ 2) < 1 - a ^ 2 := (div_lt_iff₀ hA).2 hsq
  apply (div_lt_iff₀ hA).2
  exact (pairEntropyGap_le_quadratic a b h).trans_lt
    (mul_lt_mul_of_pos_left hratio ell_pos)

theorem hasDerivAt_pairEntropyGap (a b : ℝ) (h : |a| + |b| < 1) :
    HasDerivAt (fun t => pairEntropyGap a t)
      ((Real.artanh (a + b) - Real.artanh (a - b)) / 2) b := by
  have hp : HasDerivAt (fun t => psi (a + t)) (Real.artanh (a + b)) b := by
    convert! (hasDerivAt_psi (pair_add_mem_Ioo a b h)).comp b
      ((hasDerivAt_id b).const_add a) using 1
    simp
  have hm : HasDerivAt (fun t => psi (a - t)) (-Real.artanh (a - b)) b := by
    convert! (hasDerivAt_psi (pair_sub_mem_Ioo a b h)).comp b
      ((hasDerivAt_const b a).sub (hasDerivAt_id b)) using 1
    simp
  have hf : (fun t => pairEntropyGap a t) =
      (fun t => (psi (a + t) + psi (a - t)) / 2 - psi a) :=
    funext (pairEntropyGap_eq_psi a)
  rw [hf]
  convert! ((hp.add hm).div_const 2).sub_const (psi a) using 1

theorem pairDissipation_eq_mul_deriv (a b : ℝ) (h : |a| + |b| < 1) :
    pairDissipation a b = b * deriv (fun t => pairEntropyGap a t) b := by
  rw [(hasDerivAt_pairEntropyGap a b h).deriv, pairDissipation]
  ring

theorem pairDissipation_weighted_r (a b : ℝ) (h : |a| + |b| < 1) :
    pairDissipation a b =
      (1 + a) / 2 * r (psi (b / (1 + a))) +
        (1 - a) / 2 * r (psi (b / (1 - a))) := by
  rw [r_psi (pair_ratio_add_mem_Ioo a b h), r_psi (pair_ratio_sub_mem_Ioo a b h)]
  exact pairDissipation_weighted a b h

theorem r_pairEntropyGap_le_pairDissipation (a b : ℝ) (h : |a| + |b| < 1) :
    r (pairEntropyGap a b) ≤ pairDissipation a b := by
  have hp := pair_ratio_add_mem_Ioo a b h
  have hm := pair_ratio_sub_mem_Ioo a b h
  have hJ := convexOn_r.2
    (show psi (b / (1 + a)) ∈ Set.Ico 0 ell from ⟨psi_nonneg _, psi_lt_ell hp⟩)
    (show psi (b / (1 - a)) ∈ Set.Ico 0 ell from ⟨psi_nonneg _, psi_lt_ell hm⟩)
    (show 0 ≤ (1 + a) / 2 by linarith [pair_denom_add_pos a b h])
    (show 0 ≤ (1 - a) / 2 by linarith [pair_denom_sub_pos a b h])
    (show (1 + a) / 2 + (1 - a) / 2 = 1 by ring)
  simp only [smul_eq_mul] at hJ
  rw [← pairEntropyGap_weighted a b h] at hJ
  exact hJ.trans_eq (pairDissipation_weighted_r a b h).symm

theorem rGap_pairEntropyGap_le (a b : ℝ) (h : |a| + |b| < 1) :
    rGap (pairEntropyGap a b) ≤ pairDissipation a b - 2 * pairEntropyGap a b := by
  exact sub_le_sub_right (r_pairEntropyGap_le_pairDissipation a b h) _

theorem K_pairEntropyGap_le (a b : ℝ) (h : |a| + |b| < 1) :
    K (pairEntropyGap a b) ≤ pairDissipation a b - 2 * pairEntropyGap a b :=
  (K_le_rGap (pairEntropyGap_nonneg a b h) (pairEntropyGap_lt_ell a b h)).trans
    (rGap_pairEntropyGap_le a b h)

end LeanBlast.CourtadeKumar

end

end OAI
