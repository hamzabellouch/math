import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLE.ClippedCoordinates

namespace OAI

/-! Global estimates for the exact reciprocal cutoff used in the
prescribed Euler construction. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Target

private def reciprocalCutoff (c : ℝ) (z : ℂ) : ℂ :=
  star z / (max (‖z‖ ^ 2) c : ℝ)

private lemma cutoff_denom_lower (c : ℝ) (hc : 0 < c) (z : ℂ) :
    Real.sqrt c * ‖z‖ ≤ max (‖z‖ ^ 2) c := by
  have hs := Real.sq_sqrt hc.le
  have hsq := sq_nonneg (‖z‖-Real.sqrt c)
  have hz := le_max_left (‖z‖ ^ 2) c
  have hc' := le_max_right (‖z‖ ^ 2) c
  nlinarith

private lemma reciprocalCutoff_norm_le (c : ℝ) (hc : 0 < c) (z : ℂ) :
    ‖reciprocalCutoff c z‖ ≤ (Real.sqrt c)⁻¹ := by
  have hA : 0 < max (‖z‖ ^ 2) c := hc.trans_le (le_max_right _ _)
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  rw [reciprocalCutoff,norm_div,norm_star,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hA]
  apply (div_le_iff₀ hA).2
  simpa only [div_eq_mul_inv,mul_comm] using
    (le_div_iff₀ hs).2 (by simpa only [mul_comm] using cutoff_denom_lower c hc z)

private lemma reciprocalCutoff_dist_le (c : ℝ) (hc : 0 < c) (z w : ℂ) :
    dist (reciprocalCutoff c z) (reciprocalCutoff c w) ≤ (3/c)*dist z w := by
  let A : ℝ := max (‖z‖^2) c
  let B : ℝ := max (‖w‖^2) c
  have hA : 0 < A := hc.trans_le (le_max_right _ _)
  have hB : 0 < B := hc.trans_le (le_max_right _ _)
  have hAB : 0 < A*B := mul_pos hA hB
  have hcA : c ≤ A := le_max_right _ _
  have hcB : c ≤ B := le_max_right _ _
  have hwB : ‖w‖^2 ≤ B := le_max_left _ _
  have hzw : c*‖z‖*‖w‖ ≤ A*B := by
    have h := mul_le_mul (cutoff_denom_lower c hc z) (cutoff_denom_lower c hc w)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hA.le
    nlinarith [Real.sq_sqrt hc.le]
  have hww : c*‖w‖^2 ≤ A*B := by
    exact mul_le_mul hcA hwB (sq_nonneg _) hA.le
  have hdiff : |B-A| ≤ (‖z‖+‖w‖)*dist z w := by
    have hmax := abs_max_sub_max_le_abs (‖w‖^2) (‖z‖^2) c
    have hnorm := abs_norm_sub_norm_le w z
    have he : |‖w‖^2-‖z‖^2| = |‖w‖-‖z‖| *(‖z‖+‖w‖) := by
      rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      ring
    refine hmax.trans ?_
    rw [he]
    have hnorm' : |‖w‖-‖z‖| ≤ dist z w := by
      simpa only [← dist_eq_norm,dist_comm] using hnorm
    nlinarith [norm_nonneg z,norm_nonneg w]
  have he : reciprocalCutoff c z-reciprocalCutoff c w =
      star (z-w)/(A:ℂ)+star w*((B-A:ℝ):ℂ)/((A*B:ℝ):ℂ) := by
    simp only [reciprocalCutoff,star_sub,Complex.ofReal_sub,Complex.ofReal_mul]
    change star z/(A:ℂ)-star w/(B:ℂ) = _
    field_simp [Complex.ofReal_ne_zero.mpr hA.ne',Complex.ofReal_ne_zero.mpr hB.ne']
    ring
  rw [dist_eq_norm,he]
  calc
    _ ≤ ‖star (z-w)/(A:ℂ)‖+‖star w*((B-A:ℝ):ℂ)/((A*B:ℝ):ℂ)‖ := norm_add_le _ _
    _ = dist z w/A+‖w‖*|B-A|/(A*B) := by
      simp only [norm_div,norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hA,
        abs_of_pos hB,dist_eq_norm]
    _ ≤ dist z w/A+‖w‖*((‖z‖+‖w‖)*dist z w)/(A*B) := by
      gcongr
    _ ≤ (3/c)*dist z w := by
      have hcoef : (B+‖w‖*(‖z‖+‖w‖))/(A*B) ≤ 3/c := by
        apply (div_le_div_iff₀ hAB hc).2
        have hcb := mul_le_mul_of_nonneg_right hcA hB.le
        nlinarith
      calc
        dist z w/A+‖w‖*((‖z‖+‖w‖)*dist z w)/(A*B) =
            ((B+‖w‖*(‖z‖+‖w‖))/(A*B))*dist z w := by
          field_simp [hA.ne',hB.ne']
        _ ≤ (3/c)*dist z w := mul_le_mul_of_nonneg_right hcoef dist_nonneg


lemma cutoffField_bounds (κ : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    ∃ L K : ℝ≥0, (∀ b t z, ‖cutoffField κ b j t z‖ ≤ L) ∧
      ∀ b t, LipschitzWith K (cutoffField κ b j t) := by
  let c : ℝ := (j:ℝ)^(-(4:ℤ))
  have hc : 0 < c := zpow_pos (by exact_mod_cast (Nat.succ_le_iff.mp hj) : (0:ℝ)<j) _
  let L : ℝ≥0 := ⟨|a κ| *(Real.sqrt c)⁻¹,by positivity⟩
  let K : ℝ≥0 := ⟨|a κ| *(3/c),by positivity⟩
  refine ⟨L,K,?_,?_⟩
  · intro b t z
    change ‖(a κ:ℂ)*star (z-driverValue b t)/(max (‖z-driverValue b t‖^2) c:ℝ)‖ ≤ _
    rw [mul_div_assoc,norm_mul,Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (reciprocalCutoff_norm_le c hc _) (abs_nonneg _)
  · intro b t
    apply LipschitzWith.of_dist_le_mul
    intro z w
    have he (z : ℂ) : cutoffField κ b j t z = (a κ:ℂ)*reciprocalCutoff c (z-driverValue b t) := by
      simp only [cutoffField,reciprocalCutoff,mul_div_assoc,c]
    rw [he,he,dist_eq_norm,← mul_sub,norm_mul,Complex.norm_real]
    have h := reciprocalCutoff_dist_le c hc (z-driverValue b t) (w-driverValue b t)
    rw [dist_sub_right] at h
    change |a κ| * ‖reciprocalCutoff c (z-driverValue b t)-
      reciprocalCutoff c (w-driverValue b t)‖ ≤ (|a κ| *(3/c))*dist z w
    simpa only [dist_eq_norm,mul_assoc] using
      mul_le_mul_of_nonneg_left h (abs_nonneg (a κ))

lemma continuous_cutoffField (κ : ℝ) (b : Driver) (j : ℕ) (hj : 1 ≤ j) :
    Continuous (fun p : ℝ × ℂ => cutoffField κ b j p.1 p.2) := by
  have hc : 0 < (j:ℝ)^(-(4:ℤ)) := zpow_pos (by exact_mod_cast (Nat.succ_le_iff.mp hj) : (0:ℝ)<j) _
  have hd : Continuous (fun t : ℝ => driverValue b t) :=
    b.continuous.comp continuous_real_toNNReal
  unfold cutoffField
  fun_prop (disch := intro x; exact_mod_cast ne_of_gt (hc.trans_le (le_max_right _ _)))

end SLEExactGauge.Target

end

end OAI
