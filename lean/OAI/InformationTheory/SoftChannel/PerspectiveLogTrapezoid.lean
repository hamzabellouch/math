import OAI.InformationTheory.BooleanNoise.PerspectiveLogTrapezoid
import OAI.InformationTheory.SoftChannel.NormalizedPair

namespace OAI

section

noncomputable section

namespace LeanBlast.CourtadeKumar

def PerspectiveLogTrapezoid_trapezoidGap (q w : ℝ) : ℝ :=
  (1 + w - 2 * q) * (Real.log (1 - q) - Real.log (w - q)) +
    (1 + w) * Real.log w

def PerspectiveLogTrapezoid_trapezoidGapDeriv (q w : ℝ) : ℝ :=
  Real.log (1 - q) - Real.log (w - q) - (1 + w - 2 * q) / (w - q) +
    Real.log w + (1 + w) / w

theorem PerspectiveLogTrapezoid_hasDerivAt_trapezoidGap (q w : ℝ) (hw0 : 0 < w) (hqw : q < w) :
    HasDerivAt (PerspectiveLogTrapezoid_trapezoidGap q) (PerspectiveLogTrapezoid_trapezoidGapDeriv q w) w := by
  have ha := ((hasDerivAt_id w).const_add (1 : ℝ)).sub_const (2 * q)
  have hb := HasDerivAt.const_sub (Real.log (1 - q))
    (((hasDerivAt_id w).sub_const q).log (ne_of_gt (sub_pos.mpr hqw)))
  have hc := ((hasDerivAt_id w).const_add (1 : ℝ)).mul
    (Real.hasDerivAt_log (ne_of_gt hw0))
  convert! (ha.mul hb).add hc using 1
  dsimp [PerspectiveLogTrapezoid_trapezoidGap, PerspectiveLogTrapezoid_trapezoidGapDeriv]
  ring

theorem PerspectiveLogTrapezoid_trapezoidGapDeriv_nonpos (q w : ℝ)
    (hq0 : 0 ≤ q) (hqw : q < w) (hw1 : w ≤ 1) : PerspectiveLogTrapezoid_trapezoidGapDeriv q w ≤ 0 := by
  have hw0 : 0 < w := lt_of_le_of_lt hq0 hqw
  have hd : 0 < w - q := sub_pos.mpr hqw
  have hq1 : q < 1 := lt_of_lt_of_le hqw hw1
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  let r : ℝ := (1 - q) * w / (w - q)
  have hr : 0 < r := div_pos (mul_pos h1q hw0) hd
  have hlog := Real.log_le_sub_one_of_pos hr
  have hlogeq : Real.log r = Real.log (1 - q) + Real.log w - Real.log (w - q) := by
    dsimp [r]
    rw [Real.log_div (ne_of_gt (mul_pos h1q hw0)) (ne_of_gt hd),
      Real.log_mul (ne_of_gt h1q) (ne_of_gt hw0)]
  rw [hlogeq] at hlog
  have hrem : r - 1 + (1 + w) / w - (1 + w - 2 * q) / (w - q) =
      -q * (1 - w) ^ 2 / (w * (w - q)) := by
    dsimp [r]
    field_simp [ne_of_gt hw0, ne_of_gt hd]
    ring
  have hrest : r - 1 + (1 + w) / w - (1 + w - 2 * q) / (w - q) ≤ 0 := by
    rw [hrem]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq0) (sq_nonneg _))
      (mul_nonneg hw0.le hd.le)
  unfold PerspectiveLogTrapezoid_trapezoidGapDeriv
  linarith

theorem PerspectiveLogTrapezoid_trapezoidGap_nonneg (q w : ℝ)
    (hq0 : 0 ≤ q) (hqw : q < w) (hw1 : w ≤ 1) : 0 ≤ PerspectiveLogTrapezoid_trapezoidGap q w := by
  have hw0 : 0 < w := lt_of_le_of_lt hq0 hqw
  have hd (v : ℝ) (hv : v ∈ Set.Icc w 1) :
      HasDerivAt (PerspectiveLogTrapezoid_trapezoidGap q) (PerspectiveLogTrapezoid_trapezoidGapDeriv q v) v :=
    PerspectiveLogTrapezoid_hasDerivAt_trapezoidGap q v (lt_of_lt_of_le hw0 hv.1) (lt_of_lt_of_le hqw hv.1)
  have hanti : AntitoneOn (PerspectiveLogTrapezoid_trapezoidGap q) (Set.Icc w 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc w 1)
    · intro v hv
      exact (hd v hv).continuousAt.continuousWithinAt
    · intro v hv
      exact (hd v (interior_subset hv)).differentiableAt.differentiableWithinAt
    · intro v hv
      have hvm : v ∈ Set.Icc w 1 := interior_subset hv
      rw [(hd v hvm).deriv]
      exact PerspectiveLogTrapezoid_trapezoidGapDeriv_nonpos q v hq0 (lt_of_lt_of_le hqw hvm.1) hvm.2
  have h := hanti ⟨le_refl w, hw1⟩ ⟨hw1, le_refl 1⟩ hw1
  simpa [PerspectiveLogTrapezoid_trapezoidGap] using h

end LeanBlast.CourtadeKumar
end
end

end OAI
