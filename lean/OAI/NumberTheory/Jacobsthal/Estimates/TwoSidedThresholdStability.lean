import OAI.NumberTheory.Jacobsthal.Partitions.CrossingBandGeometry
import OAI.NumberTheory.Jacobsthal.Partitions.TwoSidedThresholdGeometry

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdStability
open FinitePathGeometry NearbyParentGeometry TwoSidedThresholdGeometry ErdosEvenThreshold

theorem reciprocal_lipschitz_one {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |1/x-1/y| ≤ |x-y| := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have he : 1/x-1/y=(y-x)/(x*y) := by field_simp
  rw [he,abs_div,abs_of_pos (mul_pos hx0 hy0),abs_sub_comm y x]
  apply div_le_self (abs_nonneg _)
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

theorem reciprocal_log_gap_error {R Q D : ℝ} (hR : 3 ≤ R) (hQ : 3 ≤ Q)
    (hlog : |Real.log R-Real.log Q| ≤ D) : |1/R-1/Q| ≤ Real.exp D-1 := by
  have hR0 : 0 < R := by linarith
  have hQ0 : 0 < Q := by linarith
  have hD : 0 ≤ D := (abs_nonneg _).trans hlog
  have hc : 1 ≤ Real.exp D := Real.one_le_exp_iff.mpr hD
  have hrel := log_gap_relative hR0 hQ0 hlog
  have hxy : 1/R ≤ Real.exp D*(1/Q) := by
    rw [mul_one_div]
    apply (div_le_div_iff₀ hR0 hQ0).mpr
    simpa only [one_mul] using hrel.2
  have hyx : 1/Q ≤ Real.exp D*(1/R) := by
    rw [mul_one_div]
    apply (div_le_div_iff₀ hQ0 hR0).mpr
    simpa only [one_mul] using hrel.1
  have hh := clipped_relative_stability (A := 1/3) (by norm_num) hc hxy hyx
  have hRi : 1/R ≤ (1/3:ℝ) := one_div_le_one_div_of_le (by norm_num) hR
  have hQi : 1/Q ≤ (1/3:ℝ) := one_div_le_one_div_of_le (by norm_num) hQ
  rw [min_eq_right hRi,min_eq_right hQi] at hh
  linarith

theorem normalizedSlack_stability {R Q t u h G : ℝ}
    (hR : 0 < R) (hQ : 0 < Q) (ht : 2 ≤ t) (hu : 2 ≤ u)
    (hclose : |t-u| ≤ h) (hgap : |1/R-1/Q| ≤ G) :
    |normalizedSlack R t-normalizedSlack Q u| ≤ 3*h+2*G := by
  have ht0 : 0 < t+1 := by linarith
  have hu0 : 0 < u+1 := by linarith
  have hh0 : 0 ≤ h := (abs_nonneg _).trans hclose
  have hG0 : 0 ≤ G := (abs_nonneg _).trans hgap
  have hi : |1/(t+1)-1/(u+1)| ≤ h := by
    have hh := reciprocal_lipschitz_one (x := t+1) (y := u+1) (by linarith) (by linarith)
    have hh' : |1/(t+1)-1/(u+1)| ≤ |t-u| := by simpa only [add_sub_add_right_eq_sub] using hh
    exact hh'.trans hclose
  have hA : |(t-2)/(t+1)-(u-2)/(u+1)| ≤ 3*h := by
    have he : (t-2)/(t+1)-(u-2)/(u+1)= -3*(1/(t+1)-1/(u+1)) := by
      field_simp [ht0.ne',hu0.ne']
      ring
    rw [he,abs_mul]
    norm_num
    simpa only [one_div] using hi
  have hB : |((t-1)/(t+1)-2/R)-((u-1)/(u+1)-2/Q)| ≤ 2*h+2*G := by
    have he : ((t-1)/(t+1)-2/R)-((u-1)/(u+1)-2/Q)=
        -2*(1/(t+1)-1/(u+1))-2*(1/R-1/Q) := by
      field_simp [ht0.ne',hu0.ne',hR.ne',hQ.ne']
      ring
    rw [he]
    calc
      _ ≤ |-2*(1/(t+1)-1/(u+1))|+|2*(1/R-1/Q)| := abs_sub _ _
      _ = 2*|1/(t+1)-1/(u+1)|+2*|1/R-1/Q| := by rw [abs_mul,abs_mul]; norm_num
      _ ≤ _ := by linarith
  rw [normalizedSlack_eq_min hR ht0,normalizedSlack_eq_min hQ hu0]
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by linarith) (by linarith))

theorem coupled_near_to_thick {R Q t u d h D : ℝ}
    (hQ : 0 < Q) (hu : 2 ≤ u) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hnear : t ∈ nearThreshold R d) (hclose : |t-u| ≤ h) (hsmall : h ≤ 1)
    (hlog : |Real.log R-Real.log Q| ≤ D) (hexp : Real.exp D ≤ 4/3) :
    3 ≤ Q ∧ u ∈ thickStrip Q (d/Q+3*h+3*(Real.exp D-1)) := by
  have hs : t ∈ thresholdStrip R d := (thresholdStrip_eq_near R d).symm ▸ hnear
  have hpar := strip_parameters hd1 hs
  have hR0 : 0 < R := by linarith [hpar.1]
  have hrel := log_gap_relative hR0 hQ hlog
  have hQ3 : 3 ≤ Q := by nlinarith [hrel.1,mul_le_mul_of_nonneg_right hexp hQ.le]
  have hR3 : 3 ≤ R := by linarith [hpar.1]
  have hG := reciprocal_log_gap_error hR3 hQ3 hlog
  have hG0 : 0 ≤ Real.exp D-1 := (abs_nonneg _).trans hG
  have hstab := normalizedSlack_stability hR0 hQ hs.1 hu hclose hG
  have hnorm : |normalizedSlack R t| ≤ d/R := by
    rw [normalizedSlack,abs_div,abs_of_pos hR0,abs_of_nonneg hnear.2.1]
    exact div_le_div_of_nonneg_right hnear.2.2 hR0.le
  have hdR : d/R ≤ d/Q+(Real.exp D-1) := by
    have hh := mul_le_mul_of_nonneg_left ((le_abs_self (1/R-1/Q)).trans hG) hd0
    have hc := mul_le_mul_of_nonneg_right hd1 hG0
    rw [mul_sub,mul_one_div,mul_one_div] at hh
    linarith
  refine ⟨hQ3,hu,by linarith [(abs_le.mp hclose).1,hpar.2],?_⟩
  have hh := abs_add_le (normalizedSlack Q u-normalizedSlack R t) (normalizedSlack R t)
  rw [sub_add_cancel,abs_sub_comm (normalizedSlack Q u)] at hh
  linarith
end NumberTheoryLean.TwoSidedThresholdStability

end

end Erdos970

end OAI
