import OAI.Geometry.RCD.Transport.RenyiTangent
import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # A bounded dual approximation for the finite Rényi entropy

The logarithmic tests are clipped at finite levels. Their nonnegative
scores have an integrable bound independent of the clipping level. This
is the scalar ingredient of the semicontinuity used in the entropy
minimizing midpoint construction of Rajala, arXiv:1202.6514, Lemma 2.4.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

def renyiDualScore (q r s : ℝ) : ℝ :=
  q*r*Real.exp ((q-1)*s)+(1-q)*Real.exp (q*s)

theorem renyiDualScore_nonneg {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr : 0 ≤ r) (s : ℝ) : 0 ≤ renyiDualScore q r s := by
  unfold renyiDualScore
  positivity

theorem renyiDualScore_log {q r : ℝ} (hr : 0 < r) :
    renyiDualScore q r (Real.log r) = r^q := by
  have he : r*Real.exp ((q-1)*Real.log r) = r^q := by
    rw [mul_comm (q-1), ← Real.rpow_def_of_pos hr]
    calc
      r*r^(q-1) = r^(1:ℝ)*r^(q-1) := by rw [Real.rpow_one]
      _ = r^(1+(q-1)) := (Real.rpow_add hr _ _).symm
      _ = r^q := by congr 1; ring
  unfold renyiDualScore
  rw [mul_assoc, he, mul_comm q (Real.log r), ← Real.rpow_def_of_pos hr]
  ring

theorem rpow_le_renyiDualScore {q r : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hr : 0 ≤ r) (s : ℝ) : r^q ≤ renyiDualScore q r s := by
  have h := rpow_tangent_upper (Real.exp_pos s) hr hq0 hq1
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at h
  calc
    _ ≤ (1-q)*Real.exp (s*q)+q*Real.exp (s*(q-1))*r := h
    _ = renyiDualScore q r s := by
      rw [mul_comm s q, mul_comm s (q-1)]
      unfold renyiDualScore
      ring

theorem renyiDualScore_logTest_bound {q M r : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hM : 0 ≤ M) (hr : 0 ≤ r) :
    renyiDualScore q r (entropyLogTest M r) ≤ 1+r := by
  rcases le_total r (Real.exp (-M)) with hlo | hlo
  · rw [entropyLogTest_low hM hlo]
    have hmul := mul_le_mul_of_nonneg_right hlo (Real.exp_pos ((q-1)*(-M))).le
    rw [← Real.exp_add] at hmul
    have he : -M+(q-1)*(-M) = q*(-M) := by ring
    rw [he] at hmul
    have hexp : Real.exp (q*(-M)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hq := mul_le_mul_of_nonneg_left hmul hq0.le
    dsimp [renyiDualScore]
    nlinarith
  · rcases le_total (Real.exp M) r with hhi | hhi
    · rw [entropyLogTest_high hM hhi]
      have he0 : Real.exp ((q-1)*M) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have he1 : Real.exp (q*M) ≤ r :=
        (Real.exp_le_exp.mpr (by nlinarith : q*M ≤ M)).trans hhi
      have h0 := mul_le_mul_of_nonneg_left he0 (mul_nonneg hq0.le hr)
      have h1 := mul_le_mul_of_nonneg_left he1 (by linarith : 0 ≤ 1-q)
      dsimp [renyiDualScore]
      nlinarith
    · rw [entropyLogTest_middle hlo hhi, renyiDualScore_log ((Real.exp_pos _).trans_le hlo)]
      by_cases hr1 : r ≤ 1
      · have h := Real.rpow_le_one hr hr1 hq0.le
        linarith
      · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hr1) hq1.le
        rw [Real.rpow_one] at h
        linarith

theorem renyiDualScore_logTest_tendsto {q r : ℝ} (hq0 : 0 < q) (_hq1 : q < 1)
    (hr : 0 ≤ r) :
    Tendsto (fun k : ℕ => renyiDualScore q r (entropyLogTest (k+1) r))
      atTop (𝓝 (r^q)) := by
  rcases hr.eq_or_lt with hr | hr
  · subst r
    have he : ∀ k : ℕ, renyiDualScore q 0 (entropyLogTest (k+1) 0) =
        (1-q)*Real.exp (-q*((k:ℝ)+1)) := by
      intro k
      rw [entropyLogTest_low (by positivity) (Real.exp_pos _).le]
      dsimp [renyiDualScore]
      simp only [mul_zero, zero_mul, zero_add]
      congr 2
      ring
    simp_rw [he, Real.zero_rpow hq0.ne']
    have ht : Tendsto (fun k : ℕ => -q*((k:ℝ)+1)) atTop atBot := by
      have hnat : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      exact Filter.Tendsto.const_mul_atTop_of_neg (neg_neg_of_pos hq0)
        (tendsto_atTop_add_const_right _ 1 hnat)
    simpa using (tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp ht))
  · have hnat : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hev : ∀ᶠ k : ℕ in atTop, |Real.log r| ≤ (k:ℝ)+1 :=
      (tendsto_atTop_add_const_right _ 1 hnat).eventually (eventually_ge_atTop _)
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with k hk
    obtain ⟨hlo,hhi⟩ := abs_le.mp hk
    have hl : Real.exp (-((k:ℝ)+1)) ≤ r := by
      rw [← Real.exp_log hr]
      exact Real.exp_le_exp.mpr hlo
    have hh : r ≤ Real.exp ((k:ℝ)+1) := by
      rw [← Real.exp_log hr]
      exact Real.exp_le_exp.mpr hhi
    rw [entropyLogTest_middle hl hh, renyiDualScore_log hr]

end RegularPointCoordinates

end

end OAI
