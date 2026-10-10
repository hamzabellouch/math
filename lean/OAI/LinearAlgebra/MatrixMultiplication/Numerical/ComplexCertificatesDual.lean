import OAI.LinearAlgebra.MatrixMultiplication.Numerical.ComplexCertificatesLog
import OAI.LinearAlgebra.MatrixMultiplication.Duality.WitnessArithmetic

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

namespace MatrixMultiplication.ComplexCertificates

open DualWitness

theorem rho24_bounds : (1597 : ℝ) / 5000 < rho24 ∧ rho24 < (639 : ℝ) / 2000 := by
  norm_num [rho24, rho8]

theorem rho48_bounds : (67 : ℝ) / 125 < rho48 ∧ rho48 < (537 : ℝ) / 1000 := by
  norm_num [rho48, rho24, rho8]

theorem inactive48_lower : (463 : ℝ) / 1000 < 1 - rho48 := by
  norm_num [rho48, rho24, rho8]

theorem inactive288_lower : (9 : ℝ) / 25 < 1 - rho288 := by
  norm_num [rho288, rho96, rho48, rho24, rho8]

theorem delta24_bounds :
    (87 : ℝ) / 250 < delta24 ∧ delta24 < (177 : ℝ) / 500 := by
  obtain ⟨hl, hh⟩ := log_nine_sevenths_bounds
  norm_num [delta24, rho24, rho8]
  constructor <;> linarith

theorem z48_bounds : (127 : ℝ) / 200 < z48 ∧ z48 < (651 : ℝ) / 1000 := by
  obtain ⟨hl, hh⟩ := delta24_bounds
  have helo : (701 : ℝ) / 1000 < Real.exp (-delta24) :=
    exp_neg_354_lower.trans (Real.exp_lt_exp.mpr (by linarith))
  have hehi : Real.exp (-delta24) < (707 : ℝ) / 1000 :=
    (Real.exp_lt_exp.mpr (by linarith : -delta24 < -(87 / 250 : ℝ))).trans
      exp_neg_348_upper
  have harglo : (1 + (701 / 1000 : ℝ)) ^ 2 - 1 <
      (1 + Real.exp (-delta24)) ^ 2 - 1 := by gcongr
  have harghi : (1 + Real.exp (-delta24)) ^ 2 - 1 <
      (1 + (707 / 1000 : ℝ)) ^ 2 - 1 := by gcongr
  have hargpos : 0 < (1 + Real.exp (-delta24)) ^ 2 - 1 := by
    norm_num at harglo
    linarith
  exact ⟨log_z48_lower.trans (Real.log_lt_log (by norm_num) harglo),
    (Real.log_lt_log hargpos harghi).trans log_z48_upper⟩

theorem delta96_bounds : 0 < delta96 ∧ delta96 < (43 : ℝ) / 50 := by
  obtain ⟨hr, hr'⟩ := rho48_bounds
  obtain ⟨hz, hz'⟩ := z48_bounds
  have hd : 0 < 1 + rho48 := by linarith
  constructor
  · exact div_pos (by linarith) hd
  · apply (div_lt_iff₀ hd).2
    linarith

theorem z288_bounds : (157 : ℝ) / 250 < z288 ∧ z288 < 2 := by
  obtain ⟨hd, hd'⟩ := delta96_bounds
  have helo : (169 : ℝ) / 400 < Real.exp (-delta96) :=
    exp_neg_86_lower.trans (Real.exp_lt_exp.mpr (by linarith))
  have hehi : Real.exp (-delta96) < 1 := by
    simpa using Real.exp_lt_exp.mpr (by linarith : -delta96 < 0)
  have harglo : (1 + (169 / 400 : ℝ)) ^ 3 - 1 <
      (1 + Real.exp (-delta96)) ^ 3 - 1 := by gcongr
  have harghi : (1 + Real.exp (-delta96)) ^ 3 - 1 < 7 := by
    have h : (1 + Real.exp (-delta96)) ^ 3 - 1 < (1 + (1 : ℝ)) ^ 3 - 1 := by
      gcongr
    norm_num at h
    exact h
  have hargpos : 0 < (1 + Real.exp (-delta96)) ^ 3 - 1 := by
    norm_num at harglo
    linarith
  have hlog7 : Real.log 7 < 2 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).2
    refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 6)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact ⟨log_z288_lower.trans (Real.log_lt_log (by norm_num) harglo),
    (Real.log_lt_log hargpos harghi).trans hlog7⟩

theorem hiddenRate_lower :
    (9 / 64 : ℝ) * (549 / 500) + (463 / 1000 : ℝ) / 48 * (127 / 200) +
      (9 / 25 : ℝ) / 288 * (157 / 250) < hiddenRate := by
  have h3 := log_three_lower
  have h48 := z48_bounds.1
  have h288 := z288_bounds.1
  have hr48 := inactive48_lower
  have hr288 := inactive288_lower
  dsimp [hiddenRate]
  gcongr

theorem dual_aspect_lower : (1548637 : ℝ) / 3327360 < aspect := by
  have h2 := log_two_bounds
  have hD := hiddenRate_lower
  have hl2 : 0 < Real.log 2 := by linarith [h2.1]
  apply (lt_div_iff₀ hl2).2
  norm_num at hD
  linarith [h2.2]

theorem dual_aspect_lt_one : aspect < 1 := by
  have h3 := log_three_upper
  have h48 := z48_bounds
  have h288 := z288_bounds
  have hr48 := DualWitness.rho48_range
  have hr288 := DualWitness.rho288_range
  have h2 := log_two_bounds
  have hD : hiddenRate < (9 / 64 : ℝ) * (10987 / 10000) +
      (1 : ℝ) / 48 * (651 / 1000) + (1 : ℝ) / 288 * 2 := by
    dsimp [hiddenRate]
    gcongr <;> linarith
  have hl2 : 0 < Real.log 2 := by linarith [h2.1]
  apply (div_lt_iff₀ hl2).2
  norm_num at hD
  linarith [h2.1]

theorem dual_aspect_milestone : (465 : ℝ) / 1000 < aspect := by
  have h := dual_aspect_lower
  norm_num at h ⊢
  linarith

end MatrixMultiplication.ComplexCertificates

end OAI
