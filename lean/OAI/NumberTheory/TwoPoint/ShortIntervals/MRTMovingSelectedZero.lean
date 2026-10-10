import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingZeroTerms

namespace OAI

/-! A selected zero supplies its entire reciprocal horizontal distance in
the shrinking-disk logarithmic derivative. This is the quantitative input
for the three-factor positivity contradiction. -/

namespace TwoPointCorrelations

open Complex Finset
open scoped BigOperators Classical

lemma mrt_disk_zero_multiplicity (f : ℂ → ℂ)
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : f 0 = 1) {ρ : ℂ} (hρ : ρ ∈ mrtDiskZeros f) :
    1 ≤ (analyticOrderAt f ρ).toNat := by
  have hfinite := Erdos970.lem_m_rho_is_nat (15 / 16) (7 / 8)
    (by norm_num) (by norm_num) f hf (by rw [h0]; exact one_ne_zero)
    (by norm_num) ρ hρ
  have hpos := Erdos970.lem_m_rho_ge_1 (15 / 16) (7 / 8)
    (by norm_num) (by norm_num) f hf (by rw [h0]; exact one_ne_zero)
    (by norm_num) ρ hρ
  simpa using ENat.toNat_le_toNat hpos hfinite

variable {q : ℕ} [NeZero q]

lemma mrt_moving_real_zero_mem (χ : DirichletCharacter ℂ q)
    {r t β : ℝ} (hr : 0 < r) (hβ : 1 - r / 4 ≤ β) (hβ1 : β ≤ 1)
    (hz : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) = 0) :
    mrtMovingRealPoint r β ∈ mrtDiskZeros (mrtMovingLFunction χ r t) := by
  refine ⟨?_, ?_⟩
  · have hn := mrt_moving_real_point_norm hr hβ (show β ≤ 1 + r by linarith)
    simpa using hn.trans (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8)
  · change DirichletCharacter.LFunction χ
      (mrtMovingPoint r t (mrtMovingRealPoint r β)) / _ = 0
    rw [mrt_moving_real_point hr, hz, zero_div]

lemma mrt_moving_selected_zero_sum (χ : DirichletCharacter ℂ q)
    {r t σ β : ℝ} (hr : 0 < r) (ht : 3 * r < |t|) (hσ : 1 < σ)
    (hβ : 1 - r / 4 ≤ β) (hβ1 : β ≤ 1)
    (hz : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) = 0) :
    (3 * r) / (σ - β) ≤
      ∑ ρ ∈ (mrtDiskZeros_finite (mrtMovingLFunction χ r t)
        (mrt_moving_LFunction_analytic χ hr ht) (mrt_moving_LFunction_zero χ hr t)).toFinset,
        (((analyticOrderAt (mrtMovingLFunction χ r t) ρ).toNat : ℂ) /
          (mrtMovingRealPoint r σ - ρ)).re := by
  let f := mrtMovingLFunction χ r t
  have hf := mrt_moving_LFunction_analytic χ hr ht
  have h0 := mrt_moving_LFunction_zero χ hr t
  let w := mrtMovingRealPoint r β
  have hw : w ∈ mrtDiskZeros f := mrt_moving_real_zero_mem χ hr hβ hβ1 hz
  have hm := mrt_disk_zero_multiplicity f hf h0 hw
  have hd : 0 < σ - β := by linarith
  have h3 : 0 < 3 * r := by positivity
  have hdiff : mrtMovingRealPoint r σ - w = (((σ - β) / (3 * r) : ℝ) : ℂ) := by
    dsimp [w, mrtMovingRealPoint]
    push_cast
    ring
  have hterm : (3 * r) / (σ - β) ≤
      (((analyticOrderAt f w).toNat : ℂ) / (mrtMovingRealPoint r σ - w)).re := by
    rw [hdiff]
    change (3 * r) / (σ - β) ≤
      ((((analyticOrderAt f w).toNat : ℝ) : ℂ) / (((σ - β) / (3 * r) : ℝ) : ℂ)).re
    rw [← Complex.ofReal_div, Complex.ofReal_re]
    calc
      _ = 1 / ((σ - β) / (3 * r)) := by field_simp [hr.ne', hd.ne']
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hm) (div_pos hd h3).le
  exact hterm.trans (single_le_sum
    (fun ρ hρ => mrt_moving_zero_term_nonneg χ hr ht hσ
      ((mrtDiskZeros_finite f hf h0).mem_toFinset.mp hρ))
    ((mrtDiskZeros_finite f hf h0).mem_toFinset.mpr hw))

/-- The same bound with the full negative reciprocal of a selected zero. -/
theorem mrt_moving_neg_logderiv_of_zero (χ : DirichletCharacter ℂ q)
    {r t B σ β : ℝ} (hr : 0 < r) (ht : 3 * r < |t|) (hB : 0 < B)
    (hg : ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
      ‖mrtMovingLFunction χ r t z‖ ≤ Real.exp B)
    (hσ : 1 < σ) (hσ2 : σ ≤ 1 + r)
    (hβ : 1 - r / 4 ≤ β) (hβ1 : β ≤ 1)
    (hz : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) = 0) :
    (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
      DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))).re ≤
        mrtCharacterLogDerivativeConstant * B / (3 * r) - 1 / (σ - β) := by
  let f := mrtMovingLFunction χ r t
  have hf := mrt_moving_LFunction_analytic χ hr ht
  have h0 := mrt_moving_LFunction_zero χ hr t
  have hzn := mrt_moving_real_point_norm hr (by linarith) hσ2
  have hn : DirichletCharacter.LFunction χ (mrtMovingPoint r t (mrtMovingRealPoint r σ)) ≠ 0 := by
    rw [mrt_moving_real_point hr]
    exact χ.LFunction_ne_zero_of_one_le_re (Or.inr (by
      intro he; have hre := congrArg Complex.re he; simp at hre; linarith)) (by simpa using hσ.le)
  have hfn : f (mrtMovingRealPoint r σ) ≠ 0 :=
    div_ne_zero hn (mrt_moving_point_center_ne_zero χ hr t)
  have he := mrt_disk_logderiv f hf h0 hB hg hzn hfn
  have hlow := (abs_le.mp ((Complex.abs_re_le_norm _).trans he)).1
  have hs := mrt_moving_selected_zero_sum χ hr ht hσ hβ hβ1 hz
  rw [Complex.sub_re, Complex.re_sum] at hlow
  rw [mrt_moving_logderiv_eq χ hr ht (hzn.trans (by norm_num)) hn,
    mrt_moving_real_point hr] at hlow
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hlow
  simp only [neg_div, Complex.neg_re]
  have h3 : 0 < 3 * r := by positivity
  have hdist : σ - β ≠ 0 := ne_of_gt (by linarith)
  have heq : mrtCharacterLogDerivativeConstant * B / (3 * r) - 1 / (σ - β) =
      (mrtCharacterLogDerivativeConstant * B - (3 * r) / (σ - β)) / (3 * r) := by
    field_simp [hr.ne', hdist]
  rw [heq]
  apply (le_div_iff₀ h3).mpr
  nlinarith only [hlow, hs]

end TwoPointCorrelations

end OAI
