import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraBandGeometry

namespace OAI

/-! Reciprocal mass in the additional large-prime interval. The exact
logarithmic ratio and the small mass allow a short Bonferroni truncation. -/

namespace TwoPointCorrelations

open Filter Finset

lemma mrt_extra_prime_ratio {L : ℝ} (hL : 1 < L) :
    Real.log (mrtExtraPrimeLower L)/Real.log (mrtExtraPrimeUpper L) =
      2*Real.log L/L^(1/80:ℝ) := by
  have hL0 : 0 < L := by linarith
  have hlog : 0 < Real.log L := Real.log_pos hL
  have hp := Real.rpow_pos_of_pos hL0 (1/80)
  have he : L^(79/80:ℝ)*L^(1/80:ℝ)=L := by
    rw [← Real.rpow_add hL0]
    norm_num
  simp only [mrtExtraPrimeLower,mrtExtraPrimeUpper,Real.log_exp]
  field_simp [hL0.ne',hlog.ne',hp.ne']
  nlinarith [congrArg (fun x : ℝ => 2*Real.log L*x) he]

theorem mrt_extra_prime_mass :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ mrtExtraPrimeLower L ∧
      (∑ p ∈ mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L),
        1/(p:ℝ)) ≤ (1/50:ℝ)*Real.log L := by
  obtain ⟨C,hC,hM⟩ := mrt_prime_band_mertens
  filter_upwards [mrt_extra_band_geometry,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (200*C)))]
    with L hg hL hlog
  have hL0 : 0 < L := by linarith
  have hlog1 : 1 ≤ Real.log L := (le_max_left _ _).trans hlog
  have hlog0 : 0 < Real.log L := by linarith
  have hLC : 200*C ≤ Real.log L := (le_max_right _ _).trans hlog
  have hpow : 1 ≤ L^(79/80:ℝ) := Real.one_le_rpow hL (by norm_num)
  have hP : 2 ≤ mrtExtraPrimeLower L := by
    have hh := Real.add_one_le_exp (2*L^(79/80:ℝ))
    change 2 ≤ Real.exp (2*L^(79/80:ℝ))
    linarith
  refine ⟨hP,?_⟩
  have hm := (abs_le.mp (hM (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
    hP hg.2.2.1)).2
  have hmain : Real.log (Real.log (mrtExtraPrimeUpper L))-
      Real.log (Real.log (mrtExtraPrimeLower L)) ≤ (1/80:ℝ)*Real.log L := by
    simp only [mrtExtraPrimeUpper,mrtExtraPrimeLower,Real.log_exp]
    rw [Real.log_div hL0.ne' hlog0.ne',
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (Real.rpow_pos_of_pos hL0 _).ne',
      Real.log_rpow hL0]
    have hll := Real.log_nonneg hlog1
    have htwo := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
    linarith
  linarith

end TwoPointCorrelations

end OAI
