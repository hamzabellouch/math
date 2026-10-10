import OAI.MeasureTheory.SelfSimilar.NoOverlaps

namespace OAI

universe uι

open MeasureTheory

namespace EntropyRateDimension.Extensions

/-- Constant ratios need only one type in the entropy-gap contradiction. -/
theorem homogeneous_exponent_lower_direct {ι : Type uι} [Fintype ι] [Nonempty ι]
    (S : System ι) {lam : ℝ} (hr : ∀ i, S.ratio i = lam)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ) :
    min 1 (S.entropyRate / S.lyapunov) ≤ Coding.exponent S := by
  classical
  by_contra! hstrict
  obtain ⟨d, hed, hdm⟩ := exists_between hstrict
  have hd : 0 ≤ d := (Coding.exponent_nonneg S).trans hed.le
  have hd1 : d < 1 := hdm.trans_le (min_le_left _ _)
  have hdr : d < S.entropyRate / S.lyapunov := hdm.trans_le (min_le_right _ _)
  have hdh : d * S.lyapunov < S.entropyRate := (lt_div_iff₀ S.lyapunov_pos).mp hdr
  obtain ⟨a, hχa, hda⟩ := exists_slightly_larger_depth hd hdh
  have hap : 0 < a := S.lyapunov_pos.trans hχa
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨C, hC⟩ := S.selfSimilar_entropy_bound μ hμ hed
  apply Typed.no_strict_entropy_gap S (fun _ : ι => ())
    (fun i j _ => (hr i).trans (hr j).symm) μ hμ hd hd1 hap
    (A' := (S.lyapunov + a) / 2) (by linarith) (by linarith) hC
  simpa using mul_lt_mul_of_pos_right hda hl


/-- Same hypotheses and conclusion as homogeneous_dimension; independent proof branch. -/
theorem homogeneous_dimension_direct {ι : Type uι} [Fintype ι] [Nonempty ι] (S : System ι)
    {lam : ℝ} (hlam : 0 < lam) (hr : ∀ i, S.ratio i = lam)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (h : NoExactOverlaps S) :
    lowerHausdorffDimension μ =
      ENNReal.ofReal (min 1 (symbolEntropy S / Real.log (1/lam))) := by
  rw [← homogeneous_naturalLyapunov S hlam hr]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn : 0 < naturalLyapunov S := by
    have hp := S.lyapunov_pos
    rw [lyapunov_eq_naturalLyapunov] at hp
    exact (div_pos_iff_of_pos_right hlog).mp hp
  have hu : Coding.exponent S ≤ symbolEntropy S / naturalLyapunov S := by
    apply (le_div_iff₀ hn).mpr
    have hb := Coding.exponent_symbol_entropy_bound S
    change Coding.exponent S * S.lyapunov * Real.log 2 ≤ symbolEntropy S at hb
    rw [lyapunov_eq_naturalLyapunov] at hb
    have hc : Coding.exponent S * (naturalLyapunov S / Real.log 2) * Real.log 2 =
        Coding.exponent S * naturalLyapunov S := by
      field_simp [hlog.ne']
    rwa [hc] at hb
  have hl := homogeneous_exponent_lower_direct S hr μ hμ
  rw [entropyRate_eq_symbolEntropy S (noExactOverlaps_sameLength S h),
    lyapunov_eq_naturalLyapunov, div_div_div_cancel_right₀ hlog.ne'] at hl
  rw [S.selfSimilar_dimension μ hμ]
  exact congrArg ENNReal.ofReal (le_antisymm (le_min (S.exponent_le_one μ hμ) hu) hl)

end EntropyRateDimension.Extensions

end OAI
