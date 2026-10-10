import OAI.Analysis.KadisonKastler.ModularSpectralCuts

namespace OAI

/-! # Monotonicity of resolvent cuts

A smaller positive-part generator factors through every strictly larger
one. Its closed range is therefore contained in the larger closed range.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def cutFactor (r t s : ℝ) : ℝ := max (r - s) 0 / max (t - s) (t - r)

private theorem cutFactor_continuous {r t : ℝ} (hrt : r < t) :
    Continuous (cutFactor r t) := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro s
  exact ne_of_gt (lt_of_lt_of_le (sub_pos.mpr hrt) (le_max_right _ _))

private theorem cutFactor_identity {r t : ℝ} (hrt : r < t) (s : ℝ) :
    max (t - s) 0 * cutFactor r t s = max (r - s) 0 := by
  unfold cutFactor
  by_cases hs : s ≤ r
  · have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_lt hs hrt)
    rw [max_eq_left hts.le, max_eq_left (by linarith : t - r ≤ t - s)]
    exact mul_div_cancel₀ _ (ne_of_gt hts)
  · rw [max_eq_right (by linarith : r - s ≤ 0), zero_div, mul_zero]

theorem resolventCutGenerator_factor (R : H →L[ℂ] H) (r t : ℝ) (hrt : r < t) :
    resolventCutGenerator R r = resolventCutGenerator R t * cfc (cutFactor r t) R := by
  rw [resolventCutGenerator, resolventCutGenerator,
    ← cfc_mul (fun s : ℝ => max (t - s) 0) (cutFactor r t) R
      (by fun_prop) (cutFactor_continuous hrt).continuousOn]
  apply cfc_congr
  intro s _
  exact (cutFactor_identity hrt s).symm

theorem resolventCutGenerator_range_mono (R : H →L[ℂ] H) {r t : ℝ} (hrt : r ≤ t) :
    (resolventCutGenerator R r).range.topologicalClosure ≤
      (resolventCutGenerator R t).range.topologicalClosure := by
  rcases hrt.eq_or_lt with rfl | hrt
  · exact le_rfl
  apply Submodule.topologicalClosure_mono
  rintro _ ⟨x, rfl⟩
  refine ⟨cfc (cutFactor r t) R x, ?_⟩
  exact congrArg (fun T : H →L[ℂ] H => T x) (resolventCutGenerator_factor R r t hrt).symm

theorem resolventLowerCut_mul_of_le (R : H →L[ℂ] H) {r t : ℝ} (hrt : r ≤ t) :
    resolventLowerCut R r * resolventLowerCut R t = resolventLowerCut R r :=
  Submodule.starProjection_comp_starProjection_of_le (resolventCutGenerator_range_mono R hrt)

theorem resolventLowerCut_norm_mono (R : H →L[ℂ] H) (x : H) :
    Monotone (fun r : ℝ => ‖resolventLowerCut R r x‖) := by
  intro r t hrt
  calc
    _ = ‖resolventLowerCut R r (resolventLowerCut R t x)‖ := by
      exact congrArg (fun T : H →L[ℂ] H => ‖T x‖) (resolventLowerCut_mul_of_le R hrt).symm
    _ ≤ ‖resolventLowerCut R t x‖ := by
      simpa only [one_mul] using (resolventLowerCut R r).le_of_opNorm_le
        ((resolventLowerCut_projection R r).norm_le _) (resolventLowerCut R t x)

end

end KadisonKastler

end OAI
