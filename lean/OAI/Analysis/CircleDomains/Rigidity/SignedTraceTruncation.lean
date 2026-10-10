import OAI.Analysis.CircleDomains.Rigidity.TraceTruncationLimits

namespace OAI

/-! Signed smooth truncations for zero-trace differences of scalar tests. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def signedTraceTruncation (δ t : ℝ) : ℝ :=
  smoothTraceTruncation δ t - smoothTraceTruncation δ (-t)

 theorem signedTraceTruncation_contDiff (δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (signedTraceTruncation δ) :=
  (smoothTraceTruncation_contDiff δ).sub
    ((smoothTraceTruncation_contDiff δ).comp contDiff_id.neg)

 theorem signedTraceTruncation_deriv (δ t : ℝ) :
    deriv (signedTraceTruncation δ) t = deriv (smoothTraceTruncation δ) t +
      deriv (smoothTraceTruncation δ) (-t) := by
  have hd := (smoothTraceTruncation_contDiff δ).differentiable (by simp)
  have he := (hd t).hasDerivAt.sub ((hd (-t)).hasDerivAt.comp t (hasDerivAt_neg t))
  calc
    _ = deriv (smoothTraceTruncation δ) t - deriv (smoothTraceTruncation δ) (-t) * (-1) := he.deriv
    _ = _ := by ring

 theorem signedTraceTruncation_zero {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ δ) :
    signedTraceTruncation δ t = 0 := by
  rw [signedTraceTruncation, smoothTraceTruncation_zero hδ (abs_le.mp ht).2,
    smoothTraceTruncation_zero hδ (by linarith [(abs_le.mp ht).1])]
  exact sub_self _

 theorem signedTraceTruncation_deriv_zero {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ δ) :
    deriv (signedTraceTruncation δ) t = 0 := by
  rw [signedTraceTruncation_deriv, smoothTraceTruncation_deriv_zero hδ (abs_le.mp ht).2,
    smoothTraceTruncation_deriv_zero hδ (by linarith [(abs_le.mp ht).1])]
  exact add_zero _

 theorem signedTraceTruncation_norm_le {δ t : ℝ} (hδ : 0 < δ) :
    ‖signedTraceTruncation δ t‖ ≤ ‖t‖ := by
  by_cases ht : 0 ≤ t
  · rw [signedTraceTruncation, smoothTraceTruncation_zero (t := -t) hδ (by linarith), sub_zero,
      Real.norm_eq_abs, abs_of_nonneg (smoothTraceTruncation_mem ht).1,
      Real.norm_eq_abs, abs_of_nonneg ht]
    exact (smoothTraceTruncation_mem ht).2
  · have ht' : 0 ≤ -t := by linarith
    rw [signedTraceTruncation, smoothTraceTruncation_zero (t := t) hδ (by linarith), zero_sub,
      norm_neg, Real.norm_eq_abs, abs_of_nonneg (smoothTraceTruncation_mem ht').1,
      Real.norm_eq_abs, abs_of_nonpos (le_of_not_ge ht)]
    exact (smoothTraceTruncation_mem ht').2

 theorem signedTraceTruncation_uniform_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∀ t : ℝ,
      ‖deriv (signedTraceTruncation δ) t‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := smoothTraceTruncation_uniform_deriv_bound
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro δ hδ t
  rw [signedTraceTruncation_deriv]
  exact (norm_add_le _ _).trans (by linarith [hbound δ hδ t, hbound δ hδ (-t)])

 theorem signedTraceTruncation_tendsto {δ : ℕ → ℝ}
    (hδ : ∀ n, 0 < δ n) (hl : Tendsto δ atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => signedTraceTruncation (δ n) t) atTop (𝓝 t) := by
  by_cases ht : 0 ≤ t
  · have hz : ∀ n, smoothTraceTruncation (δ n) (-t) = 0 :=
      fun n => smoothTraceTruncation_zero (hδ n) (by linarith [hδ n])
    simpa only [signedTraceTruncation, hz, sub_zero] using smoothTraceTruncation_tendsto hδ hl ht
  · have hz : ∀ n, smoothTraceTruncation (δ n) t = 0 :=
      fun n => smoothTraceTruncation_zero (hδ n) (by linarith [hδ n])
    simpa only [signedTraceTruncation, hz, zero_sub, neg_neg] using
      (smoothTraceTruncation_tendsto hδ hl (show 0 ≤ -t by linarith)).neg

 theorem signedTraceTruncation_deriv_tendsto {δ : ℕ → ℝ}
    (hδ : ∀ n, 0 < δ n) (hl : Tendsto δ atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => deriv (signedTraceTruncation (δ n)) t) atTop
      (𝓝 (if t = 0 then 0 else 1)) := by
  by_cases ht : 0 ≤ t
  · have hz : ∀ n, deriv (smoothTraceTruncation (δ n)) (-t) = 0 :=
      fun n => smoothTraceTruncation_deriv_zero (hδ n) (by linarith [hδ n])
    simpa only [signedTraceTruncation_deriv, hz, add_zero] using
      smoothTraceTruncation_deriv_tendsto hδ hl ht
  · have hz : ∀ n, deriv (smoothTraceTruncation (δ n)) t = 0 :=
      fun n => smoothTraceTruncation_deriv_zero (hδ n) (by linarith [hδ n])
    simpa only [signedTraceTruncation_deriv, hz, zero_add, neg_eq_zero] using
      smoothTraceTruncation_deriv_tendsto hδ hl (show 0 ≤ -t by linarith)

end CircleDomainRigidity

end

end OAI
