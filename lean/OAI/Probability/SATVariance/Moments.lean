import OAI.Probability.SATVariance.MarkovReplacement

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma real_rate_pos {k : ℕ} (hk : 1 ≤ k) : 0 < 1-((2 : ℝ)^k)⁻¹ := by
  have hp : (2 : ℝ) ≤ (2 : ℝ)^k := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk)
  exact sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr (by linarith))

lemma real_rate_lt_one (k : ℕ) : 1-((2 : ℝ)^k)⁻¹ < 1 := by
  have h : 0 < ((2 : ℝ)^k)⁻¹ := by positivity
  linarith

lemma measurable_natH (n k : ℕ) :
    Measurable (fun ω : Stream n k => (firstFailure ω).toNat) :=
  (measurable_of_countable fun x : ℕ∞ => x.toNat).comp (measurable_firstFailure n k)

lemma natH_mass_bound {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (m : ℕ) :
    ((streamLaw n k).map (fun ω => (firstFailure ω).toNat) {m}).toReal ≤
      ((2 : ℝ)^n/(1-((2 : ℝ)^k)⁻¹))*(1-((2 : ℝ)^k)⁻¹)^m := by
  let := streamLaw_probability n k hkn
  have hq := real_rate_pos hk
  rw [Measure.map_apply (measurable_natH n k) (by measurability)]
  cases m with
  | zero =>
    simp only [pow_zero, mul_one]
    apply (measureReal_le_one (μ := streamLaw n k)).trans
    apply (le_div_iff₀ hq).2
    have hp := one_le_pow₀ (n := n) (by norm_num : (1 : ℝ) ≤ 2)
    have hr := real_rate_lt_one k
    linarith
  | succ m =>
    have hs : (fun ω : Stream n k => (firstFailure ω).toNat) ⁻¹' {m+1} ⊆
        {ω | (m : ℕ∞) < firstFailure ω} := by
      intro ω hω
      have he : firstFailure ω = ((m+1 : ℕ) : ℕ∞) :=
        (ENat.toNat_eq_iff (by omega)).mp hω
      change (m : ℕ∞) < firstFailure ω
      rw [he]
      exact_mod_cast Nat.lt_succ_self m
    have hh := ENNReal.toReal_mono (by finiteness)
      ((measure_mono hs).trans (first_moment_tail hkn m))
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat, rate_toReal] at hh
    apply hh.trans_eq
    rw [pow_succ, ← mul_assoc, mul_right_comm, div_mul_cancel₀ _ hq.ne']

lemma H_integrable_pow {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (p : ℕ) :
    Integrable (fun ω : Stream n k => (H ω)^p) (streamLaw n k) := by
  let := streamLaw_probability n k hkn
  let ν := (streamLaw n k).map (fun ω => (firstFailure ω).toNat)
  have hp : IsProbabilityMeasure ν := inferInstance
  let q := 1-((2 : ℝ)^k)⁻¹
  have hq := real_rate_pos hk
  have hqNorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq]; exact real_rate_lt_one k
  have hs : Summable (fun m : ℕ => (ν {m}).toReal * ‖(m : ℝ)^p‖) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _
      ((summable_pow_mul_geometric_of_norm_lt_one p hqNorm).mul_left ((2 : ℝ)^n/q))
    intro m
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ)^p)]
    calc
      _ ≤ (((2 : ℝ)^n/q)*q^m)*(m : ℝ)^p :=
        mul_le_mul_of_nonneg_right (natH_mass_bound hk hkn m) (by positivity)
      _ = _ := by ring
  have hi : Integrable (fun m : ℕ => (m : ℝ)^p) ν := by
    rw [← Measure.sum_smul_dirac ν]
    exact integrable_sum_dirac (fun _ => measure_ne_top _ _) hs
  exact hi.comp_measurable (measurable_natH n k)

lemma H_memLp_two {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    MemLp (H : Stream n k → ℝ) 2 (streamLaw n k) :=
  (memLp_two_iff_integrable_sq (measurable_H n k).aestronglyMeasurable).mpr
    (H_integrable_pow hk hkn 2)

end RandomKSAT

end

end OAI
