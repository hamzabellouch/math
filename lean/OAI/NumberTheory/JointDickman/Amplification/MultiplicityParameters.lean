import OAI.NumberTheory.JointDickman.Amplification.SmallCandidateMultiplicity

namespace OAI

/-! # Choosing the grid and tolerance for the small-addition estimate -/

namespace JointDickman
open Filter
open scoped Topology

theorem smallMultiplicityExponent_tendsto (L : ℕ) :
    Tendsto (smallMultiplicityExponent L) (𝓝 0) (𝓝 ((6 : ℝ)/L*Real.log 2)) := by
  change Tendsto (fun τ : ℝ => ((6 : ℝ)/L+4*τ)*Real.log 2+2*highOmissionExponent τ) _ _
  have hh := (((tendsto_const_nhds (x := (6 : ℝ)/L)).add (tendsto_id.const_mul (4 : ℝ))).mul_const (Real.log 2)).add
    (highOmissionExponent_tendsto.const_mul (2 : ℝ))
  simpa [smallMultiplicityExponent] using hh

/-- The order is a fixed sufficiently fine grid, then a positive tolerance.
No arithmetic or probabilistic premise is used in this choice. -/
theorem exists_small_multiplicity_tolerance {L : ℕ} (hL : 10000 ≤ L) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ samplingTau ∧ smallMultiplicityExponent L τ < 8/1000 := by
  have hLr : (10000 : ℝ) ≤ L := by exact_mod_cast hL
  have hlog : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ)-1 = 1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hb : (6 : ℝ)/L*Real.log 2 < 8/1000 := by
    have hd : (6 : ℝ)/L ≤ 6/10000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hLr
    have hp : 0 ≤ (6 : ℝ)/L := div_nonneg (by norm_num) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hlog hp]
  have he := (smallMultiplicityExponent_tendsto L).eventually (Iio_mem_nhds hb)
  obtain ⟨δ,hδ,hbound⟩ := Metric.eventually_nhds_iff.mp he
  let τ := min (δ/2) (samplingTau/2)
  have hsampling : 0 < samplingTau := by norm_num [samplingTau]
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  refine ⟨τ,hτ,?_,?_⟩
  · exact (min_le_right _ _).trans (by linarith)
  · apply hbound
    rw [Real.dist_eq,sub_zero,abs_of_pos hτ]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

theorem smallCandidateAlternatives_power_bound {L : ℕ} (hL : 3 ≤ L)
    {τ : ℝ} (hτ : 0 < τ) (hτsmall : τ ≤ samplingTau)
    (he : smallMultiplicityExponent L τ ≤ 8/1000) :
    ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C : ℝ) (i k : Fin M) (A D U V : Finset ℕ),
      RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D →
      RegularPrimeSet B L τ C U → RegularPrimeSet B L τ C V →
      ((smallCandidateAlternatives B L T H τ C i k A D U V).card : ℝ) ≤
        (B : ℝ)^(8/1000 : ℝ) := by
  have hsmall : τ ≤ 1/100 := hτsmall.trans (by norm_num [samplingTau])
  filter_upwards [smallCandidateAlternatives_rpow_bound hL hτ hsmall, eventually_ge_atTop 1] with B hB hB1
  intro T H M C i k A D U V hA hD hU hV
  exact (hB T H M C i k A D U V hA hD hU hV).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hB1) he)

end JointDickman

end OAI
