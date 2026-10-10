import OAI.NumberTheory.EgyptianFractions.MajorArcApproximationBridge

namespace OAI
noncomputable section
open MeasureTheory

namespace Problem337.MinorArc

/-- Reduction of a displayed natural fraction cannot increase its denominator. -/
theorem displayed_fraction_den_le (a q : ℕ) (hq : 0 < q) :
    ((a : ℚ) / q).den ≤ q := by
  apply Nat.le_of_dvd hq
  have h := Rat.den_dvd (a : ℤ) (q : ℤ)
  simpa only [Rat.divInt_eq_div, Int.cast_natCast, Int.natCast_dvd_natCast] using h

/-- The finite nonreduced union is contained in the reduced-rational union.
No restriction to the unit interval is needed in this direction. -/
theorem finite_majorArcs_subset (Q N : ℕ) :
    ThreePrimeAnalysis.majorArcUnion Q (1 / (N : ℝ)) ⊆ majorArcs Q N := by
  intro x hx
  obtain ⟨q, hq, hqQ, a, haq, hnear⟩ :=
    ThreePrimeAnalysis.mem_majorArcUnion_iff.mp hx
  let r : ℚ := (a : ℚ) / q
  have hden : r.den ≤ q := displayed_fraction_den_le a q hq
  refine ⟨r, hden.trans hqQ, ?_⟩
  change |x - (r : ℝ)| ≤ 1 / ((r.den : ℝ) * N)
  have hr : (r : ℝ) = (a : ℝ) / q := by simp [r]
  rw [hr]
  apply hnear.trans
  rw [div_div, mul_comm (N : ℝ)]
  by_cases hN : N = 0
  · simp [hN]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hdpos : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  apply one_div_le_one_div_of_le (mul_pos hdpos hNpos)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hden) hNpos.le

/-- On the unit interval the reduced-rational and finite nonreduced
major arcs coincide, so their Dirichlet and integration APIs can be combined. -/
theorem majorArcs_unit_eq_finite {Q N : ℕ} (hN : 2 ≤ N) :
    majorArcs Q N ∩ Set.Icc (0 : ℝ) 1 =
      ThreePrimeAnalysis.majorArcUnion Q (1 / (N : ℝ)) ∩ Set.Icc (0 : ℝ) 1 :=
  majorArcs_unit_eq_majorArcUnion_unit hN

/-- The exact bridge transfers the uniform integration budget to the actual
reduced-rational major arcs used in Dirichlet extraction. -/
theorem norm_integral_majorArcs_unit_le {Q N : ℕ} (hN : 2 ≤ N)
    {B : ℝ} (hB : 0 ≤ B) (f : ℝ → ℂ)
    (hf : ∀ x ∈ majorArcs Q N ∩ Set.Icc (0 : ℝ) 1, ‖f x‖ ≤ B) :
    ‖∫ x in majorArcs Q N ∩ Set.Icc (0 : ℝ) 1, f x‖ ≤
      4 * B * (Q : ℝ) / N := by
  have hsubset : majorArcs Q N ∩ Set.Icc (0 : ℝ) 1 ⊆
      ThreePrimeAnalysis.majorArcUnion Q (1 / (N : ℝ)) := by
    rw [majorArcs_unit_eq_finite hN]
    exact Set.inter_subset_left
  have h := ThreePrimeAnalysis.norm_integral_majorArcs_le Q
    (by positivity : 0 ≤ 1 / (N : ℝ)) hB hsubset f hf
  convert h using 1; ring

/-- The cubic major-arc error bound in the reduced-rational interface. -/
theorem norm_integral_cubic_majorArcs_unit_error_le {Q N : ℕ} (hN : 2 ≤ N)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε) (f g phase : ℝ → ℂ)
    (hf : ∀ x ∈ majorArcs Q N ∩ Set.Icc (0 : ℝ) 1, ‖f x‖ ≤ B)
    (hg : ∀ x ∈ majorArcs Q N ∩ Set.Icc (0 : ℝ) 1, ‖g x‖ ≤ B)
    (herr : ∀ x ∈ majorArcs Q N ∩ Set.Icc (0 : ℝ) 1, ‖f x - g x‖ ≤ ε)
    (hphase : ∀ x ∈ majorArcs Q N ∩ Set.Icc (0 : ℝ) 1, ‖phase x‖ ≤ 1) :
    ‖∫ x in majorArcs Q N ∩ Set.Icc (0 : ℝ) 1,
      (f x ^ 3 - g x ^ 3) * phase x‖ ≤ 12 * (Q : ℝ) * B ^ 2 * ε / N := by
  have hsubset : majorArcs Q N ∩ Set.Icc (0 : ℝ) 1 ⊆
      ThreePrimeAnalysis.majorArcUnion Q (1 / (N : ℝ)) := by
    rw [majorArcs_unit_eq_finite hN]
    exact Set.inter_subset_left
  have h := ThreePrimeAnalysis.norm_integral_cubic_majorArc_error_le Q
    (by positivity : 0 ≤ 1 / (N : ℝ)) hB hε hsubset f g phase hf hg herr hphase
  convert h using 1; ring

end Problem337.MinorArc

end

end OAI
