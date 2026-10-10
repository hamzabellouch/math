import OAI.NumberTheory.EgyptianFractions.MinorArcMeasure
import OAI.NumberTheory.EgyptianFractions.RationalArcVolume

namespace OAI
noncomputable section

namespace Problem337.MinorArc

/-- The elementary finite-window radius agrees with the variable-radius API. -/
theorem rationalWindow_eq_rationalArc (N q a : ℕ) :
    rationalWindow N q a = ThreePrimeAnalysis.rationalArc q a (1 / (N : ℝ)) := by
  simp only [rationalWindow, ThreePrimeAnalysis.rationalArc, div_div, mul_comm]

/-- Reduced Dirichlet neighborhoods on the unit interval are contained in
exactly the finite major-arc union used by the integral error estimates. -/
theorem majorArcs_unit_subset_majorArcUnion {Q N : ℕ} (hN : 2 ≤ N) :
    majorArcs Q N ∩ Set.Icc (0 : ℝ) 1 ⊆
      ThreePrimeAnalysis.majorArcUnion Q (1 / (N : ℝ)) := by
  simpa only [ThreePrimeAnalysis.majorArcUnion, rationalWindow_eq_rationalArc] using
    majorArcs_unit_subset (Q := Q) hN

/-- Removing reduction from the displayed major-arc centers does not enlarge
the union beyond the reduced-rational Dirichlet major arcs. -/
theorem majorArcUnion_subset_majorArcs {Q N : ℕ} (hN : 0 < N) :
    ThreePrimeAnalysis.majorArcUnion Q (1 / (N : ℝ)) ⊆ majorArcs Q N := by
  intro x hx
  obtain ⟨q, hq, hqQ, a, _ha, hnear⟩ :=
    ThreePrimeAnalysis.mem_majorArcUnion_iff.mp hx
  let r : ℚ := (a : ℚ) / q
  have hdenDvd : r.den ∣ q := by
    have h := Rat.den_dvd (a : ℤ) (q : ℤ)
    rw [← Rat.intCast_div_eq_divInt] at h
    simpa only [Int.cast_natCast, Int.natCast_dvd_natCast] using h
  have hdenle : r.den ≤ q := Nat.le_of_dvd (by omega) hdenDvd
  refine ⟨r, hdenle.trans hqQ, ?_⟩
  have hr : (r : ℝ) = (a : ℝ) / q := by simp [r]
  change |x - (r : ℝ)| ≤ 1 / ((r.den : ℝ) * N)
  rw [hr]
  apply hnear.trans
  rw [div_div, mul_comm (N : ℝ) (q : ℝ)]
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  exact one_div_le_one_div_of_le (mul_pos hd hn)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hdenle) hn.le)

/-- The two major-arc conventions are identical after restricting to `[0,1]`. -/
theorem majorArcs_unit_eq_majorArcUnion_unit {Q N : ℕ} (hN : 2 ≤ N) :
    majorArcs Q N ∩ Set.Icc (0 : ℝ) 1 =
      ThreePrimeAnalysis.majorArcUnion Q (1 / (N : ℝ)) ∩ Set.Icc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨majorArcs_unit_subset_majorArcUnion hN hx, hx.2⟩
  · intro x hx
    exact ⟨majorArcUnion_subset_majorArcs (by omega) hx.1, hx.2⟩

/-- Outside the finite major arcs used for integration, Dirichlet gives an
actual reduced approximation in the minor-arc denominator window. -/
theorem exists_minor_fraction_of_not_mem_majorArcUnion {Q N : ℕ}
    (hN : 2 ≤ N) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hminor : x ∉ ThreePrimeAnalysis.majorArcUnion Q (1 / (N : ℝ))) :
    ∃ a : ℤ, ∃ q : ℕ, Q < q ∧ q ≤ N ∧ 0 < q ∧
      IsCoprime a (q : ℤ) ∧
      |x - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * N) ∧
      |x - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
  apply exists_minor_coprime_fraction x (by omega)
  intro hxmajor
  exact hminor (majorArcs_unit_subset_majorArcUnion hN ⟨hxmajor, hx⟩)

end Problem337.MinorArc

end

end OAI
