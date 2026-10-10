import OAI.NumberTheory.EgyptianFractions.MajorArcApproximationBridge

namespace OAI
noncomputable section

namespace Problem337.MinorArc

/-- Enlarging the radius enlarges the explicit finite major-arc union. -/
theorem majorArcUnion_mono_radius (Q : ℕ) {δ ε : ℝ} (hδε : δ ≤ ε) :
    ThreePrimeAnalysis.majorArcUnion Q δ ⊆ ThreePrimeAnalysis.majorArcUnion Q ε := by
  intro x hx
  obtain ⟨q, hq, hqQ, a, haq, hnear⟩ :=
    ThreePrimeAnalysis.mem_majorArcUnion_iff.mp hx
  apply ThreePrimeAnalysis.mem_majorArcUnion_iff.mpr
  exact ⟨q, hq, hqQ, a, haq, hnear.trans
    (div_le_div_of_nonneg_right hδε (Nat.cast_nonneg q))⟩

/-- Dirichlet approximation in the real parameter window used by minor-arc
estimates. The scale is rounded only internally; the theorem exposes the
usable real inequalities `R ≤ q ≤ X/R` without floor losses. -/
theorem exists_minor_fraction_real_window {X R x : ℝ}
    (hR : 0 < R) (hXR : 4 * R ≤ X)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hminor : x ∉ ThreePrimeAnalysis.majorArcUnion ⌊R⌋₊ (2 * R / X)) :
    ∃ a : ℤ, ∃ q : ℕ, R ≤ (q : ℝ) ∧ (q : ℝ) ≤ X / R ∧ 0 < q ∧
      IsCoprime a (q : ℤ) ∧ |x - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
  have hX : 0 < X := by linarith
  let N : ℕ := ⌊X / R⌋₊
  have hY : 4 ≤ X / R := (le_div_iff₀ hR).mpr hXR
  have hN4 : 4 ≤ N := by
    apply Nat.le_floor
    exact hY
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNlow : (X / R) / 2 ≤ (N : ℝ) := by
    have hh := Nat.lt_floor_add_one (X / R)
    change X / R < (N : ℝ) + 1 at hh
    linarith
  have hNup : (N : ℝ) ≤ X / R := Nat.floor_le (by positivity)
  have hradius : 1 / (N : ℝ) ≤ 2 * R / X := by
    apply (div_le_div_iff₀ hNpos hX).mpr
    have hlow : X / R ≤ 2 * (N : ℝ) := by linarith
    have hh := (div_le_iff₀ hR).mp hlow
    nlinarith
  have hminor' : x ∉ ThreePrimeAnalysis.majorArcUnion ⌊R⌋₊ (1 / (N : ℝ)) := by
    intro hxmajor
    exact hminor (majorArcUnion_mono_radius ⌊R⌋₊ hradius hxmajor)
  obtain ⟨a, q, hqR, hqN, hq, hcop, _hnear, hsq⟩ :=
    exists_minor_fraction_of_not_mem_majorArcUnion (by omega : 2 ≤ N) hx hminor'
  refine ⟨a, q, ?_, (by exact_mod_cast hqN : (q : ℝ) ≤ N).trans hNup,
    hq, hcop, hsq⟩
  have hh := Nat.lt_floor_add_one R
  have hfq : (⌊R⌋₊ : ℝ) + 1 ≤ q := by exact_mod_cast hqR
  exact (hh.trans_le hfq).le

end Problem337.MinorArc

end

end OAI
