import Mathlib

namespace OAI

noncomputable section

namespace Problem313

/-- A continuous strictly increasing distribution on the unit interval attains
its infimum-defined quantiles at unique interior points. -/
theorem quantile_attainment_of_strictMonoOn
    {μ : ℝ → ℝ} (hcont : ContinuousOn μ (Set.Icc 0 1))
    (hmono : StrictMonoOn μ (Set.Icc 0 1))
    (hzero : μ 0 = 0) (hone : μ 1 = 1)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    let q := sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p}
    q ∈ Set.Ioo (0 : ℝ) 1 ∧ μ q = a := by
  have ha : a ∈ Set.Icc (μ 0) (μ 1) := by
    rw [hzero, hone]
    exact ⟨ha0.le, ha1.le⟩
  obtain ⟨r, hr, hra⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont ha
  have hr0 : 0 < r := by
    by_contra h
    have heq : r = 0 := le_antisymm (le_of_not_gt h) hr.1
    rw [heq, hzero] at hra
    linarith
  have hr1 : r < 1 := by
    by_contra h
    have heq : r = 1 := le_antisymm hr.2 (le_of_not_gt h)
    rw [heq, hone] at hra
    linarith
  have hset : {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p} = Set.Icc r 1 := by
    ext p
    constructor
    · rintro ⟨hp, hap⟩
      refine ⟨?_, hp.2⟩
      by_contra h
      have hlt := hmono hp hr (lt_of_not_ge h)
      rw [hra] at hlt
      exact (not_lt_of_ge hap) hlt
    · intro hp
      have hpunit : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hr.1.trans hp.1, hp.2⟩
      refine ⟨hpunit, ?_⟩
      rw [← hra]
      exact hmono.monotoneOn hr hpunit hp.1
  dsimp only
  rw [hset, csInf_Icc hr.2]
  exact ⟨⟨hr0, hr1⟩, hra⟩

/-- Positive derivatives in the interior imply the strict monotonicity required
by the quantile attainment theorem; endpoints only require continuity. -/
theorem strictMonoOn_unit_of_hasDerivAt_pos
    {μ D : ℝ → ℝ} (hcont : ContinuousOn μ (Set.Icc 0 1))
    (hderiv : ∀ p ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt μ (D p) p)
    (hpos : ∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < D p) :
    StrictMonoOn μ (Set.Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) hcont
  intro p hp
  have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hp
  rw [(hderiv p hp').deriv]
  exact hpos p hp'

/-- The quantile width estimate in derivative form. -/
theorem quantile_attainment_of_hasDerivAt_pos
    {μ D : ℝ → ℝ} (hcont : ContinuousOn μ (Set.Icc 0 1))
    (hderiv : ∀ p ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt μ (D p) p)
    (hpos : ∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < D p)
    (hzero : μ 0 = 0) (hone : μ 1 = 1)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    let q := sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p}
    q ∈ Set.Ioo (0 : ℝ) 1 ∧ μ q = a :=
  quantile_attainment_of_strictMonoOn hcont
    (strictMonoOn_unit_of_hasDerivAt_pos hcont hderiv hpos) hzero hone ha0 ha1

end Problem313

end

end OAI
