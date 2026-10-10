import Mathlib

namespace OAI

noncomputable section

namespace Problem313

/-- The derivative of log odds, stated without any probability-specific definitions. -/
theorem hasDerivAt_log_odds {μ : ℝ → ℝ} {d x : ℝ}
    (hd : HasDerivAt μ d x) (hpos : 0 < μ x) (hone : μ x < 1) :
    HasDerivAt (fun t => Real.log (μ t) - Real.log (1 - μ t))
      (d / (μ x * (1 - μ x))) x := by
  have hne : μ x ≠ 0 := ne_of_gt hpos
  have hne' : 1 - μ x ≠ 0 := ne_of_gt (sub_pos.mpr hone)
  convert! (hd.log hne).sub (((hasDerivAt_const x (1 : ℝ)).sub hd).log hne') using 1
  dsimp only [Pi.sub_apply]
  field_simp
  ring

/-- Integrating a logistic differential inequality by the mean value theorem.
Continuity is needed on the closed interval, differentiability only in its interior. -/
theorem logistic_coordinate_width {μ μ' : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hcont : ContinuousOn μ (Set.Icc a b))
    (hμ : ∀ x ∈ Set.Icc a b, 0 < μ x ∧ μ x < 1)
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt μ (μ' x) x)
    (hbound : ∀ x ∈ Set.Ioo a b, μ x * (1 - μ x) ≤ C * μ' x) :
    b - a ≤ C * ((Real.log (μ b) - Real.log (1 - μ b)) -
      (Real.log (μ a) - Real.log (1 - μ a))) := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · subst b
    simp
  let g : ℝ → ℝ := fun x => C * (Real.log (μ x) - Real.log (1 - μ x))
  let g' : ℝ → ℝ := fun x => C * (μ' x / (μ x * (1 - μ x)))
  have hg : ContinuousOn g (Set.Icc a b) := by
    apply ContinuousOn.const_mul
    exact (hcont.log (fun x hx => ne_of_gt (hμ x hx).1)).sub
      ((continuousOn_const.sub hcont).log
        (fun x hx => ne_of_gt (sub_pos.mpr (hμ x hx).2)))
  have hgd : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x := by
    intro x hx
    have hμx := hμ x (Set.Ioo_subset_Icc_self hx)
    exact (hasDerivAt_log_odds (hd x hx) hμx.1 hμx.2).const_mul C
  obtain ⟨x, hx, hslope⟩ := exists_hasDerivAt_eq_slope g g' hlt hg hgd
  have hμx := hμ x (Set.Ioo_subset_Icc_self hx)
  have hden : 0 < μ x * (1 - μ x) := mul_pos hμx.1 (sub_pos.mpr hμx.2)
  have hg' : 1 ≤ g' x := by
    dsimp [g']
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hden).2 (by simpa using hbound x hx)
  rw [hslope] at hg'
  have hle := (le_div_iff₀ (sub_pos.mpr hlt)).1 hg'
  dsimp [g] at hle
  linarith

/-- The symmetric endpoint form used in sharp-threshold estimates. -/
theorem logistic_width_of_hasDerivAt {μ μ' : ℝ → ℝ} {a b C ε : ℝ}
    (hab : a ≤ b) (hε : 0 < ε) (hεone : ε < 1)
    (hcont : ContinuousOn μ (Set.Icc a b))
    (hμ : ∀ x ∈ Set.Icc a b, 0 < μ x ∧ μ x < 1)
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt μ (μ' x) x)
    (hbound : ∀ x ∈ Set.Ioo a b, μ x * (1 - μ x) ≤ C * μ' x)
    (ha : μ a = ε) (hb : μ b = 1 - ε) :
    b - a ≤ 2 * C * Real.log ((1 - ε) / ε) := by
  have h := logistic_coordinate_width hab hcont hμ hd hbound
  rw [ha, hb] at h
  have hsub : 1 - (1 - ε) = ε := by ring
  rw [hsub] at h
  rw [Real.log_div (ne_of_gt (sub_pos.mpr hεone)) (ne_of_gt hε)]
  linarith

end Problem313

end

end OAI
