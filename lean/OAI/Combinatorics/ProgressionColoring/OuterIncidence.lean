import OAI.Combinatorics.ProgressionColoring.OuterColoring

namespace OAI

universe uI uLabel

namespace QuantitativeVanDerWaerden

open scoped BigOperators

theorem outer_weight_le_of_support_lower {n : ℕ} {L : ℝ} (hL : L ≤ (n : ℝ)) :
    Real.exp (-(n : ℝ) / 32) ≤ Real.exp (-L / 32) := by
  apply Real.exp_le_exp.mpr
  linarith

theorem outer_weight_le_of_half_length {n h : ℕ} (hsize : h ≤ 2 * n) :
    Real.exp (-(n : ℝ) / 32) ≤ Real.exp (-(h : ℝ) / 64) := by
  have hsize' : (h : ℝ) ≤ 2 * n := by exact_mod_cast hsize
  apply Real.exp_le_exp.mpr
  linarith

theorem outer_total_weight_bound {I : Type uI} {Label : Type uLabel} (s : Finset I)
    (support : I → Finset Label) (L : ℝ)
    (hsize : ∀ i ∈ s, L ≤ ((support i).card : ℝ)) :
    ∑ i ∈ s, Real.exp (-((support i).card : ℝ) / 32) ≤
      s.card * Real.exp (-L / 32) := by
  calc
    (∑ i ∈ s, Real.exp (-((support i).card : ℝ) / 32)) ≤
        ∑ _i ∈ s, Real.exp (-L / 32) :=
      Finset.sum_le_sum fun i hi => outer_weight_le_of_support_lower (hsize i hi)
    _ = s.card * Real.exp (-L / 32) := by simp

/-- The anchored count through one label gives the local incident-weight
bound, after grouping actual pattern indices by their return period. -/
theorem outer_local_incident_bound {I : Type uI} {Label : Type uLabel} [Fintype I] [DecidableEq I]
    [DecidableEq Label] (support : I → Finset Label) (period : I → ℕ)
    (periods : Finset ℕ) (countBound : ℕ → ℕ)
    (hperiod : ∀ i, period i ∈ periods)
    (hsize : ∀ i, period i ≤ 2 * (support i).card)
    (hcount : ∀ b h,
      (Finset.univ.filter (fun i => b ∈ support i ∧ period i = h)).card ≤ countBound h)
    (b : Label) :
    ∑ i ∈ Finset.univ.filter (fun i => b ∈ support i),
        Real.exp (-((support i).card : ℝ) / 32) ≤
      ∑ h ∈ periods, (countBound h : ℝ) * Real.exp (-(h : ℝ) / 64) := by
  classical
  let incident := Finset.univ.filter (fun i => b ∈ support i)
  have hmap : ∀ i ∈ incident, period i ∈ periods := fun i _ => hperiod i
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_le_sum
  intro h hh
  have hcard : (incident.filter (fun i => period i = h)).card ≤ countBound h := by
    simpa only [incident, Finset.filter_filter] using hcount b h
  calc
    (∑ i ∈ incident.filter (fun i => period i = h),
        Real.exp (-((support i).card : ℝ) / 32)) ≤
        ∑ _i ∈ incident.filter (fun i => period i = h), Real.exp (-(h : ℝ) / 64) := by
      apply Finset.sum_le_sum
      intro i hi
      have hih : period i = h := (Finset.mem_filter.mp hi).2
      simpa only [hih] using outer_weight_le_of_half_length (hsize i)
    _ = ((incident.filter (fun i => period i = h)).card : ℝ) *
        Real.exp (-(h : ℝ) / 64) := by simp
    _ ≤ (countBound h : ℝ) * Real.exp (-(h : ℝ) / 64) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.exp_pos _).le

end QuantitativeVanDerWaerden

end OAI
