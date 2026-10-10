import OAI.Analysis.CircleDomains.Selection.GoodSample
import OAI.Analysis.CircleDomains.Transfer.GridSummability

namespace OAI

/-!
# Selecting a compatible grid with small costs

This is the numerical selection step in `047-02`, Section 2. A small
expected wedge cost and a terminal count whose scaled expectation tends
to zero give a positive grid spacing and a compatible sample for which
both realized costs are small. The random staircase and its compatibility
conditions are explicit hypotheses of this selection theorem.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

/-- The terminal expectation tends to zero after multiplication by `h²`
when it is bounded by the finite clipped-product estimate from the paper. -/
theorem scaled_terminal_mean_tendsto_zero_of_bound
    {X κ τ ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (J : ℝ → X → ℝ) (F : Finset κ) (P : Finset τ) (a b : τ → ι → ℝ)
    (ha : ∀ p ∈ P, ∀ s, 0 ≤ a p s) (hb : ∀ p ∈ P, ∀ s, 0 ≤ b p s)
    (ha2 : ∀ p ∈ P, Summable (fun s => a p s ^ 2))
    (hb2 : ∀ p ∈ P, Summable (fun s => b p s ^ 2))
    (hJ0 : ∀ h, 0 < h → ∀ᵐ x ∂μ, 0 ≤ J h x)
    (hbound : ∀ᶠ h : ℝ in 𝓝[>] 0,
      h ^ 2 * (∫ x, J h x ∂μ) ≤ h ^ 2 * (F.card : ℝ) +
        ∑ p ∈ P, ∑' s, min h (a p s) * min h (b p s)) :
    Tendsto (fun h : ℝ => h ^ 2 * (∫ x, J h x ∂μ)) (𝓝[>] 0) (𝓝 0) := by
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have hnonneg : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 ≤ h ^ 2 * (∫ x, J h x ∂μ) := by
    filter_upwards [hpos] with h hh
    exact mul_nonneg (sq_nonneg h) (integral_nonneg_of_ae (hJ0 h hh))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (terminal_mean_bound_tendsto_zero F P a b ha hb ha2 hb2) hnonneg hbound

/-- Choose an arbitrarily small positive grid spacing and a compatible
sample with wedge cost below `η` and scaled square-root terminal count
below `η`. The probability-space event may encode all compatibility
conditions needed by the geometric construction. -/
theorem exists_compatible_good_grid {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ]
    (W J : ℝ → X → ℝ) (P : ℝ → X → Prop) {η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ)
    (hWi : ∀ h, 0 < h → Integrable (W h) μ)
    (hJi : ∀ h, 0 < h → Integrable (J h) μ)
    (hW0 : ∀ h, 0 < h → ∀ᵐ x ∂μ, 0 ≤ W h x)
    (hJ0 : ∀ h, 0 < h → ∀ᵐ x ∂μ, 0 ≤ J h x)
    (hP : ∀ h, 0 < h → ∀ᵐ x ∂μ, P h x)
    (hWmean : ∀ᶠ h : ℝ in 𝓝[>] 0, (∫ x, W h x ∂μ) < η / 4)
    (hJmean : Tendsto (fun h : ℝ => h ^ 2 * (∫ x, J h x ∂μ))
      (𝓝[>] 0) (𝓝 0)) :
    ∃ h : ℝ, 0 < h ∧ h < δ ∧ ∃ x, P h x ∧ W h x < η ∧
      h * Real.sqrt (J h x) < η := by
  have hη2 : 0 < η ^ 2 := sq_pos_of_pos hη
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0,
      0 < h ∧ h < δ ∧ (∫ x, W h x ∂μ) < η / 4 ∧
        h ^ 2 * (∫ x, J h x ∂μ) < η ^ 2 / 4 := by
    filter_upwards [hpos, hid.eventually_lt_const hδ, hWmean,
      hJmean.eventually_lt_const (by positivity : 0 < η ^ 2 / 4)]
      with h hh hd hw hj
    exact ⟨hh, hd, hw, hj⟩
  obtain ⟨h, hh, hd, hw, hj⟩ := hsmall.exists
  have hGi : Integrable (fun x => h ^ 2 * J h x) μ := (hJi h hh).const_mul _
  have hG0 : ∀ᵐ x ∂μ, 0 ≤ h ^ 2 * J h x :=
    (hJ0 h hh).mono (fun x hx => mul_nonneg (sq_nonneg h) hx)
  have hWratio : (∫ x, W h x ∂μ) / η < (1 : ℝ) / 4 :=
    (div_lt_iff₀ hη).mpr (by nlinarith [hw])
  have hJratio : (∫ x, h ^ 2 * J h x ∂μ) / η ^ 2 < (1 : ℝ) / 4 := by
    rw [integral_const_mul]
    exact (div_lt_iff₀ hη2).mpr (by nlinarith [hj])
  have hmean : (∫ x, W h x ∂μ) / η +
      (∫ x, h ^ 2 * J h x ∂μ) / η ^ 2 < 1 := by
    linarith
  obtain ⟨x, hxP, hxW, hxJ⟩ := exists_good_sample hη hη2 (hWi h hh) hGi
    (hW0 h hh) hG0 ((hP h hh).and (hJ0 h hh)) hmean
  refine ⟨h, hh, hd, x, hxP.1, hxW, ?_⟩
  have hsquare : (h * Real.sqrt (J h x)) ^ 2 < η ^ 2 := by
    rwa [mul_pow, Real.sq_sqrt hxP.2]
  exact (sq_lt_sq₀ (mul_nonneg hh.le (Real.sqrt_nonneg _)) hη.le).mp hsquare

end CircleDomainRigidity.FiniteTransfer

end OAI
