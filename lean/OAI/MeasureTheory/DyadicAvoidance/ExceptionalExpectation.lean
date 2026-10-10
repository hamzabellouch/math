import Mathlib

namespace OAI

universe u_Ω

noncomputable section

namespace Problem310.Auxiliary

open Set MeasureTheory

/-- For a finite random family of measurable sets, averaging their densities is
identical to integrating pointwise membership probabilities. -/
theorem expected_density_eq_pointwise_probability
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → Set ℝ) (hR : ∀ ω, MeasurableSet (R ω)) :
    (∫⁻ ω, volume (R ω ∩ Icc (0 : ℝ) 1) ∂μ) =
      ∫⁻ x in Icc (0 : ℝ) 1, μ {ω | x ∈ R ω} := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let S : Set (Ω × ℝ) := {z | z.2 ∈ R z.1}
  have hS : MeasurableSet S := by
    have heq : S = ⋃ ω, ({ω} : Set Ω) ×ˢ R ω := by
      ext ⟨ω, x⟩
      simp [S]
    rw [heq]
    exact MeasurableSet.iUnion fun ω => (measurableSet_singleton ω).prod (hR ω)
  have heq := (Measure.prod_apply (μ := μ) (ν := ν) hS).symm.trans
    (Measure.prod_apply_symm (μ := μ) (ν := ν) hS)
  change (∫⁻ ω, ν (R ω) ∂μ) = ∫⁻ x, μ {ω | x ∈ R ω} ∂ν at heq
  simpa only [ν, Measure.restrict_apply (hR _)] using heq

/-- A uniform bound outside a small exceptional set of centers controls the
expected density. This is the integration step in the repair argument. -/
theorem expected_density_le_of_pointwise_bound
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → Set ℝ) (hR : ∀ ω, MeasurableSet (R ω))
    (G : Set ℝ) (hG : MeasurableSet G) (a : ENNReal)
    (hgood : ∀ x ∈ G, μ {ω | x ∈ R ω} ≤ a) :
    (∫⁻ ω, volume (R ω ∩ Icc (0 : ℝ) 1) ∂μ) ≤
      a + volume (Gᶜ ∩ Icc (0 : ℝ) 1) := by
  rw [expected_density_eq_pointwise_probability μ R hR]
  calc
    (∫⁻ x in Icc (0 : ℝ) 1, μ {ω | x ∈ R ω}) ≤
        ∫⁻ x in Icc (0 : ℝ) 1, a + Gᶜ.indicator (fun _ => (1 : ENNReal)) x := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ G
      · simpa [hx] using hgood x hx
      · simp only [mem_compl_iff, hx, not_false_eq_true, indicator_of_mem]
        exact (prob_le_one).trans (le_add_self)
    _ = a + volume (Gᶜ ∩ Icc (0 : ℝ) 1) := by
      rw [lintegral_add_left measurable_const]
      simp [lintegral_indicator hG.compl, Measure.restrict_apply hG.compl]

end Problem310.Auxiliary

end

end OAI
