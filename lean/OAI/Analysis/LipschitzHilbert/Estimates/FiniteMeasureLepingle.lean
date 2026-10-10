import OAI.Analysis.LipschitzHilbert.Estimates.ComplexVariation

namespace OAI

/-! Normalize a finite line cell, apply the published probability-space
inequality, then restore its unnormalized measure without loss. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert

theorem martingale_smul_measure {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ m}
    {F : ℕ → Ω → ℝ} (hF : Martingale F ℱ μ) (c : ℝ≥0∞) (hc : c ≠ ∞) :
    Martingale F ℱ (c • μ) := by
  have : IsFiniteMeasure (c • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top _ _)⟩
  apply martingale_of_setIntegral_eq_succ hF.stronglyAdapted
    (fun n => (hF.integrable n).smul_measure hc)
  intro n s hs
  simp only [Measure.restrict_smul, integral_smul_measure]
  rw [hF.setIntegral_eq (Nat.le_succ n) hs]

/-- The scalar probability-space theorem gives the same constant on
every finite measure. This is the normalization used on coarsest line cells. -/
theorem lepingle_complex_finite_measure (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω),
        IsFiniteMeasure μ → ∀ (κ : Type) [Fintype κ]
          (ℱ : Filtration ℕ m) (F : ℕ → Ω → EuclideanSpace ℂ κ),
          (∀ k, Martingale (fun n x => (F n x k).re) ℱ μ) →
          (∀ k, Martingale (fun n x => (F n x k).im) ℱ μ) →
          (∀ k n, MemLp (fun x => (F n x k).re) 2 μ) →
          (∀ k n, MemLp (fun x => (F n x k).im) 2 μ) → ∀ N : ℕ,
            (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤
              (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F N x‖ₑ ^ 2 ∂μ := by
  obtain ⟨C,hC,hbound⟩ := lepingle_complex_bound hL
  refine ⟨C,hC,?_⟩
  intro Ω m μ hμ κ inst ℱ F hRe hIm hRe2 hIm2 N
  let : IsFiniteMeasure μ := hμ
  by_cases hzero : μ = 0
  · simp [hzero]
  have hmass : μ Set.univ ≠ 0 := fun hz => hzero (Measure.measure_univ_eq_zero.mp hz)
  have htop : μ Set.univ ≠ ∞ := (measure_lt_top μ Set.univ).ne
  let c := (μ Set.univ)⁻¹
  have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.mpr htop
  have hctop : c ≠ ∞ := ENNReal.inv_ne_top.mpr hmass
  have hprob : IsProbabilityMeasure (c • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hmass htop⟩
  have h := hbound Ω m (c • μ) hprob κ ℱ F
    (fun k => martingale_smul_measure (hRe k) c hctop)
    (fun k => martingale_smul_measure (hIm k) c hctop)
    (fun k n => (hRe2 k n).smul_measure hctop)
    (fun k n => (hIm2 k n).smul_measure hctop) N
  simp only [lintegral_smul_measure, smul_eq_mul] at h
  rw [← mul_assoc, mul_comm ((C : ℝ≥0∞) ^ 2) c, mul_assoc] at h
  have hcancel := mul_le_mul_right h c⁻¹
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul] using hcancel

end LipschitzHilbert

end

end OAI
