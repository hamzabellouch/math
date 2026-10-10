import OAI.MeasureTheory.DyadicAvoidance.ExceptionalCenters
import OAI.MeasureTheory.DyadicAvoidance.ExceptionalExpectation

namespace OAI

universe u_Ω

noncomputable section

namespace Problem310.Auxiliary

open Set Filter Topology MeasureTheory

/-- First-moment selection followed by deterministic open-neighborhood repair. -/
theorem periodic_hitting_of_expected_exceptional
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 < p) (B : Ω → Set ℝ)
    (hBo : ∀ ω, IsOpen (B ω))
    (hBp : ∀ ω x, x + 1 ∈ B ω ↔ x ∈ B ω)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (hBmean : (∫⁻ ω, volume (B ω ∩ Icc (0 : ℝ) 1) ∂μ) ≤ ENNReal.ofReal (2 * p))
    (hRmean : (∫⁻ ω, volume
      (exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n) ∩ Icc (0 : ℝ) 1) ∂μ)
        ≤ ENNReal.ofReal (3 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by
  let f : Ω → ENNReal := fun ω => volume (B ω ∩ Icc (0 : ℝ) 1)
  let g : Ω → ENNReal := fun ω => volume
    (exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n) ∩ Icc (0 : ℝ) 1)
  have hf : Measurable f := measurable_of_countable f
  have hg : Measurable g := measurable_of_countable g
  obtain ⟨ω, hω⟩ := exists_le_lintegral (μ := μ) (hf.add hg).aemeasurable
  apply periodic_hitting_of_small_exceptional p hp (B ω) (hBo ω) (hBp ω) N hN
  calc
    f ω + g ω ≤ ∫⁻ ω, f ω + g ω ∂μ := hω
    _ = (∫⁻ ω, f ω ∂μ) + ∫⁻ ω, g ω ∂μ := lintegral_add_left hf _
    _ ≤ ENNReal.ofReal (2 * p) + ENNReal.ofReal (3 * p) := add_le_add hBmean hRmean
    _ = ENNReal.ofReal (5 * p) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- Full analytic repair interface from pointwise failure probabilities on stable centers. -/
theorem periodic_hitting_of_pointwise_failure_bound
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 < p) (B : Ω → Set ℝ)
    (hBo : ∀ ω, IsOpen (B ω))
    (hBp : ∀ ω x, x + 1 ∈ B ω ↔ x ∈ B ω)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (G : Set ℝ) (hG : MeasurableSet G)
    (hbad : volume (Gᶜ ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p)
    (hBmean : (∫⁻ ω, volume (B ω ∩ Icc (0 : ℝ) 1) ∂μ) ≤ ENNReal.ofReal (2 * p))
    (hgood : ∀ x ∈ G,
      μ {ω | x ∈ exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)}
        ≤ ENNReal.ofReal (2 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by
  apply periodic_hitting_of_expected_exceptional μ p hp B hBo hBp N hN hBmean
  have hRm : ∀ ω, MeasurableSet
      (exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)) :=
    fun ω => (isClosed_exceptionalCenters (B ω) (hBo ω) N _).measurableSet
  calc
    (∫⁻ ω, volume
        (exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n) ∩ Icc (0 : ℝ) 1) ∂μ)
        ≤ ENNReal.ofReal (2 * p) + volume (Gᶜ ∩ Icc (0 : ℝ) 1) :=
      expected_density_le_of_pointwise_bound μ _ hRm G hG _ hgood
    _ ≤ ENNReal.ofReal (2 * p) + ENNReal.ofReal p := add_le_add le_rfl hbad
    _ = ENNReal.ofReal (3 * p) := by
      rw [← ENNReal.ofReal_add (by positivity) (le_of_lt hp)]
      congr 1
      ring

end Problem310.Auxiliary

end

end OAI
