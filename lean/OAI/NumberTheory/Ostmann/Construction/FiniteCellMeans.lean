import OAI.NumberTheory.Ostmann.Construction.GoodCellSelection

namespace OAI

/-! # Means on the actual fibers of a finite partition -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def finiteCellMass (P : Finset ℕ) (label : ℕ → ℕ) (μ : ℕ → ℝ) (h : ℕ) : ℝ :=
  ∑ p ∈ P.filter (fun p => label p = h), μ p

noncomputable def finiteCellMean (P : Finset ℕ) (label : ℕ → ℕ) (μ f : ℕ → ℝ) (h : ℕ) : ℝ :=
  (finiteCellMass P label μ h)⁻¹ * ∑ p ∈ P.filter (fun p => label p = h), μ p * f p

theorem finiteCellMass_nonneg (P : Finset ℕ) (label : ℕ → ℕ) (μ : ℕ → ℝ)
    (hμ : ∀ p ∈ P, 0 ≤ μ p) (h : ℕ) : 0 ≤ finiteCellMass P label μ h := by
  exact Finset.sum_nonneg (fun p hp => hμ p (Finset.mem_filter.mp hp).1)

theorem finiteCellMass_mul_mean (P : Finset ℕ) (label : ℕ → ℕ) (μ f : ℕ → ℝ)
    (hμ : ∀ p ∈ P, 0 ≤ μ p) (h : ℕ) :
    finiteCellMass P label μ h * finiteCellMean P label μ f h =
      ∑ p ∈ P.filter (fun p => label p = h), μ p * f p := by
  by_cases hz : finiteCellMass P label μ h = 0
  · have hpoint : ∀ p ∈ P.filter (fun p => label p = h), μ p = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun p hp => hμ p (Finset.mem_filter.mp hp).1)).mp hz
    simp only [finiteCellMean, hz, zero_mul]
    exact (Finset.sum_eq_zero (fun p hp => by rw [hpoint p hp, zero_mul])).symm
  · simp only [finiteCellMean, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]

theorem finiteCellMean_le_one (P : Finset ℕ) (label : ℕ → ℕ) (μ f : ℕ → ℝ)
    (hμ : ∀ p ∈ P, 0 ≤ μ p) (hf : ∀ p ∈ P, f p ≤ 1) (h : ℕ) :
    finiteCellMean P label μ f h ≤ 1 := by
  have hnon := finiteCellMass_nonneg P label μ hμ h
  by_cases hz : finiteCellMass P label μ h = 0
  · simp [finiteCellMean, hz]
  · have hpos : 0 < finiteCellMass P label μ h := lt_of_le_of_ne hnon (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hpos).mp
    rw [finiteCellMass_mul_mean P label μ f hμ h, mul_one]
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_of_le_one_right (hμ p (Finset.mem_filter.mp hp).1) (hf p (Finset.mem_filter.mp hp).1)

theorem finiteCellMass_sum (P I : Finset ℕ) (label : ℕ → ℕ) (μ : ℕ → ℝ)
    (hlabel : ∀ p ∈ P, label p ∈ I) :
    (∑ h ∈ I, finiteCellMass P label μ h) = ∑ p ∈ P, μ p := by
  exact Finset.sum_fiberwise_of_maps_to hlabel μ

theorem finiteCellMean_sum (P I : Finset ℕ) (label : ℕ → ℕ) (μ f : ℕ → ℝ)
    (hlabel : ∀ p ∈ P, label p ∈ I) (hμ : ∀ p ∈ P, 0 ≤ μ p) :
    (∑ h ∈ I, finiteCellMass P label μ h * finiteCellMean P label μ f h) =
      ∑ p ∈ P, μ p * f p := by
  simp_rw [finiteCellMass_mul_mean P label μ f hμ]
  exact Finset.sum_fiberwise_of_maps_to hlabel (fun p => μ p * f p)

/-- A positive average over the primes yields many heavy cells of positive
average under the actual fiber masses, without a new probabilistic input. -/
theorem finite_positive_heavy_cells (P I : Finset ℕ) (label : ℕ → ℕ) (μ f : ℕ → ℝ)
    (hlabel : ∀ p ∈ P, label p ∈ I) (hμ : ∀ p ∈ P, 0 ≤ μ p)
    (hf : ∀ p ∈ P, f p ≤ 1) (δ θ M : ℝ) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ)
    (hbias : δ * (∑ p ∈ P, μ p) ≤ ∑ p ∈ P, μ p * f p)
    (hthin : I.card * θ ≤ (δ / 4) * ∑ p ∈ P, μ p)
    (hcap : ∀ h ∈ I, finiteCellMass P label μ h ≤ M) :
    (δ / 4) * (∑ p ∈ P, μ p) ≤
      (positiveHeavyCells I (finiteCellMass P label μ) (finiteCellMean P label μ f) δ θ).card * M := by
  have hh := positiveHeavyCells_card I (finiteCellMass P label μ) (finiteCellMean P label μ f)
    δ θ M (fun h _ => finiteCellMass_nonneg P label μ hμ h) hδ hθ
    (fun h _ => finiteCellMean_le_one P label μ f hμ hf h)
    (by rw [finiteCellMass_sum P I label μ hlabel, finiteCellMean_sum P I label μ f hlabel hμ]; exact hbias)
    (by rw [finiteCellMass_sum P I label μ hlabel]; exact hthin) hcap
  rwa [finiteCellMass_sum P I label μ hlabel] at hh

end Ostmann

end OAI
