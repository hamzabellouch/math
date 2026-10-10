import OAI.Geometry.RCD.Metric.RescaledPackingBound

namespace OAI

/-! # Integrating finite covers with bounded overlap -/

open Set MeasureTheory

noncomputable section
namespace RegularPointCoordinates

attribute [local instance] Classical.propDecidable

variable {X I : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Integrate a nonnegative function over a finite cover, allowing overlap. -/
theorem integral_le_sum_cover (s : Finset I) (A : I → Set X) (hA : ∀ i ∈ s, MeasurableSet (A i))
    {Ω : Set X} (hΩ : MeasurableSet Ω) (hcover : Ω ⊆ ⋃ i ∈ s, A i)
    {f : X → ℝ} (hf : Integrable f μ) (hpos : ∀ x, 0 ≤ f x) :
    (∫ x in Ω, f x ∂μ) ≤ ∑ i ∈ s, ∫ x in A i, f x ∂μ := by
  classical
  have heq : (∫ x, ∑ i ∈ s, (A i).indicator f x ∂μ) =
      ∑ i ∈ s, ∫ x in A i, f x ∂μ := by
    rw [integral_finsetSum s (fun i hi => hf.indicator (hA i hi))]
    exact Finset.sum_congr rfl (fun i hi => integral_indicator (hA i hi))
  rw [← integral_indicator hΩ, ← heq]
  apply integral_mono (hf.indicator hΩ)
    (integrable_finsetSum s (fun i hi => hf.indicator (hA i hi)))
  intro x
  have hnonneg (i : I) : 0 ≤ (A i).indicator f x := indicator_nonneg (fun y _ => hpos y) x
  by_cases hx : x ∈ Ω
  · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcover hx)
    rw [indicator_of_mem hx]
    calc
      f x = (A i).indicator f x := (indicator_of_mem hxi f).symm
      _ ≤ _ := Finset.single_le_sum (fun j _ => hnonneg j) hi
  · rw [indicator_of_notMem hx]
    exact Finset.sum_nonneg fun i _ => hnonneg i

/-- A bound on overlap controls the sum of local integrals by the global
integral, with precisely the same multiplicity constant. -/
theorem sum_integral_le_overlap (s : Finset I) (A : I → Set X)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) (N : ℕ)
    (hoverlap : ∀ x, (s.filter (fun i => x ∈ A i)).card ≤ N)
    {f : X → ℝ} (hf : Integrable f μ) (hpos : ∀ x, 0 ≤ f x) :
    (∑ i ∈ s, ∫ x in A i, f x ∂μ) ≤ N * ∫ x, f x ∂μ := by
  classical
  have heq : (∫ x, ∑ i ∈ s, (A i).indicator f x ∂μ) =
      ∑ i ∈ s, ∫ x in A i, f x ∂μ := by
    rw [integral_finsetSum s (fun i hi => hf.indicator (hA i hi))]
    exact Finset.sum_congr rfl (fun i hi => integral_indicator (hA i hi))
  rw [← heq, ← integral_const_mul]
  apply integral_mono (integrable_finsetSum s (fun i hi => hf.indicator (hA i hi)))
    (hf.const_mul _)
  intro x
  have hsum : (∑ i ∈ s, (A i).indicator f x) =
      ((s.filter (fun i => x ∈ A i)).card:ℝ)*f x := by
    simp only [indicator_apply, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_zero, add_zero]
  dsimp only
  rw [hsum]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hoverlap x) (hpos x)

end RegularPointCoordinates

end

end OAI
