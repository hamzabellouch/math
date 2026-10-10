import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedNuclearHardy

namespace OAI

/-! Summing localized estimates using spatial overlap rather than the number
of nuclei. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem finite_overlap_integral {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {μ : Measure X} (B : ι → Set X) (hB : ∀ i, MeasurableSet (B i))
    (f : X → ℝ) (hf : Integrable f μ) (hpos : ∀ x, 0 ≤ f x) (M : ℝ)
    (hoverlap : ∀ x, (∑ i, if x ∈ B i then (1:ℝ) else 0) ≤ M) :
    (∑ i, ∫ x in B i, f x ∂μ) ≤ M*∫ x, f x ∂μ := by
  classical
  simp_rw [← integral_indicator (hB _)]
  rw [← integral_finsetSum Finset.univ (fun i _ => hf.integrableOn.integrable_indicator (hB i)),
    ← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards [] with x
    exact Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun y _ => hpos y) x)
  · exact hf.const_mul M
  · filter_upwards [] with x
    have he : (∑ i, (B i).indicator f x) = (∑ i, if x ∈ B i then (1:ℝ) else 0)*f x := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hx : x ∈ B i <;> simp [hx]
    rw [he]
    exact mul_le_mul_of_nonneg_right (hoverlap x) (hpos x)

end ContinuumCoulomb

end

end OAI
