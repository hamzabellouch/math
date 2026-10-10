import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.MeanZeroGramDecay
import OAI.Analysis.RieszRectifiability.Packing.ADCoreMassPacking

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory

theorem finite_geometric_two_sum_le (s : Finset ℕ) : ∑ k ∈ s, (1 / 2 : ℝ) ^ k ≤ 2 := by
  have h := summable_geometric_two.sum_le_tsum s (fun k _ => by positivity)
  simpa only [tsum_geometric_two] using! h

theorem finite_row_bound_of_geometric_slices {ι : Type*} (s : Finset ι)
    (gap : ι → ℕ) (v : ι → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hslice : ∀ k : ℕ, ∑ j ∈ s with gap j = k, v j ≤ A * (1 / 2 : ℝ) ^ k) :
    ∑ j ∈ s, v j ≤ 2 * A := by
  classical
  have hsum : (∑ k ∈ s.image gap, ∑ j ∈ s with gap j = k, v j) = ∑ j ∈ s, v j :=
    Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem gap hj) v
  rw [← hsum]
  calc
    _ ≤ ∑ k ∈ s.image gap, A * (1 / 2 : ℝ) ^ k := Finset.sum_le_sum (fun k _ => hslice k)
    _ = A * ∑ k ∈ s.image gap, (1 / 2 : ℝ) ^ k := (Finset.mul_sum _ _ _).symm
    _ ≤ A * 2 := mul_le_mul_of_nonneg_left (finite_geometric_two_sum_le _) hA
    _ = _ := by ring

theorem finite_L2_bessel_of_geometric_gram_slices {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (f : ι → X → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (w : ι → ℝ) (gap : ι → ι → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ i ∈ s, 0 < w i)
    (hslice : ∀ i ∈ s, ∀ k : ℕ,
      ∑ j ∈ s with gap i j = k, |∫ x, f i x * f j x ∂μ| * w j ≤
        A * w i * (1 / 2 : ℝ) ^ k)
    (u : X → ℝ) (hu : MemLp u 2 μ) :
    ∑ i ∈ s, (∫ x, f i x * u x ∂μ) ^ 2 ≤ (2 * A) * ∫ x, u x ^ 2 ∂μ := by
  refine finite_L2_bessel_of_weighted_pairings μ s f hf w (2 * A) (by positivity) hw ?_ u hu
  intro i hi
  have h := finite_row_bound_of_geometric_slices s (gap i)
    (fun j => |∫ x, f i x * f j x ∂μ| * w j) (A * w i)
    (mul_nonneg hA (hw i hi).le) (hslice i hi)
  simpa only [mul_assoc] using! h

end

end RieszRectifiability

end OAI
