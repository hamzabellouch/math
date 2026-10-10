import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.FiniteWeightedSchur
import OAI.Analysis.RieszRectifiability.Kernel.L2Pairings

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory

theorem finite_synthesis_sq_le_weighted_gram {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : Finset ι) (h : ι → E) (w a : ι → ℝ) (C : ℝ)
    (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, |inner ℝ (h i) (h j)| * w j ≤ C * w i) :
    ‖∑ i ∈ s, a i • h i‖ ^ 2 ≤ C * ∑ i ∈ s, a i ^ 2 := by
  have heq : ‖∑ i ∈ s, a i • h i‖ ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, a i * a j * inner ℝ (h i) (h j) := by
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, |a i| * |a j| * |inner ℝ (h i) (h j)| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [abs_mul] using! le_abs_self (a i * a j * inner ℝ (h i) (h j))
    _ ≤ _ := finite_weighted_schur_quadratic s (fun i j => |inner ℝ (h i) (h j)|) w a C hw
      (fun _ _ _ _ => abs_nonneg _) (fun i _ j _ => by rw [real_inner_comm]) hrow

theorem finite_bessel_of_weighted_gram {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : Finset ι) (h : ι → E) (w : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, |inner ℝ (h i) (h j)| * w j ≤ C * w i) (u : E) :
    ∑ i ∈ s, (inner ℝ (h i) u) ^ 2 ≤ C * ‖u‖ ^ 2 := by
  let a := fun i => inner ℝ (h i) u
  let S : ℝ := ∑ i ∈ s, a i ^ 2
  let v := ∑ i ∈ s, a i • h i
  have hSv : inner ℝ v u = S := by
    simp only [v, S, a, sum_inner, real_inner_smul_left, pow_two]
  have hv : ‖v‖ ^ 2 ≤ C * S := finite_synthesis_sq_le_weighted_gram s h w a C hw hrow
  have hcs := real_inner_mul_inner_self_le v u
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hSv] at hcs
  have hcs' : S ^ 2 ≤ ‖v‖ ^ 2 * ‖u‖ ^ 2 := by simpa only [pow_two] using! hcs
  have hsq : S ^ 2 ≤ C * S * ‖u‖ ^ 2 := by
    exact hcs'.trans (mul_le_mul_of_nonneg_right hv (sq_nonneg ‖u‖))
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change S ≤ C * ‖u‖ ^ 2
  by_cases hzero : S = 0
  · rw [hzero]
    exact mul_nonneg hC (sq_nonneg _)
  · have hpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
    nlinarith

theorem finite_L2_bessel_of_weighted_pairings {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (f : ι → X → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (w : ι → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, |∫ x, f i x * f j x ∂μ| * w j ≤ C * w i)
    (u : X → ℝ) (hu : MemLp u 2 μ) :
    ∑ i ∈ s, (∫ x, f i x * u x ∂μ) ^ 2 ≤ C * ∫ x, u x ^ 2 ∂μ := by
  have hGram : ∀ i ∈ s, ∑ j ∈ s, |inner ℝ ((hf i).toLp (f i)) ((hf j).toLp (f j))| * w j ≤ C * w i := by
    simpa only [toLp_inner_eq_integral] using! hrow
  have hb := finite_bessel_of_weighted_gram s (fun i => (hf i).toLp (f i)) w C hC hw hGram (hu.toLp u)
  simpa only [toLp_inner_eq_integral, toLp_norm_sq_eq_integral] using! hb

theorem finite_L2_packing_of_pairing_lower_bounds {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (f : ι → X → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (w mass : ι → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, |∫ x, f i x * f j x ∂μ| * w j ≤ C * w i)
    (u : X → ℝ) (hu : MemLp u 2 μ) (v : ℝ) (hv : 0 < v)
    (hlower : ∀ i ∈ s, v ^ 2 * mass i ≤ (∫ x, f i x * u x ∂μ) ^ 2) :
    ∑ i ∈ s, mass i ≤ (C * ∫ x, u x ^ 2 ∂μ) / v ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hv)).mpr
  calc
    _ = ∑ i ∈ s, v ^ 2 * mass i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ s, (∫ x, f i x * u x ∂μ) ^ 2 := Finset.sum_le_sum hlower
    _ ≤ _ := finite_L2_bessel_of_weighted_pairings μ s f hf w C hC hw hrow u hu

end

end RieszRectifiability

end OAI
