import OAI.Analysis.IrrationalRotation.Model.LaurentConvolution
import Mathlib

namespace OAI

noncomputable section

namespace Invariant233.FiniteWindow

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_convolution (K n : ℕ) (a b : Ω → ℤ → ℂ)
    (ha : ∀ i, Measurable (fun ω => a ω i))
    (hb : ∀ i, Measurable (fun ω => b ω i)) :
    Measurable (fun ω => convolution K (a ω) (b ω) n) := by
  unfold convolution
  fun_prop

theorem norm_convolution_le (K n : ℕ) (D : ℝ) (a b : ℤ → ℂ)
    (ha : ∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a i‖ ≤ D)
    (hb : ∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b i‖ ≤ D) :
    ‖convolution K a b n‖ ≤ (2 * K + 1 : ℕ) * D ^ 2 := by
  classical
  have hD : 0 ≤ D := (norm_nonneg (a 0)).trans (ha 0 (by simp))
  unfold convolution
  calc
    ‖∑ i ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter
        (fun i => |(n : ℤ) + i| ≤ (K : ℤ)), a i * b (-(n : ℤ) - i)‖
        ≤ ∑ i ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter
          (fun i => |(n : ℤ) + i| ≤ (K : ℤ)), ‖a i * b (-(n : ℤ) - i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter
          (fun i => |(n : ℤ) + i| ≤ (K : ℤ)), D ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨his, hin⟩ := Finset.mem_filter.mp hi
      have hiK : |i| ≤ (K : ℤ) := abs_le.mpr (Finset.mem_Icc.mp his)
      have hniK : |-(n : ℤ) - i| ≤ (K : ℤ) := by
        simpa only [show -(n : ℤ) - i = -((n : ℤ) + i) by omega, abs_neg] using hin
      rw [norm_mul, pow_two]
      exact mul_le_mul (ha i hiK) (hb _ hniK) (norm_nonneg _) hD
    _ ≤ ∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), D ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i hi hnot => sq_nonneg D)
    _ = (2 * K + 1 : ℕ) * D ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, Int.card_Icc]
      congr 2
      omega

theorem integrableOn_convolution (μ : Measure Ω) (E : Set Ω)
    (hE : μ E < ∞) (K n : ℕ) (D : ℝ) (a b : Ω → ℤ → ℂ)
    (ha : ∀ i, Measurable (fun ω => a ω i))
    (hb : ∀ i, Measurable (fun ω => b ω i))
    (haD : ∀ᵐ ω ∂μ.restrict E, ∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a ω i‖ ≤ D)
    (hbD : ∀ᵐ ω ∂μ.restrict E, ∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b ω i‖ ≤ D) :
    IntegrableOn (fun ω => convolution K (a ω) (b ω) n) E μ := by
  apply IntegrableOn.of_bound hE (measurable_convolution K n a b ha hb).aestronglyMeasurable
    ((2 * K + 1 : ℕ) * D ^ 2)
  filter_upwards [haD, hbD] with ω hωa hωb
  exact norm_convolution_le K n D (a ω) (b ω) hωa hωb

theorem integrableOn_norm_convolution (μ : Measure Ω) (E : Set Ω)
    (hE : μ E < ∞) (K n : ℕ) (D : ℝ) (a b : Ω → ℤ → ℂ)
    (ha : ∀ i, Measurable (fun ω => a ω i))
    (hb : ∀ i, Measurable (fun ω => b ω i))
    (haD : ∀ᵐ ω ∂μ.restrict E, ∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a ω i‖ ≤ D)
    (hbD : ∀ᵐ ω ∂μ.restrict E, ∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b ω i‖ ≤ D) :
    IntegrableOn (fun ω => ‖convolution K (a ω) (b ω) n‖) E μ :=
  (integrableOn_convolution μ E hE K n D a b ha hb haD hbD).norm

end Invariant233.FiniteWindow

end

end OAI
