import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced

theorem hasSum_profile_integrals {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (x : ι → Ω → ℝ)
    (hmeas : ∀ i, AEStronglyMeasurable (x i) μ)
    (hnonneg : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ x i ω)
    (hnorm : ∀ᵐ ω ∂μ, HasSum (fun i => x i ω) 1) :
    HasSum (fun i => ∫ ω, x i ω ∂μ) (μ.real Set.univ) := by
  have hint : Integrable (fun ω => ∑' i, x i ω) μ := by
    apply (integrable_const (1 : ℝ)).congr
    filter_upwards [hnorm] with ω hω
    exact hω.tsum_eq.symm
  have h := hasSum_integral_of_dominated_convergence x hmeas
    (fun i => (hnonneg i).mono (fun ω hω => by simp [Real.norm_eq_abs, abs_of_nonneg hω]))
    (hnorm.mono (fun ω hω => hω.summable)) hint hnorm
  simpa using h

theorem hasSum_profile_weighted_mass {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (x : ι → Ω → ℝ) (P w : ι → ℝ)
    (hmeas : ∀ i, AEStronglyMeasurable (x i) μ)
    (hnonneg : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ x i ω)
    (hnorm : ∀ᵐ ω ∂μ, HasSum (fun i => x i ω) 1)
    (hinc : ∀ i, ∫ ω, x i ω ∂μ = w i * P i) :
    HasSum (fun i => w i * P i) (μ.real Set.univ) := by
  apply (hasSum_profile_integrals μ x hmeas hnonneg hnorm).congr_fun
  intro i
  exact (hinc i).symm

theorem deletion_profile_first_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (x : (ℕ × ℕ) → Ω → ℝ)
    (P : ℕ × ℕ → ℝ) (k : ℝ)
    (hmeas : ∀ ij, AEStronglyMeasurable (x ij) μ)
    (hnonneg : ∀ ij, ∀ᵐ ω ∂μ, 0 ≤ x ij ω)
    (hnorm : ∀ᵐ ω ∂μ, HasSum (fun ij => x ij ω) 1)
    (hinc : ∀ ij, ∫ ω, x ij ω ∂μ = (ij.1 : ℝ) * P ij)
    (hmass : μ.real Set.univ = k) :
    HasSum (fun ij => (ij.1 : ℝ) * P ij) k := by
  rw [← hmass]
  exact hasSum_profile_weighted_mass μ x P (fun ij => (ij.1 : ℝ))
    hmeas hnonneg hnorm hinc

theorem deletion_profile_second_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (x : (ℕ × ℕ) → Ω → ℝ)
    (P : ℕ × ℕ → ℝ) (c : ℝ)
    (hmeas : ∀ ij, AEStronglyMeasurable (x ij) μ)
    (hnonneg : ∀ ij, ∀ᵐ ω ∂μ, 0 ≤ x ij ω)
    (hnorm : ∀ᵐ ω ∂μ, HasSum (fun ij => x ij ω) 1)
    (hinc : ∀ ij, ∫ ω, x ij ω ∂μ = (ij.2 : ℝ) * P ij)
    (hmass : μ.real Set.univ = c) :
    HasSum (fun ij => (ij.2 : ℝ) * P ij) c := by
  rw [← hmass]
  exact hasSum_profile_weighted_mass μ x P (fun ij => (ij.2 : ℝ))
    hmeas hnonneg hnorm hinc

theorem invisible_profile_recurrence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (x : (ℕ × ℕ) → Ω → ℝ)
    (P : ℕ → ℕ → ℝ) (k : ℝ)
    (hinc : ∀ i j : ℕ, ∫ ω, x (i + 1, j) ω ∂μ = (i + 1 : ℝ) * P (i + 1) j)
    (hinvisible : ∀ i j : ℕ, ∀ᵐ ω ∂μ, x (i + 1, j) ω = P i j)
    (hmass : μ.real Set.univ = k) :
    ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j := by
  intro i j
  rw [← hinc i j, integral_congr_ae (hinvisible i j)]
  simp [hmass]

theorem invisible_cover_profile_recurrence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (x : (ℕ × ℕ) → Ω → ℝ)
    (P : ℕ → ℕ → ℝ) (c : ℝ)
    (hinc : ∀ i j : ℕ, ∫ ω, x (i, j + 1) ω ∂μ = (j + 1 : ℝ) * P i (j + 1))
    (hinvisible : ∀ i j : ℕ, ∀ᵐ ω ∂μ, x (i, j + 1) ω = P i j)
    (hmass : μ.real Set.univ = c) :
    ∀ i j : ℕ, (j + 1 : ℝ) * P i (j + 1) = c * P i j := by
  intro i j
  rw [← hinc i j, integral_congr_ae (hinvisible i j)]
  simp [hmass]

end Balanced

end OAI
