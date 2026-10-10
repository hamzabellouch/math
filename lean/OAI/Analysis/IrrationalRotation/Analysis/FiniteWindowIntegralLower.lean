import OAI.Analysis.IrrationalRotation.Analysis.LaurentNoncancellation
import OAI.Analysis.IrrationalRotation.Analysis.FiniteConvolutionMeasurability
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

open MeasureTheory

namespace Invariant233.FiniteWindow

theorem integrableOn_convolution_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : ℕ) (D : ℝ) (E : Set Ω) (a b : Ω → ℤ → ℂ)
    (ha : ∀ i, Measurable (fun ω => a ω i))
    (hb : ∀ i, Measurable (fun ω => b ω i))
    (hE : ∀ᵐ ω ∂μ.restrict E,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a ω i‖ ≤ D) ∧
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b ω i‖ ≤ D)) :
    IntegrableOn (fun ω => ∑ n ∈ Finset.range (2 * K + 1),
      ‖convolution K (a ω) (b ω) n‖) E μ := by
  classical
  exact integrable_finsetSum _ (fun n _ =>
    integrableOn_norm_convolution μ E (measure_lt_top μ E) K n D a b ha hb
      (hE.mono (fun _ h => h.1)) (hE.mono (fun _ h => h.2)))

theorem integral_lower_of_sum_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : ℕ) (D δ ε : ℝ)
    (hcoeff : ∀ a b : ℤ → ℂ,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a i‖ ≤ D) →
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b i‖ ≤ D) →
      δ ≤ ‖a 0‖ → δ ≤ ‖b 0‖ →
      ε ≤ ∑ n ∈ Finset.range (2 * K + 1), ‖convolution K a b n‖)
    (E : Set Ω) (a b : Ω → ℤ → ℂ)
    (ha : ∀ i, Measurable (fun ω => a ω i))
    (hb : ∀ i, Measurable (fun ω => b ω i))
    (hE : ∀ᵐ ω ∂μ.restrict E,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a ω i‖ ≤ D) ∧
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b ω i‖ ≤ D) ∧
      δ ≤ ‖a ω 0‖ ∧ δ ≤ ‖b ω 0‖) :
    ε * μ.real E ≤ ∫ ω in E, ∑ n ∈ Finset.range (2 * K + 1),
      ‖convolution K (a ω) (b ω) n‖ ∂μ := by
  have hbounds : ∀ᵐ ω ∂μ.restrict E,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a ω i‖ ≤ D) ∧
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b ω i‖ ≤ D) :=
    hE.mono (fun _ h => ⟨h.1, h.2.1⟩)
  have hi := integrableOn_convolution_sum μ K D E a b ha hb hbounds
  have hpoint : ∀ᵐ ω ∂μ.restrict E,
      ε ≤ ∑ n ∈ Finset.range (2 * K + 1), ‖convolution K (a ω) (b ω) n‖ :=
    hE.mono (fun ω h => hcoeff (a ω) (b ω) h.1 h.2.1 h.2.2.1 h.2.2.2)
  have h := integral_mono_ae (integrable_const ε) hi hpoint
  simpa only [setIntegral_const, smul_eq_mul, mul_comm] using h

theorem finite_sum_obstruction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Set Ω) (N : ℕ) (F : ℕ → Ω → ℝ) (c ε C : ℝ)
    (hε : 0 ≤ ε) (hmass : c ≤ μ.real E)
    (hint : ∀ n ∈ Finset.range N, IntegrableOn (F n) E μ)
    (hlower : ε * μ.real E ≤ ∫ ω in E, ∑ n ∈ Finset.range N, F n ω ∂μ)
    (hupper : ∀ n ∈ Finset.range N, (∫ ω in E, F n ω ∂μ) ≤ C) :
    c * ε ≤ (N : ℝ) * C := by
  calc
    c * ε ≤ ε * μ.real E := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hmass hε
    _ ≤ ∫ ω in E, ∑ n ∈ Finset.range N, F n ω ∂μ := hlower
    _ = ∑ n ∈ Finset.range N, ∫ ω in E, F n ω ∂μ :=
      integral_finsetSum _ hint
    _ ≤ ∑ n ∈ Finset.range N, C := Finset.sum_le_sum hupper
    _ = (N : ℝ) * C := by simp [nsmul_eq_mul]

theorem uniform_event_integral_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : ℕ) (D δ : ℝ) (hδ : 0 < δ) :
    ∃ ε > 0, ∀ (E : Set Ω) (a b : Ω → ℤ → ℂ),
      (∀ i, Measurable (fun ω => a ω i)) →
      (∀ i, Measurable (fun ω => b ω i)) →
      (∀ᵐ ω ∂μ.restrict E,
        (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a ω i‖ ≤ D) ∧
        (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b ω i‖ ≤ D) ∧
        δ ≤ ‖a ω 0‖ ∧ δ ≤ ‖b ω 0‖) →
      ε * μ.real E ≤ ∫ ω in E, ∑ n ∈ Finset.range (2 * K + 1),
        ‖convolution K (a ω) (b ω) n‖ ∂μ := by
  obtain ⟨ε, hε, hcoeff⟩ := uniform_convolution_sum_lower_bound K D δ hδ
  exact ⟨ε, hε, fun E a b ha hb hE =>
    integral_lower_of_sum_bound μ K D δ ε hcoeff E a b ha hb hE⟩

end Invariant233.FiniteWindow

end OAI
