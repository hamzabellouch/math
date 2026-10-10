import Mathlib.Probability.Kernel.Posterior
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace Invariant233.FiniteMixturePosterior

variable {I X : Type*} [Fintype I] [MeasurableSpace I]
  [MeasurableSingletonClass I] [MeasurableSpace X]

theorem comp_eq_withDensity (π : Measure I) (μ : Measure X)
    (κ : Kernel I X) (u : I → X → ℝ≥0∞)
    (hu : ∀ i, Measurable (u i))
    (hκ : ∀ i, κ i = μ.withDensity (u i)) :
    κ ∘ₘ π = μ.withDensity (fun x => ∑ i, π {i} * u i x) := by
  ext s hs
  rw [Measure.bind_apply hs κ.aemeasurable, withDensity_apply _ hs,
    lintegral_fintype, lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [hκ i, withDensity_apply _ hs, lintegral_const_mul _ (hu i)]
    exact mul_comm _ _
  · intro i _
    exact measurable_const.mul (hu i)

theorem rnDeriv_density_ratio (μ : Measure X) [SigmaFinite μ]
    {a b : X → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b)
    [SigmaFinite (μ.withDensity a)] [SigmaFinite (μ.withDensity b)] :
    (μ.withDensity a).rnDeriv (μ.withDensity b) =ᵐ[μ.withDensity b]
      fun x => a x / b x := by
  have hbμ : μ.withDensity b ≪ μ := withDensity_absolutelyContinuous μ b
  filter_upwards [Measure.rnDeriv_eq_div
      (withDensity_absolutelyContinuous μ a) hbμ,
    hbμ (Measure.rnDeriv_withDensity μ ha),
    hbμ (Measure.rnDeriv_withDensity μ hb)] with x hx hax hbx
  simpa only [hax, hbx] using hx


variable [Nonempty I] [StandardBorelSpace I]

theorem posterior_singletons (π : Measure I) [IsFiniteMeasure π]
    (μ : Measure X) [SigmaFinite μ]
    (κ : Kernel I X) [IsFiniteKernel κ]
    (u : I → X → ℝ≥0∞) (hu : ∀ i, Measurable (u i))
    (hκ : ∀ i, κ i = μ.withDensity (u i)) :
    ∀ᵐ x ∂κ ∘ₘ π, ∀ i : I,
      (κ†π) x {i} = π {i} * u i x / (∑ j, π {j} * u j x) := by
  let h : X → ℝ≥0∞ := fun x => ∑ i, π {i} * u i x
  have hh : Measurable h := by
    exact Finset.measurable_sum _ (fun i _ => measurable_const.mul (hu i))
  have hμeq : κ ∘ₘ π = μ.withDensity h := comp_eq_withDensity π μ κ u hu hκ
  have : IsFiniteMeasure (μ.withDensity h) := hμeq ▸ inferInstance
  have hratio (i : I) : (κ i).rnDeriv (κ ∘ₘ π) =ᵐ[κ ∘ₘ π]
      fun x => u i x / h x := by
    have : IsFiniteMeasure (μ.withDensity (u i)) := hκ i ▸ inferInstance
    rw [hκ i, hμeq]
    exact rnDeriv_density_ratio μ (hu i) hh
  filter_upwards [posterior_eq_withDensity_of_countable κ π,
    ae_all_iff.mpr hratio] with x hx hxr i
  rw [hx]
  simp only [withDensity_apply _ (measurableSet_singleton i),
    lintegral_singleton, hxr i]
  change u i x / h x * π {i} = π {i} * u i x / h x
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ac_rfl

theorem posterior_disintegration (π : Measure I) [IsFiniteMeasure π]
    (μ : Measure X) (κ : Kernel I X) [IsFiniteKernel κ]
    (u : I → X → ℝ≥0∞) (hu : ∀ i, Measurable (u i))
    (hκ : ∀ i, κ i = μ.withDensity (u i)) :
    (μ.withDensity (fun x => ∑ i, π {i} * u i x)) ⊗ₘ (κ†π) =
      (π ⊗ₘ κ).map Prod.swap := by
  rw [← comp_eq_withDensity π μ κ u hu hκ]
  exact compProd_posterior_eq_map_swap

theorem posterior_lower_bound (π : Measure I) [IsFiniteMeasure π]
    (μ : Measure X) [SigmaFinite μ]
    (κ : Kernel I X) [IsFiniteKernel κ]
    (u : I → X → ℝ≥0∞) (hu : ∀ i, Measurable (u i))
    (hκ : ∀ i, κ i = μ.withDensity (u i)) (C : ℝ≥0∞) :
    ∀ᵐ x ∂κ ∘ₘ π, ∀ i : I, 1 ≤ u i x →
      (∑ j, π {j} * u j x) ≤ C → π {i} / C ≤ (κ†π) x {i} := by
  filter_upwards [posterior_singletons π μ κ u hu hκ] with x hx i hi hC
  rw [hx i]
  apply ENNReal.div_le_div ?_ hC
  simpa only [mul_one] using mul_le_mul_right hi (π {i})

theorem posterior_discrete_singletons {D : Type*} [MeasurableSpace D]
    [Countable D] [MeasurableSingletonClass D]
    (π : Measure I) [IsFiniteMeasure π]
    (κ : Kernel I D) [IsFiniteKernel κ] :
    ∀ᵐ d ∂κ ∘ₘ π, ∀ i : I,
      (κ†π) d {i} = π {i} * κ i {d} / (∑ j, π {j} * κ j {d}) := by
  apply posterior_singletons π Measure.count κ (fun i d => κ i {d})
  · intro i
    exact measurable_of_countable _
  · intro i
    simp only [count_withDensity, Measure.sum_smul_dirac]

theorem posterior_quantized_singletons {D : Type*} [MeasurableSpace D]
    [Countable D] [MeasurableSingletonClass D]
    (π : Measure I) [IsFiniteMeasure π]
    (κ : Kernel I X) [IsFiniteKernel κ]
    (Q : X → D) (hQ : Measurable Q) :
    ∀ᵐ d ∂κ.map Q ∘ₘ π, ∀ i : I,
      ((κ.map Q)†π) d {i} =
        π {i} * κ i (Q ⁻¹' {d}) / (∑ j, π {j} * κ j (Q ⁻¹' {d})) := by
  filter_upwards [posterior_discrete_singletons π (κ.map Q)] with d hd i
  simpa only [Kernel.map_apply' κ hQ _ (measurableSet_singleton _)] using hd i

theorem posterior_quantized_lower_bound {D : Type*} [MeasurableSpace D]
    [Countable D] [MeasurableSingletonClass D]
    (π : Measure I) [IsFiniteMeasure π]
    (κ : Kernel I X) [IsFiniteKernel κ]
    (Q : X → D) (hQ : Measurable Q) (μ : Measure X) (C : ℝ≥0∞) :
    ∀ᵐ d ∂κ.map Q ∘ₘ π, ∀ i : I,
      μ (Q ⁻¹' {d}) ≠ 0 → μ (Q ⁻¹' {d}) ≠ ∞ →
      μ (Q ⁻¹' {d}) ≤ κ i (Q ⁻¹' {d}) →
      (∑ j, π {j} * κ j (Q ⁻¹' {d})) ≤ C * μ (Q ⁻¹' {d}) →
      π {i} / C ≤ ((κ.map Q)†π) d {i} := by
  filter_upwards [posterior_quantized_singletons π κ Q hQ] with d hd i h0 ht hi hC
  rw [hd i]
  calc
    π {i} / C = (π {i} * μ (Q ⁻¹' {d})) / (C * μ (Q ⁻¹' {d})) :=
      (ENNReal.mul_div_mul_right _ _ h0 ht).symm
    _ ≤ π {i} * κ i (Q ⁻¹' {d}) / (∑ j, π {j} * κ j (Q ⁻¹' {d})) :=
      ENNReal.div_le_div (mul_le_mul_right hi _) hC

end Invariant233.FiniteMixturePosterior

end OAI
