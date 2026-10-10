import OAI.Combinatorics.BalancedRyser.Probability.IndependentTrialKernel
import OAI.Combinatorics.BalancedRyser.Probability.IndependentTrials3

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials

variable {Ω α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → α} {Z : Ω → β} {V : Ω → γ}
  {f : (α × β) × γ → ℝ} {c : ℝ}

theorem independent_three_block_increment_bound
    (hX : Measurable X) (hZ : Measurable Z) (hV : Measurable V)
    (hindCurrent : IndepFun X Z μ)
    (hindFuture : IndepFun (fun ω => (X ω, Z ω)) V μ)
    (hf : StronglyMeasurable f)
    (hfi : Integrable (fun ω => f ((X ω, Z ω), V ω)) μ)
    (hfslice : ∀ x z, Integrable (fun v => f ((x, z), v)) (μ.map V))
    (hHslice : ∀ x, Integrable (fun z => ∫ v, f ((x, z), v) ∂(μ.map V)) (μ.map Z))
    (hosc : ∀ x z z', ∀ᵐ v ∂(μ.map V), |f ((x, z), v) - f ((x, z'), v)| ≤ c) :
    ∀ᵐ ω ∂μ,
      |μ[fun ω => f ((X ω, Z ω), V ω) |
          (inferInstance : MeasurableSpace (α × β)).comap (fun ω => (X ω, Z ω))] ω -
        μ[fun ω => f ((X ω, Z ω), V ω) |
          (inferInstance : MeasurableSpace α).comap X] ω| ≤ c := by
  have hrep₁ := condExp_independent_pair (hX.prodMk hZ) hV hindFuture hf hfi
  have hH : StronglyMeasurable (fun xz : α × β => ∫ v, f (xz, v) ∂(μ.map V)) :=
    hf.integral_prod_right'
  have hHint : Integrable (fun ω => ∫ v, f ((X ω, Z ω), v) ∂(μ.map V)) μ :=
    integrable_condExp.congr hrep₁
  have hrep₂ := condExp_independent_pair hX hZ hindCurrent hH hHint
  have hsmall :
      (inferInstance : MeasurableSpace α).comap X ≤
        (inferInstance : MeasurableSpace (α × β)).comap (fun ω => (X ω, Z ω)) :=
    MeasurableSpace.comap_le_comap_of_eq_comp Prod.fst measurable_fst rfl
  have htower := condExp_condExp_of_le (μ := μ) (f := fun ω => f ((X ω, Z ω), V ω))
    hsmall (hX.prodMk hZ).comap_le
  have hrep₀ := htower.symm.trans ((condExp_congr_ae hrep₁).trans hrep₂)
  filter_upwards [hrep₁, hrep₀] with ω h₁ h₀
  rw [h₁, h₀]
  apply abs_sub_integral_le_of_oscillation (hHslice (X ω)) (Z ω)
  exact Eventually.of_forall fun z =>
    abs_integral_sub_integral_le (hfslice (X ω) (Z ω)) (hfslice (X ω) z)
      (hosc (X ω) (Z ω) z)

end Balanced.IndependentTrials

end OAI
