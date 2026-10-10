import OAI.Analysis.CircleDomains.Probability.BorelDensityBudget
import OAI.Analysis.CircleDomains.Probability.ProbabilitySquareBounds

namespace OAI

/-! Joint measurable densities and preservation of their budgets under
probability mixtures. This is applied separately to occupation and tuple kernels. -/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
  [MeasurableSpace.CountablyGenerated X]

theorem jointly_measurable_densities_of_bounded_budget
    (μ : Z → Measure X) (hμ : Measurable μ) (σ : Measure X) [IsFiniteMeasure σ]
    (mass energy : ℝ≥0∞) (hmass : mass < ∞)
    (hbudget : ∀ z, BoundedDensityBudget σ (μ z) mass energy) :
    ∃ g : Z × X → ℝ≥0∞, Measurable g ∧ ∀ z,
      μ z = σ.withDensity (fun x => g (z, x)) ∧ (∫⁻ x, g (z, x) ^ 2 ∂σ) ≤ energy := by
  let κ : Kernel Z X := ⟨μ, hμ⟩
  let : IsFiniteKernel κ := ⟨⟨mass, hmass, fun z => (hbudget z).1⟩⟩
  let η : Kernel Z X := Kernel.const Z σ
  let g : Z × X → ℝ≥0∞ := fun p => κ.rnDeriv η p.1 p.2
  refine ⟨g, Kernel.measurable_rnDeriv κ η, ?_⟩
  intro z
  obtain ⟨f, hf, hμf, hfe⟩ := (hbudget z).2
  have hrn : (fun x => g (z, x)) =ᵐ[σ] (μ z).rnDeriv σ :=
    Kernel.rnDeriv_eq_rnDeriv_measure
  have hgf : (fun x => g (z, x)) =ᵐ[σ] f :=
    hrn.trans (by rw [hμf]; exact Measure.rnDeriv_withDensity σ hf)
  refine ⟨hμf.trans (withDensity_congr_ae hgf).symm, ?_⟩
  apply le_trans (le_of_eq (lintegral_congr_ae ?_)) hfe
  filter_upwards [hgf] with x hx
  exact congrArg (fun t : ℝ≥0∞ => t ^ 2) hx

theorem boundedDensityBudget_bind
    (μ : Z → Measure X) (hμ : Measurable μ) (σ : Measure X) [IsFiniteMeasure σ]
    (mass energy : ℝ≥0∞) (hmass : mass < ∞)
    (hbudget : ∀ z, BoundedDensityBudget σ (μ z) mass energy)
    (P : Measure Z) [IsProbabilityMeasure P] :
    BoundedDensityBudget σ (P.bind μ) mass energy := by
  obtain ⟨g, hg, hμg⟩ := jointly_measurable_densities_of_bounded_budget μ hμ σ
    mass energy hmass hbudget
  have hmass' : (P.bind μ) univ ≤ mass := by
    rw [Measure.bind_apply MeasurableSet.univ hμ.aemeasurable]
    calc
      _ ≤ ∫⁻ _z, mass ∂P := lintegral_mono fun z => (hbudget z).1
      _ = mass := by simp
  refine ⟨hmass', (fun x => ∫⁻ z, g (z, x) ∂P),
    (hg.comp measurable_swap).lintegral_prod_right', ?_, ?_⟩
  · ext s hs
    rw [Measure.bind_apply hs hμ.aemeasurable, withDensity_apply _ hs]
    simp_rw [(hμg _).1, withDensity_apply _ hs]
    exact lintegral_lintegral_swap hg.aemeasurable
  · exact density_square_integral_mixture_bound P σ g hg energy
      (Eventually.of_forall fun z => (hμg z).2)

end CircleDomainRigidity

end

end OAI
