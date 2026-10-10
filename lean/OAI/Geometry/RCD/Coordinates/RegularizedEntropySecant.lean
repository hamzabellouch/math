import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # The regularized signed logarithmic variation is bounded by the entropy secant -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem regularized_log_secant_le_entropy (μ : Measure X) [SigmaFinite μ]
    (ν₀ : Measure X) [IsProbabilityMeasure ν₀]
    (r : Lp ℝ 2 μ) {h : X → ℝ}
    (hr : (r : X → ℝ) =ᵐ[μ] fun x => h x^2)
    (hrn : (fun x => h x^2) =ᵐ[μ] fun x => (ν₀.rnDeriv μ x).toReal)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal * Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hmap0 : π.map (fun γ => γ 0) = ν₀)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    (hs : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ B)
    (t : Time) (ht : 0 < (t:ℝ))
    (het : Integrable (fun x => ((π.map (fun γ => γ t)).rnDeriv μ x).toReal *
      Real.log ((π.map (fun γ => γ t)).rnDeriv μ x).toReal) μ) :
    regularizedPlanLogSecant π h t ≤
      (boltzmannEntropy μ (π.map (fun γ => γ t))-boltzmannEntropy μ ν₀)/(t:ℝ)+
        (t:ℝ)*(μ B).toReal := by
  have hν (s : Time) : π.map (fun γ => γ s) ≪ μ :=
    Measure.absolutelyContinuous_of_le_smul (hcomp s)
  have hνB (s : Time) : π.map (fun γ => γ s) ≪ μ.restrict B :=
    Measure.absolutelyContinuous_of_le_smul ((compression_iff_localized μ _ (hs s) C).mp (hcomp s))
  have hi (s : Time) : Integrable (fun x => h x^2) (π.map (fun γ => γ s)) :=
    ((Lp.memLp r).of_measure_le_smul hC (hcomp s)).integrable (by norm_num) |>.congr (hν s |>.ae_eq hr)
  have hil (s : Time) : Integrable (fun x => Real.log (h x^2+(t:ℝ)^2)) (π.map (fun γ => γ s)) :=
    integrable_log_of_lower _ ((hi s).add (integrable_const _)) (sq_pos_of_pos ht)
      (Eventually.of_forall fun x => by nlinarith [sq_nonneg (h x)])
  have hip (s : Time) : Integrable (fun γ : C(Time,X) => Real.log (h (γ s)^2+(t:ℝ)^2)) π :=
    (hil s).comp_measurable (measurable_path_eval s)
  have hg := entropy_regularized_subgradient_localized μ ν₀ (π.map (fun γ => γ t)) hB
    (hmap0 ▸ hνB 0) (hνB t) he0 het (sq_pos_of_pos ht) _ hrn (hmap0 ▸ hil 0) (hil t)
  have he (s : Time) : (∫γ : C(Time,X), Real.log (h (γ s)^2+(t:ℝ)^2) ∂π) =
      ∫x, Real.log (h x^2+(t:ℝ)^2) ∂π.map (fun γ => γ s) :=
    (integral_map (measurable_path_eval s).aemeasurable (hil s).aestronglyMeasurable).symm
  simp only [regularizedPlanLogSecant,planInitialSecant,geodesicExtension_eq]
  rw [integral_sub (hip t) (hip 0),he t,he 0,hmap0]
  apply (div_le_iff₀ ht).mpr
  field_simp
  nlinarith only [hg]

end RegularPointCoordinates

end

end OAI
