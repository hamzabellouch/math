import OAI.Analysis.IrrationalRotation.Analysis.TrimmingWeakLimits
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Bounded.Normed

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace Invariant233.VaryingMapWeakLimit

variable {X Y : Type*} [MeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]

theorem tendsto_map_of_ae_tendsto (μ : FiniteMeasure X)
    (f : ℕ → X → Y) (g : X → Y)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hlim : ∀ᵐ x ∂(μ : Measure X), Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => μ.map (f n)) atTop (𝓝 (μ.map g)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro φ
  have hi := tendsto_integral_of_dominated_convergence (μ := (μ : Measure X))
    (fun _ => ‖φ‖)
    (fun n => (φ.continuous.measurable.comp (hf n)).aestronglyMeasurable)
    (integrable_const ‖φ‖)
    (fun n => Filter.Eventually.of_forall (fun x => φ.norm_coe_le_norm (f n x)))
    (hlim.mono (fun x hx => φ.continuous.continuousAt.tendsto.comp hx))
  simpa only [Function.comp_def, FiniteMeasure.toMeasure_map,
    integral_map (hf _).aemeasurable φ.continuous.aestronglyMeasurable,
    integral_map hg.aemeasurable φ.continuous.aestronglyMeasurable] using hi

theorem tendsto_map_restrict_of_ae_tendsto (μ : FiniteMeasure X)
    (f : ℕ → X → Y) (g : X → Y)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hlim : ∀ᵐ x ∂(μ : Measure X), Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hlost : Tendsto (fun n => μ (A n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => (μ.restrict (A n)).map (f n)) atTop (𝓝 (μ.map g)) := by
  apply TrimmingWeakLimits.tendsto_of_add_eq_of_mass_tendsto_zero
    (tendsto_map_of_ae_tendsto μ f g hf hg hlim)
    (δn := fun n => (μ.restrict (A n)ᶜ).map (f n))
  · intro n
    rw [← FiniteMeasure.map_add (hf n)]
    congr 1
    simpa only [union_compl_self, FiniteMeasure.restrict_univ] using
      (FiniteMeasure.restrict_union (μ := μ) disjoint_compl_right (hA n).compl).symm
  · simpa only [FiniteMeasure.mass, FiniteMeasure.map_apply _ (hf _) MeasurableSet.univ,
      preimage_univ, FiniteMeasure.restrict_apply μ _ MeasurableSet.univ,
      univ_inter] using hlost

end Invariant233.VaryingMapWeakLimit

end

end OAI
