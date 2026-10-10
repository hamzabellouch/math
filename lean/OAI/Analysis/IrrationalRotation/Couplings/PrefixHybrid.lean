import OAI.Analysis.IrrationalRotation.Model.PrefixHybrid
import OAI.Analysis.IrrationalRotation.Sampling.ProductSampling
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Invariant233.ProductModel

@[simp] theorem prefixEndpoint_apply (D i : ℕ) (x y : Base) :
    prefixEndpoint D x y i = if i < D then y i else x i := by
  simp [prefixEndpoint, selectedEndpoint]

@[simp] theorem prefixPair_fst (D : ℕ) (xy : EndpointPair) :
    (prefixPair D xy).1 = xy.1 := rfl

theorem continuous_prefixEndpoint (D : ℕ) :
    Continuous (fun xy : EndpointPair => prefixEndpoint D xy.1 xy.2) := by
  apply continuous_pi
  intro i
  by_cases hi : i < D
  · simpa only [prefixEndpoint_apply, ite_eq_left hi, Function.comp_def] using
      (continuous_apply i).comp continuous_snd
  · simpa only [prefixEndpoint_apply, ite_eq_right hi, Function.comp_def] using
      (continuous_apply i).comp continuous_fst

theorem continuous_prefixPair (D : ℕ) : Continuous (prefixPair D) :=
  continuous_fst.prodMk (continuous_prefixEndpoint D)

theorem measurable_prefixPair (D : ℕ) : Measurable (prefixPair D) :=
  Sampling.endpointMap_measurable (Finset.range D)

theorem tendsto_prefixEndpoint (x y : Base) :
    Tendsto (fun D => prefixEndpoint D x y) atTop (𝓝 y) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i] with D hD
  simp [prefixEndpoint_apply, hD]

theorem tendsto_prefixPair (xy : EndpointPair) :
    Tendsto (fun D => prefixPair D xy) atTop (𝓝 xy) :=
  tendsto_const_nhds.prodMk_nhds (tendsto_prefixEndpoint xy.1 xy.2)

theorem prefixPairLaw_first_marginal (ν : Measure EndpointPair) (D : ℕ) :
    (prefixPairLaw ν D).map Prod.fst = ν.map Prod.fst := by
  rw [prefixPairLaw, Measure.map_map measurable_fst (measurable_prefixPair D)]
  rfl

theorem prefixPairLaw_second_marginal (ν : Measure EndpointPair) (D : ℕ) :
    (prefixPairLaw ν D).map Prod.snd =
      ν.map (fun xy => prefixEndpoint D xy.1 xy.2) := by
  rw [prefixPairLaw, Measure.map_map measurable_snd (measurable_prefixPair D)]
  rfl

instance prefixPairLaw_finite (ν : Measure EndpointPair) [IsFiniteMeasure ν] (D : ℕ) :
    IsFiniteMeasure (prefixPairLaw ν D) := by
  unfold prefixPairLaw
  infer_instance

theorem prefixPairLaw_weaklyConverges (ν : Measure EndpointPair) [IsFiniteMeasure ν] :
    WeaklyConverges (prefixPairLaw ν) ν := by
  intro φ
  have hmap (D : ℕ) :
      (∫ xy, φ xy ∂prefixPairLaw ν D) = ∫ xy, φ (prefixPair D xy) ∂ν := by
    exact integral_map (measurable_prefixPair D).aemeasurable
      φ.continuous.aestronglyMeasurable
  simp_rw [hmap]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
  · intro D
    exact (φ.continuous.comp (continuous_prefixPair D)).aestronglyMeasurable
  · exact integrable_const _
  · intro D
    exact Filter.Eventually.of_forall (fun xy => φ.norm_coe_le_norm (prefixPair D xy))
  · exact Filter.Eventually.of_forall (fun xy =>
      φ.continuous.continuousAt.tendsto.comp (tendsto_prefixPair xy))

theorem ordered_selectedEndpoint {x y : Base} (hxy : Ordered x y) (I : Finset ℕ) :
    Ordered x (selectedEndpoint I x y) ∧ Ordered (selectedEndpoint I x y) y := by
  constructor <;> intro i <;> by_cases hi : i ∈ I
  · simpa only [selectedEndpoint, ite_eq_left hi] using hxy i
  · simp only [selectedEndpoint, ite_eq_right hi, le_refl]
  · simp only [selectedEndpoint, ite_eq_left hi, le_refl]
  · simpa only [selectedEndpoint, ite_eq_right hi] using hxy i

theorem prefixPairLaw_ordered (ν : Measure EndpointPair)
    (hν : ∀ᵐ xy ∂ν, Ordered xy.1 xy.2) (D : ℕ) :
    ∀ᵐ xy ∂prefixPairLaw ν D, Ordered xy.1 xy.2 := by
  rw [prefixPairLaw, ae_map_iff (measurable_prefixPair D).aemeasurable
    Sampling.ordered_measurable]
  filter_upwards [hν] with xy hxy
  exact (ordered_selectedEndpoint hxy (Finset.range D)).1

end Invariant233.ProductModel

end

end OAI
