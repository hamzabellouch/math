import OAI.Analysis.CircleDomains.Sobolev.CoareaLevels
import OAI.Analysis.CircleDomains.Probability.BandMeasure
import OAI.Analysis.CircleDomains.Uniformization.Conformal
import OAI.Analysis.CircleDomains.Topology.SphereLevels

namespace OAI

/-!
# Weighted coarea with the actual boundary-band incidences

The abstract dust events in the weighted-level estimate are here the
actual circle-band fibers. Their measurability and measure bounds are
proved from the compact band graph and its liminf–limsup budget.
The final theorem applies this to the finite-plane part of a bounded
real coordinate on the concrete Riemann sphere.
-/

open Set MeasureTheory Metric
open scoped Topology ENNReal

namespace CircleDomainRigidity

def unitIntervalBandIncidence {X : Type*} [TopologicalSpace X]
    (G : Set X) (f : X → ℝ) (x : X) : Set ℝ :=
  {t | (x, (t : AddCircle (1 : ℝ))) ∈ circleBandGraph G f}

theorem measurableSet_unitIntervalBandIncidence
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ y ∈ G, |f y| ≤ M) (x : X) :
    MeasurableSet (unitIntervalBandIncidence G f x) :=
  (measurableSet_circleBandIncidence hM x).preimage
    (AddCircle.continuous_mk' (1 : ℝ)).measurable

theorem measure_unitIntervalBandIncidence_le
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [CompactSpace X] [T2Space X]
    {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ y ∈ G, |f y| ≤ M)
    {x : X} (hx : x ∈ closure G) {a : ℝ}
    (hbudget : Filter.limsup f (𝓝[G] x) - Filter.liminf f (𝓝[G] x) ≤ a) :
    (volume.restrict (Ico (0 : ℝ) 1)) (unitIntervalBandIncidence G f x) ≤
      ENNReal.ofReal a := by
  rw [restrict_Ico_eq_restrict_Ioc]
  have hmeasure := (AddCircle.measurePreserving_mk (T := (1 : ℝ)) 0).measure_preimage
    (measurableSet_circleBandIncidence hM x).nullMeasurableSet
  change (volume.restrict (Ioc (0 : ℝ) (0 + 1)))
    (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹'
      {t : AddCircle (1 : ℝ) | (x, t) ∈ circleBandGraph G f}) = _ at hmeasure
  calc
    _ = volume {t : AddCircle (1 : ℝ) | (x, t) ∈ circleBandGraph G f} := by
      simpa only [zero_add, unitIntervalBandIncidence, Set.preimage, mem_ofPred_eq] using hmeasure
    _ ≤ _ := volume_circleBandGraph_incidence_le_budget hM hx hbudget

attribute [local instance] sphereMetric

/-- The weighted physical-plus-dust level bound for a bounded real
coordinate on the sphere. Only the scalar coarea formula is a published
input; the actual dust-incidence bound is derived from its band budget.
The physical term here uses the finite-plane chart and Euclidean H¹. -/
theorem weighted_level_bound_of_real_sphere_coordinate
    {S : Type*} [Countable S]
    (hcoarea : WeightedPlanarScalarCoarea)
    {G : Set Sphere} (hG : IsOpen G) (f : Sphere → ℝ) {M : ℝ}
    (hM : ∀ y ∈ G, |f y| ≤ M)
    (hf : ContDiffOn ℝ 1 (fun z : ℂ => f (z : Sphere))
      (((↑) : ℂ → Sphere) ⁻¹' G))
    (p : S → Sphere) (hp : ∀ s, p s ∈ closure G)
    (m a : S → ℝ) (hm : ∀ s, 0 ≤ m s) (ha : ∀ s, 0 ≤ a s)
    (hbudget : ∀ s, Filter.limsup f (𝓝[G] (p s)) -
      Filter.liminf f (𝓝[G] (p s)) ≤ a s)
    (hm2 : Summable (fun s => m s ^ 2)) (ha2 : Summable (fun s => a s ^ 2))
    (q : ℂ → ℝ) (hq : Measurable q) (hq0 : ∀ z, 0 ≤ q z)
    (hq2 : (∫⁻ z in (((↑) : ℂ → Sphere) ⁻¹' G), ENNReal.ofReal (q z ^ 2)) < ∞)
    (hf2 : (∫⁻ z in (((↑) : ℂ → Sphere) ⁻¹' G),
      ENNReal.ofReal (‖fderiv ℝ (fun z : ℂ => f (z : Sphere)) z‖ ^ 2)) < ∞) :
    (∫⁻ t in Ico (0 : ℝ) 1,
      (weightedCircleLevelLength (((↑) : ℂ → Sphere) ⁻¹' G)
          (fun z : ℂ => f (z : Sphere)) (fun z => ENNReal.ofReal (q z)) t +
        weightedBandIncidence (fun s => unitIntervalBandIncidence G f (p s)) m t)) ≤
      (∫⁻ z in (((↑) : ℂ → Sphere) ⁻¹' G),
        ENNReal.ofReal (q z) * ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f (z : Sphere)) z‖) +
        ENNReal.ofReal (∑' s, m s * a s) ∧
    (∫⁻ t in Ico (0 : ℝ) 1,
      (weightedCircleLevelLength (((↑) : ℂ → Sphere) ⁻¹' G)
          (fun z : ℂ => f (z : Sphere)) (fun z => ENNReal.ofReal (q z)) t +
        weightedBandIncidence (fun s => unitIntervalBandIncidence G f (p s)) m t)) < ∞ := by
  exact weighted_level_bound_of_planar_coarea hcoarea (hG.preimage OnePoint.continuous_coe)
    hf hq hq0 hq2 hf2 (fun s => unitIntervalBandIncidence G f (p s)) m a
    (fun s => measurableSet_unitIntervalBandIncidence hM (p s)) hm ha
    (fun s => measure_unitIntervalBandIncidence_le hM (hp s) (hbudget s)) hm2 ha2

end CircleDomainRigidity

end OAI
