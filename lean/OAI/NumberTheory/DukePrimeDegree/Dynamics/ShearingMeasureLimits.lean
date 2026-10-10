import OAI.NumberTheory.DukePrimeDegree.Geometry.CompactAction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

namespace OAI

/-!
# A limiting shear preserves the limiting measure

This is the measure step in the unipotent shearing argument. If two
families of probability measures have the same weak limit, and one is
the translate of the other by converging group elements, the limiting
element preserves that measure. Compact observables give uniform control
even when the sampled points leave every compact set.
-/

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology BoundedContinuousFunction

namespace DukePrimeDegree

variable {G X I : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [TopologicalSpace X] [LocallyCompactSpace X]
  [T2Space X] [MetrizableSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MulAction G X] [ContinuousSMul G X]
  {l : Filter I} [NeBot l]

omit [LocallyCompactSpace X] [T2Space X] [MetrizableSpace X] [SigmaCompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [NeBot l] in
/-- Moving translations of a compact observable converge uniformly. -/
lemma compact_observable_varying_smul
    (f : X → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (a : I → G) (g : G) (ha : Tendsto a l (𝓝 g)) :
    ∀ ε > 0, ∀ᶠ i in l, ∀ x,
      |f (a i • x) - f (g • x)| < ε := by
  have hid : Tendsto (fun i => a i * g⁻¹) l (𝓝 1) := by
    simpa only [mul_inv_cancel] using ha.mul_const g⁻¹
  intro ε hε
  have hu := Metric.tendstoUniformly_iff.mp
    (compact_observable_smul_tendstoUniformly (G := G) f hf hc) ε hε
  filter_upwards [hid.eventually hu] with i hi x
  simpa only [mul_smul, inv_smul_smul, Real.dist_eq, abs_sub_comm] using hi (g • x)

omit [LocallyCompactSpace X] [T2Space X] [MetrizableSpace X] [SigmaCompactSpace X]
  [NeBot l] in
/-- The group element and the probability measure can both vary: the
integral error from replacing the group element by its limit vanishes. -/
lemma integral_compact_observable_varying_smul
    (μ : I → ProbabilityMeasure X)
    (f : CompactlySupportedContinuousMap X ℝ)
    (a : I → G) (g : G) (ha : Tendsto a l (𝓝 g)) :
    Tendsto (fun i => (∫ x, f (a i • x) ∂(μ i : Measure X)) -
      ∫ x, f (g • x) ∂(μ i : Measure X)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [compact_observable_varying_smul f f.continuous f.hasCompactSupport a g ha
    (ε / 2) hhalf] with i hi
  have hia : Integrable (fun x => f (a i • x)) (μ i : Measure X) :=
    (f.toBoundedContinuousFunction.compContinuous
      ⟨fun x => a i • x, continuous_const_smul (a i)⟩).integrable (μ := (μ i : Measure X))
  have hig : Integrable (fun x => f (g • x)) (μ i : Measure X) :=
    (f.toBoundedContinuousFunction.compContinuous
      ⟨fun x => g • x, continuous_const_smul g⟩).integrable (μ := (μ i : Measure X))
  rw [Real.dist_eq, sub_zero, ← integral_sub hia hig]
  have hb := norm_integral_le_of_norm_le_const (μ := (μ i : Measure X))
    (f := fun x => f (a i • x) - f (g • x))
    (C := ε / 2) (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using (hi x).le))
  have he : (μ i : Measure X).real univ = 1 := by simp
  rw [he, mul_one, Real.norm_eq_abs] at hb
  exact hb.trans_lt (by linarith)

/-- A limiting shear belongs to the actual stabilizer of the limiting
probability measure. The hypotheses are weak limits and an exact
translation relation between approximating measures. -/
theorem map_eq_of_converging_translated_probabilities
    (μ ν : I → ProbabilityMeasure X) (ρ : ProbabilityMeasure X)
    (hμ : Tendsto μ l (𝓝 ρ)) (hν : Tendsto ν l (𝓝 ρ))
    (a : I → G) (g : G) (ha : Tendsto a l (𝓝 g))
    (htranslate : ∀ᶠ i in l,
      (μ i : Measure X).map (fun x => a i • x) = (ν i : Measure X)) :
    (ρ : Measure X).map (fun x => g • x) = (ρ : Measure X) := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hfixed := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ
    (f.toBoundedContinuousFunction.compContinuous
      ⟨fun x => g • x, continuous_const_smul g⟩)
  have htarget := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν
    f.toBoundedContinuousFunction
  have hvary := integral_compact_observable_varying_smul μ f a g ha
  have hsame : Tendsto (fun i => ∫ x, f (a i • x) ∂(μ i : Measure X)) l
      (𝓝 (∫ x, f x ∂(ρ : Measure X))) := by
    apply htarget.congr'
    filter_upwards [htranslate] with i hi
    change (∫ x, f x ∂(ν i : Measure X)) = _
    rw [← hi, integral_map (f := fun x => f x)
      (continuous_const_smul (a i)).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
  have hzero := hsame.sub hfixed
  have he : (∫ x, f x ∂(ρ : Measure X)) -
      (∫ x, f (g • x) ∂(ρ : Measure X)) = 0 := tendsto_nhds_unique hzero hvary
  rw [integral_map (f := fun x => f x) (continuous_const_smul g).measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  exact (sub_eq_zero.mp he).symm

/-- The sampled group element may vary across the orbit window. Uniform
smallness of its error, almost everywhere in each window, is enough.
This is the form used with a terminal polynomial shear. -/
theorem map_eq_of_asymptotically_translated_pairs
    {Z : Type*} [MeasurableSpace Z]
    (taus : I → ProbabilityMeasure Z) (p q : I → Z → X)
    (hp : ∀ i, Measurable (p i)) (hq : ∀ i, Measurable (q i))
    (ρ : ProbabilityMeasure X)
    (hplim : Tendsto (fun i => (taus i).map (p i)) l (𝓝 ρ))
    (hqlim : Tendsto (fun i => (taus i).map (q i)) l (𝓝 ρ))
    (g : G) (b : I → Z → G)
    (hsmall : ∀ U ∈ 𝓝 (1 : G), ∀ᶠ i in l, ∀ᵐ z ∂(taus i : Measure Z), b i z ∈ U)
    (hpair : ∀ᶠ i in l, ∀ᵐ z ∂(taus i : Measure Z),
      q i z = b i z • (g • p i z)) :
    (ρ : Measure X).map (fun x => g • x) = (ρ : Measure X) := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let fg : X →ᵇ ℝ := f.toBoundedContinuousFunction.compContinuous
    ⟨fun x => g • x, continuous_const_smul g⟩
  have hpleft := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hplim fg
  have hqleft := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hqlim
    f.toBoundedContinuousFunction
  change Tendsto (fun i => ∫ x, f (g • x) ∂((taus i).map (p i) : Measure X)) l
    (𝓝 (∫ x, f (g • x) ∂(ρ : Measure X))) at hpleft
  change Tendsto (fun i => ∫ x, f x ∂((taus i).map (q i) : Measure X)) l
    (𝓝 (∫ x, f x ∂(ρ : Measure X))) at hqleft
  have hpint : Tendsto (fun i => ∫ z, f (g • p i z) ∂(taus i : Measure Z)) l
      (𝓝 (∫ x, f (g • x) ∂(ρ : Measure X))) := by
    simpa only [ProbabilityMeasure.toMeasure_map,
      integral_map (f := fun x => f (g • x)) (hp _).aemeasurable
        (f.continuous.comp (continuous_const_smul g)).aestronglyMeasurable] using hpleft
  have hqint : Tendsto (fun i => ∫ z, f (q i z) ∂(taus i : Measure Z)) l
      (𝓝 (∫ x, f x ∂(ρ : Measure X))) := by
    simpa only [ProbabilityMeasure.toMeasure_map,
      integral_map (f := fun x => f x) (hq _).aemeasurable
        f.continuous.aestronglyMeasurable] using hqleft
  have hdiff : Tendsto (fun i => (∫ z, f (q i z) ∂(taus i : Measure Z)) -
      ∫ z, f (g • p i z) ∂(taus i : Measure Z)) l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    let U : Set G := {a | ∀ x, dist (f x) (f (a • x)) < ε / 2}
    have hU : U ∈ 𝓝 (1 : G) :=
      Metric.tendstoUniformly_iff.mp
        (compact_observable_smul_tendstoUniformly (G := G) f f.continuous
          f.hasCompactSupport) (ε / 2) hhalf
    filter_upwards [hsmall U hU, hpair] with i hi hpairi
    have hqi : Integrable (fun z => f (q i z)) (taus i : Measure Z) :=
      (f.toBoundedContinuousFunction.integrable
        (μ := (taus i : Measure Z).map (q i))).comp_measurable (hq i)
    have hpi : Integrable (fun z => f (g • p i z)) (taus i : Measure Z) :=
      (fg.integrable (μ := (taus i : Measure Z).map (p i))).comp_measurable (hp i)
    rw [Real.dist_eq, sub_zero, ← integral_sub hqi hpi]
    have hb : ∀ᵐ z ∂(taus i : Measure Z),
        ‖f (q i z) - f (g • p i z)‖ ≤ ε / 2 := by
      filter_upwards [hi, hpairi] with z hz he
      rw [he, Real.norm_eq_abs]
      simpa only [Real.dist_eq, abs_sub_comm] using (hz (g • p i z)).le
    have hn := norm_integral_le_of_norm_le_const hb
    have hm : (taus i : Measure Z).real univ = 1 := by simp
    rw [hm, mul_one, Real.norm_eq_abs] at hn
    exact hn.trans_lt (by linarith)
  have he := tendsto_nhds_unique (hqint.sub hpint) hdiff
  rw [integral_map (f := fun x => f x) (continuous_const_smul g).measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  exact (sub_eq_zero.mp he).symm

end DukePrimeDegree

end

end OAI
