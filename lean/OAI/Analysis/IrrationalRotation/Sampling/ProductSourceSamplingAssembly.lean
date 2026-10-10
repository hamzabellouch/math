import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingTailReindex
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingScaleTrimming
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingWeightAssembly
import OAI.Analysis.IrrationalRotation.Model.ProductScaleSampling

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Invariant233.ProductModel.SamplingWeights

theorem orderedOrbitSampling_of_source_limits
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ)
    (hN : ∀ᶠ j in atTop, ProductSamplingPowersAt p j (N j))
    (θ : ℕ → ℝ) (I : Finset ℕ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (hθblock : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ≤ 2 / ((p.m j : ℝ) * p.K j))
    (hL2 : HasUniformL2Marginals (fun j =>
      TailTrimming.orbitAverageMeasure θ (N j) (fun n x => ENNReal.ofReal
        (orbitWeight (Finset.range (p.prefixCount (j + 1))) I
          ((p.m j : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m j : ℝ) ^ 2) θ n x))))
    (hweak : WeaklyConverges (fun j =>
      TailTrimming.orbitAverageMeasure θ (N j) (fun n x => ENNReal.ofReal
        (orbitWeight (Finset.range (p.prefixCount (j + 1))) I
          ((p.m j : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m j : ℝ) ^ 2) θ n x)))
      (triangularLaw I)) :
    OrderedOrbitSampling θ I := by
  let D (j : ℕ) := Finset.range (p.prefixCount (j + 1))
  let h (j : ℕ) := (p.m j : ℝ) ^ (-(3 / 5 : ℝ))
  let α (j : ℕ) := 1 / (p.m j : ℝ) ^ 2
  let M (j : ℕ) := ⌊(p.m j : ℝ) ^ ((7 / 10 : ℝ) * p.m j)⌋₊
  have hh1 (j : ℕ) : h j ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast (show 1 ≤ p.m j by have := hp.m_ge_100 j; omega)
    · norm_num
  apply TailTrimming.orderedOrbitSampling_of_eventually_prefix_samples θ I hθ0 D N M
    (fun j n x => ENNReal.ofReal (prefixWeight (D j) I (h j) (α j) θ n x))
  · exact Filter.Eventually.of_forall (fun j n _ =>
      (measurable_prefixWeight (D j) I (h j) (α j) θ n).ennreal_ofReal)
  · filter_upwards [hN] with j hj
    exact hj.positive
  · filter_upwards [hN] with j hj
    exact fun n hn => Nat.le_floor (hj.range n hn).2
  · apply Filter.Eventually.of_forall
    intro j n hn
    simpa only [prefixWeight_restrict] using orbitWeight_ae_prefix_order (D j) I (hh1 j) θ n
  · simpa only [prefixWeight_restrict, D, h, α] using hL2
  · simpa only [prefixWeight_restrict, D, h, α] using hweak
  · apply TailTrimming.source_horizon_angle_tail_tendsto_zero hp θ hθ0 hθsum hθblock M
    intro j
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end Invariant233.ProductModel.SamplingWeights

end

end OAI
