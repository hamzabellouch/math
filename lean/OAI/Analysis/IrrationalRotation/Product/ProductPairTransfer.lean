import OAI.Analysis.IrrationalRotation.Product.ProductPairRatios
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingTrimming
import OAI.Analysis.IrrationalRotation.Operators.OperatorCompactTransfer

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductModel

theorem ae_ratio_identity_of_positive_ordered_orbit_support
    (θ c : ℕ → ℝ) (F : Base → Fiber →L[ℂ] Fiber)
    (horbit : ∀ n : ℕ, 0 < n → ∀ᵐ x ∂baseMeasure,
      Ordered x (rotationIterate θ (n : ℤ) x) →
        (1 - F (rotationIterate θ (n : ℤ) x)) *
          ratioDiagonal θ c x (rotationIterate θ (n : ℤ) x) * F x = 0)
    (ν : Measure EndpointPair) (hfst : ν.map Prod.fst ≪ baseMeasure)
    (hsupp : SupportedOnPositiveOrderedOrbitPairs θ ν) :
    ∀ᵐ xy ∂ν, (1 - F xy.2) * ratioDiagonal θ c xy.1 xy.2 * F xy.1 = 0 := by
  have hall : ∀ᵐ x ∂baseMeasure, ∀ n : ℕ, 0 < n →
      Ordered x (rotationIterate θ (n : ℤ) x) →
        (1 - F (rotationIterate θ (n : ℤ) x)) *
          ratioDiagonal θ c x (rotationIterate θ (n : ℤ) x) * F x = 0 := by
    apply ae_all_iff.mpr
    intro n
    by_cases hn : 0 < n
    · exact (horbit n hn).mono (fun x hx _ => hx)
    · exact Filter.Eventually.of_forall (fun _ h => (hn h).elim)
  have hpull := ae_of_ae_map measurable_fst.aemeasurable (hfst.ae_le hall)
  obtain ⟨N, hN, hsupp⟩ := hsupp
  filter_upwards [hpull, hsupp] with xy hx hxy
  obtain ⟨horder, n, hn, heq⟩ := hxy
  rw [heq] at horder ⊢
  exact hx n (hN n hn) horder

theorem pairIdentity_of_orderedOrbitSampling
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (F : Base → Fiber →L[ℂ] Fiber)
    (hproj : ∀ x, IsStarProjection (F x))
    (hFm : ∀ v : Fiber, StronglyMeasurable (fun x => F x v))
    (horbit : ∀ n : ℕ, 0 < n → ∀ᵐ x ∂baseMeasure,
      Ordered x (rotationIterate θ (n : ℤ) x) →
        (1 - F (rotationIterate θ (n : ℤ) x)) *
          ratioDiagonal θ c x (rotationIterate θ (n : ℤ) x) * F x = 0)
    (I : Finset ℕ) (hsampling : OrderedOrbitSampling θ I) :
    ∀ᵐ xy ∂triangularLaw I, PairIdentity θ c F xy := by
  obtain ⟨η, hfinite, hsupp, hL2, hweak⟩ := hsampling
  let ηf : ℕ → FiniteMeasure EndpointPair := fun l => ⟨η l, hfinite l⟩
  let ν : FiniteMeasure EndpointPair := ⟨triangularLaw I, Sampling.triangularLaw_finite I⟩
  have hconv : Tendsto ηf atTop (𝓝 ν) :=
    (weaklyConverges_iff_tendsto ηf ν).mp hweak
  have horder : ∀ l, ∀ᵐ xy ∂η l, Ordered xy.1 xy.2 := by
    intro l
    obtain ⟨N, hN, hs⟩ := hsupp l
    exact hs.mono (fun _ h => h.1)
  have hratio := hL2.ae_all_cocycleRatio_bounds θ c hθ0 hθ hc horder
  have hlimit := triangularLaw_ae_all_cocycleRatio_bounds θ c hθ0 hθ hc I
  have hac := hL2.uniformlyAbsolutelyContinuous
  have hzero : ∀ l, ∀ᵐ xy ∂η l,
      (1 - F xy.2) * ratioDiagonal θ c xy.1 xy.2 * F xy.1 = 0 := by
    intro l
    obtain ⟨H, hH, hdens⟩ := hL2
    obtain ⟨f, g, hf, hg, hmf, hmg, hbf, hbg⟩ := hdens l
    apply ae_ratio_identity_of_positive_ordered_orbit_support θ c F horbit (η l)
    · rw [hmf]
      exact withDensity_absolutelyContinuous _ _
    · exact hsupp l
  have htransfer := CompactTransfer.compact_operator_transfer baseMeasure F hproj
    (fun k => ProductCocycle.cocycleVersion θ c k)
    (fun k x => ProductCocycle.cocycleVersion_pos θ c k x)
    (fun k => ProductCocycle.measurable_cocycleVersion θ c k)
    (fun k => (hFm (lp.single 2 k 1)).measurable)
    hconv hac.1 hac.2 1 zero_lt_one
    (fun l k => (hratio l).mono (fun xy h => (h k).2))
    (fun k => hlimit.mono (fun xy h => (h k).2))
    (fun l => (hzero l).mono (fun xy h => by
      simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc,
        ProductModel.ratioDiagonal, Invariant233.ratioDiagonal, cocycleRatio] using h))
  filter_upwards [hlimit, htransfer] with xy hr hz
  refine ⟨hr, ?_⟩
  simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc,
    ProductModel.ratioDiagonal, Invariant233.ratioDiagonal, cocycleRatio] using hz

end Invariant233.ProductModel

end

end OAI
