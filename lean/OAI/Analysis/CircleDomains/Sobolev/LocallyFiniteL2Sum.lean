import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates
import Mathlib.MeasureTheory.Function.LpSpace.Complete

namespace OAI

/-! L² control of a pointwise finite sum by the sum of its local error
norms. This applies to the countable partition-of-unity error terms. -/

open Set Filter MeasureTheory Function
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem finiteSupport_hasSum_finsum {ι : Type*} (f : ι → ℝ)
    (hf : HasFiniteSupport f) : HasSum f (∑ᶠ i, f i) := by
  rw [← show (∑' i, f i) = ∑ᶠ i, f i from tsum_eq_finsum hf]
  exact (summable_of_hasFiniteSupport hf).hasSum

theorem aestronglyMeasurable_finsum_of_pointFinite
    {ι : Type*} [Countable ι] (μ : Measure EuclideanPlane)
    (f : ι → EuclideanPlane → ℝ) (hf : ∀i, AEStronglyMeasurable (f i) μ)
    (hfin : ∀x, HasFiniteSupport (fun i => f i x)) :
    AEStronglyMeasurable (fun x => ∑ᶠ i, f i x) μ := by
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
    (f := fun s x => ∑ i ∈ s, f i x)
  · intro s
    exact Finset.aestronglyMeasurable_fun_sum s (fun i _ => hf i)
  · exact Eventually.of_forall fun x => finiteSupport_hasSum_finsum _ (hfin x)

theorem eLpNorm_finsum_le_tsum_of_pointFinite
    {ι : Type*} [Countable ι] (μ : Measure EuclideanPlane)
    (f : ι → EuclideanPlane → ℝ) (hf : ∀i, AEStronglyMeasurable (f i) μ)
    (hfin : ∀x, HasFiniteSupport (fun i => f i x)) :
    eLpNorm (fun x => ∑ᶠ i, f i x) 2 μ ≤ ∑' i, eLpNorm (f i) 2 μ := by
  apply Lp.eLpNorm_le_of_ae_tendsto
    (u := (atTop : Filter (Finset ι)))
    (f := fun s x => ∑ i ∈ s, f i x)
  · apply Eventually.of_forall
    intro s
    have h := eLpNorm_sum_le (f := f) (s := s) (μ := μ) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have he : (fun x => ∑ i ∈ s, f i x) = ∑i ∈ s, f i := by
      ext x
      simp only [Finset.sum_apply]
    rw [he]
    exact h.trans (ENNReal.sum_le_tsum s)
  · intro s
    exact Finset.aestronglyMeasurable_fun_sum s (fun i _ => hf i)
  · exact aestronglyMeasurable_finsum_of_pointFinite μ f hf hfin
  · exact Eventually.of_forall fun x => finiteSupport_hasSum_finsum _ (hfin x)

end CircleDomainRigidity

end

end OAI
