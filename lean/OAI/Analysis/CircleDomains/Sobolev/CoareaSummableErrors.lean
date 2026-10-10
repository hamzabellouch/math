import OAI.Analysis.CircleDomains.Sobolev.SobolevScalarCoarea
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

/-! One null exceptional set controls all errors in a summable smooth
approximation on every full pointwise level. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem coarea_summable_errors
    (hcoarea : PlanarSobolevCoarea)
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V v univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hb : IsBounded E)
    (e : ℕ → EuclideanPlane → ℝ≥0∞) (he : ∀ n, Measurable (e n))
    (hsum : (∑' n, ∫⁻ p in E, e n p * ENNReal.ofReal ‖V p‖) < ∞) :
    ∀ᵐ t ∂volume,
      (∑' n, sobolevLevelIntegral E v (e n) t) < ∞ ∧
      Tendsto (fun n => sobolevLevelIntegral E v (e n) t) atTop (𝓝 0) := by
  have hm (n : ℕ) := (hcoarea v hv V hw hLp E hE hb (e n) (he n)).1
  have hi : (∫⁻ t, ∑' n, sobolevLevelIntegral E v (e n) t) < ∞ := by
    rw [lintegral_tsum hm]
    convert hsum using 1
    congr 1
    funext n
    exact (hcoarea v hv V hw hLp E hE hb (e n) (he n)).2
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hi.ne] with t ht
  exact ⟨ht, ENNReal.tendsto_atTop_zero_of_tsum_ne_top ht.ne⟩

end CircleDomainRigidity

end

end OAI
