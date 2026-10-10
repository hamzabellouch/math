import OAI.Analysis.CircleDomains.Sobolev.LocallySobolevACL
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

namespace OAI

/-! Exact local Sobolev coordinate integration with the actual weak
partial, now without any global support or global L2 hypothesis. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma locally_sobolev_coordinate_fundamentalTheorem {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R))) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ a b : ℝ,
      IntervalIntegrable (fun t => V (physicalCoordinateLine i y t) i) volume a b ∧
      (∫ t in a..b, V (physicalCoordinateLine i y t) i) =
        u (physicalCoordinateLine i y b)-u (physicalCoordinateLine i y a) := by
  filter_upwards [locally_sobolev_coordinate_absolutelyContinuous hu hw hLp i,
    locally_sobolev_coordinate_ae_hasDerivAt hu hw hLp i] with y hac hd
  have heq : (fun t => deriv (fun s => u (physicalCoordinateLine i y s)) t) =ᵐ[volume]
      fun t => V (physicalCoordinateLine i y t) i := hd.mono fun t ht => ht.deriv
  intro a b
  refine ⟨(hac a b).intervalIntegrable_deriv.congr_ae (ae_restrict_of_ae heq), ?_⟩
  rw [← intervalIntegral.integral_congr_ae_restrict (ae_restrict_of_ae heq)]
  exact (hac a b).integral_deriv_eq_sub

end CircleDomainRigidity

end

end OAI
