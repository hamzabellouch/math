import OAI.Analysis.CircleDomains.Sobolev.PlaneCovectorEnergy
import OAI.Analysis.CircleDomains.Topology.CircleChainRule
import OAI.Analysis.CircleDomains.Topology.PhysicalPlaneCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace OAI

/-! Transport the actual smoothed stream to the complex physical chart.
Its two L2 partial derivatives give finite full differential energy. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem complexPlaneCoordinates_symm_measurePreserving :
    MeasurePreserving complexPlaneCoordinates.symm volume volume := by
  exact euclideanPlaneCoordinates_symm_measurePreserving.comp
    Complex.volume_preserving_equiv_real_prod

theorem smooth_circle_complex_energy_finite
    {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω) (w : EuclideanPlane → UnitAddCircle)
    (hw : SmoothCircleOn w Ω)
    (hpartial : ∀ i : Fin 2, MemLp
      (fun x => circleFDeriv w x (EuclideanSpace.single i 1)) 2 (volume.restrict Ω)) :
    SmoothCircleOn (w ∘ complexPlaneCoordinates.symm) (complexPlaneCoordinates.symm ⁻¹' Ω) ∧
    (∫⁻ z in complexPlaneCoordinates.symm ⁻¹' Ω,
      ENNReal.ofReal ‖circleFDeriv (w ∘ complexPlaneCoordinates.symm) z‖ ^ 2) < ∞ := by
  let q := complexPlaneCoordinates.symm
  have hq : MeasurePreserving q volume volume := complexPlaneCoordinates_symm_measurePreserving
  have hmp := hq.restrict_preimage hΩ.measurableSet
  have henergy := lintegral_planeCovector_sq_lt_top (volume.restrict Ω) (circleFDeriv w) hpartial
  have hpull : (∫⁻ z, ENNReal.ofReal ‖circleFDeriv w (q z)‖ ^ 2
      ∂(volume.restrict (q ⁻¹' Ω))) =
      ∫⁻ x, ENNReal.ofReal ‖circleFDeriv w x‖ ^ 2 ∂(volume.restrict Ω) :=
    hmp.lintegral_comp_emb q.toHomeomorph.measurableEmbedding
      (fun x => ENNReal.ofReal ‖circleFDeriv w x‖ ^ 2)
  refine ⟨?_, ?_⟩
  · intro z hz a ha
    exact (hw (q z) hz a ha).comp z q.contDiff.contDiffAt
  · have hmajor : (∫⁻ z, ENNReal.ofReal ‖q.toContinuousLinearMap‖ ^ 2 *
        ENNReal.ofReal ‖circleFDeriv w (q z)‖ ^ 2 ∂(volume.restrict (q ⁻¹' Ω))) < ∞ := by
      rw [lintegral_const_mul' _ _ (by finiteness), hpull]
      exact ENNReal.mul_lt_top (by finiteness) henergy
    apply lt_of_le_of_lt (lintegral_mono_ae ?_) hmajor
    filter_upwards [ae_restrict_mem (hΩ.preimage q.continuous).measurableSet] with z hz
    rw [circleFDeriv_comp hΩ hw q.differentiableAt hz, q.fderiv]
    calc
      ENNReal.ofReal ‖(circleFDeriv w (q z)).comp q.toContinuousLinearMap‖ ^ 2 ≤
          (ENNReal.ofReal ‖circleFDeriv w (q z)‖ * ENNReal.ofReal ‖q.toContinuousLinearMap‖) ^ 2 := by
        rw [← ENNReal.ofReal_mul (norm_nonneg _)]
        exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (ContinuousLinearMap.opNorm_comp_le _ _)) 2
      _ = _ := by rw [mul_pow, mul_comm]

end CircleDomainRigidity

end

end OAI
