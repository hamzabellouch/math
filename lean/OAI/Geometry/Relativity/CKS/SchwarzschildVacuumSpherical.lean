import OAI.Geometry.Relativity.CKS.SchwarzschildSpherical
import OAI.Geometry.Relativity.CKS.SchwarzschildVacuumRound

namespace OAI

noncomputable section
open Set Filter CKSLorentz CKSCalculus CKSRealizedRound CKSAngularGeometry CKSCartesianOuter
open CKSSphericalChart
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CKSSchwarzschild

lemma spherical_vacuum_regular {m : ℝ} {x : PhysicalPoint} (hx : 0 < x 0)
    (hs : Real.sin (x 1) ≠ 0) (hp : 0 < lapseSquared m (x 0)) :
    CKSLocalBending.DEC
      (physicalMetricJet (spatialCoefficients (cartMetric m)) (sphericalMap x))
      (physicalTensorJet (spatialCoefficients (cartTensor m)) (sphericalMap x)) ∧
    (physicalMetricJet (spatialCoefficients (cartMetric m)) (sphericalMap x)).energy
      (physicalTensorJet (spatialCoefficients (cartTensor m)) (sphericalMap x)) = 0 := by
  have hv (y : PhysicalPoint) := (velocity_smooth m).contDiffAt (x := y 0)
  have hpx : 0 < CKSRealizedRound.radicand (fun _ => m) (velocity m) x := by
    rwa [round_radicand_eq]
  have hreg : ∀ᶠ y in 𝓝 x, 0 < y 0 ∧ Real.sin (y 1) ≠ 0 ∧
      0 < CKSRealizedRound.radicand (fun _ => m) (velocity m) y := by
    filter_upwards [(coord 0).continuous.continuousAt (x := x) |>.eventually (isOpen_Ioi.mem_nhds hx),
      (Real.continuous_sin.comp (coord 1).continuous).continuousAt (x := x) |>.eventually_ne hs,
      (contDiffAt_radicand (contDiffAt_const (c := m)) (hv x) hx.ne').continuousAt.eventually (isOpen_Ioi.mem_nhds hpx)]
      with y hy hsy hpy
    exact ⟨hy,hsy,hpy⟩
  have hEqG : coordinatePullback sphericalMap (spatialCoefficients (cartMetric m)) =ᶠ[𝓝 x]
      outerMetric (fun _ => m) (velocity m) := by
    filter_upwards [hreg] with y hy
    exact spherical_metric_pullback hy.1 ((round_radicand_eq m y) ▸ hy.2.2)
  have hEqK : coordinatePullback sphericalMap (spatialCoefficients (cartTensor m)) =ᶠ[𝓝 x]
      CKSRealizedRound.tensor (CKSRealizedRound.lapse (fun _ => m) (velocity m))
        (velocity m) (radial (deriv (velocity m))) (fun _ => 0) (fun _ => 0) := by
    filter_upwards [hreg] with y hy
    exact spherical_tensor_pullback hy.1 ((round_radicand_eq m y) ▸ hy.2.2)
  let frame : LocalFrame := fun i y => adaptedFrame
    (CKSRealizedRound.lapse (fun _ => m) (velocity m) y) (y 0^2 • sphericalAngularMetric y) 0 i
  have hFrame : ∀ᶠ y in 𝓝 x, SmoothOrthonormalAt
      (coordinatePullback sphericalMap (spatialCoefficients (cartMetric m))) frame y := by
    filter_upwards [hreg,hEqG.eventually_nhds] with y hy heq
    exact (round_smoothOrthonormalAt (contDiffAt_const (c := m)) (hv y) hy.1.ne' hy.2.1 hy.2.2).congr_metric heq
  have hu := contDiffAt_lapse (contDiffAt_const (c := m)) (hv x) hx.ne' hpx
  have hK := (tensor_contDiffAt hu (hv x)
    (contDiffAt_radial (velocity_deriv_smooth m).contDiffAt)
    (contDiffAt_const (c := 0)) (contDiffAt_const (c := 0))
    (CKSRealizedRound.lapse_pos hpx).ne').congr_of_eventuallyEq hEqK
  have hsymm : (coordinatePullback sphericalMap (spatialCoefficients (cartTensor m)) x).IsHermitian := by
    rw [hEqK.self_of_nhds]
    exact CKSRealizedRound.tensor_hermitian ..
  have hdec := local_coordinate_DEC_pushforward (sphericalChart x hx.ne' hs)
    (spatialCoefficients (cartMetric m)) (spatialCoefficients (cartTensor m)) frame
    (sphericalChart_mem x hx.ne' hs) (Eventually.of_forall fun y => sphericalMap_smooth.contDiffAt)
    (sphericalChart_inverse_smooth x hx.ne' hs) hFrame hK hsymm
  have hen := local_coordinate_energy_pushforward (sphericalChart x hx.ne' hs)
    (spatialCoefficients (cartMetric m)) (spatialCoefficients (cartTensor m)) frame
    (sphericalChart_mem x hx.ne' hs) (Eventually.of_forall fun y => sphericalMap_smooth.contDiffAt)
    (sphericalChart_inverse_smooth x hx.ne' hs) hFrame hK hsymm
  change CKSLocalBending.DEC (physicalMetricJet (spatialCoefficients (cartMetric m)) (sphericalMap x))
    (physicalTensorJet (spatialCoefficients (cartTensor m)) (sphericalMap x)) ↔
    CKSLocalBending.DEC (physicalMetricJet (coordinatePullback sphericalMap (spatialCoefficients (cartMetric m))) x)
    (physicalTensorJet (coordinatePullback sphericalMap (spatialCoefficients (cartTensor m))) x) at hdec
  change (physicalMetricJet (spatialCoefficients (cartMetric m)) (sphericalMap x)).energy
    (physicalTensorJet (spatialCoefficients (cartTensor m)) (sphericalMap x)) =
    (physicalMetricJet (coordinatePullback sphericalMap (spatialCoefficients (cartMetric m))) x).energy
    (physicalTensorJet (coordinatePullback sphericalMap (spatialCoefficients (cartTensor m))) x) at hen
  rw [physicalMetricJet_congr hEqG,physicalTensorJet_congr hEqK] at hdec hen
  obtain ⟨hC,hJ⟩ := radial_round_vacuum (m := m) (hv x) hx.ne' hs hpx
  refine ⟨hdec.mpr ?_,hen.trans hC⟩
  unfold CKSLocalBending.DEC CKSLocalBending.momentumSq
  change Real.sqrt (∑ i, ∑ j, _ * (tensorJet _ _ _ _ _ x |> (metricJet _ x).momentum) i *
    (tensorJet _ _ _ _ _ x |> (metricJet _ x).momentum) j) ≤ _
  simp only [hJ,Pi.zero_apply,mul_zero,Finset.sum_const_zero,Real.sqrt_zero]
  exact hC.ge
end CKSSchwarzschild

end

end OAI
