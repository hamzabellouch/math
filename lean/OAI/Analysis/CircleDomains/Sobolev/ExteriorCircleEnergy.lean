import OAI.Analysis.CircleDomains.Sobolev.ExteriorDerivativeMean

namespace OAI

/-! The angular energy of a principal exterior derivative is at least
one. The proof keeps the actual derivative and uses its exact mean. -/
open Set Filter Function Metric Asymptotics Bornology Real MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exterior_derivative_continuousOn_circle {F : ℂ → ℂ} {R r : ℝ}
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (hr : R < r) :
    ContinuousOn (deriv F) (sphere 0 r) := by
  apply (hF.deriv (isOpen_lt continuous_const continuous_norm)).continuousOn.mono
  intro z hz
  simpa only [mem_ofPred_eq, (mem_sphere_zero_iff_norm.mp hz)] using hr

lemma exterior_derivative_circle_energy {F : ℂ → ℂ} {R r : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (ht : Tendsto (fun z => F z-z) (cobounded ℂ) (𝓝 0)) (hr : R < r) :
    1 ≤ circleAverage (fun z => ‖deriv F z‖^2) 0 r := by
  have hrp : 0 < r := hR.trans hr
  have hc := exterior_derivative_continuousOn_circle hF hr
  have hci := hc.circleIntegrable hrp.le
  have hcre := Complex.continuous_re.comp_continuousOn hc
  have hm : circleAverage (fun z => (deriv F z).re) 0 r = 1 := by
    have he := Complex.reCLM.circleAverage_comp_comm hci
    change circleAverage (fun z => (deriv F z).re) 0 r =
      (circleAverage (deriv F) 0 r).re at he
    simpa only [exterior_derivative_circleAverage hR hF ht hr, Complex.one_re] using he
  have hc2 : CircleIntegrable (fun z => 2*(deriv F z).re-1) 0 r := ((continuousOn_const.mul hcre).sub continuousOn_const).circleIntegrable hrp.le
  have hcn : CircleIntegrable (fun z => ‖deriv F z‖^2) 0 r := (hc.norm.pow 2).circleIntegrable hrp.le
  have hcm : CircleIntegrable (fun z => 2*(deriv F z).re) 0 r :=
    (continuousOn_const.mul hcre).circleIntegrable hrp.le
  have hav : circleAverage (fun z => 2*(deriv F z).re-1) 0 r = 1 := by
    rw [circleAverage_fun_sub hcm
      (circleIntegrable_const 1 0 r)]
    have he : circleAverage (fun z => 2*(deriv F z).re) 0 r =
        2*circleAverage (fun z => (deriv F z).re) 0 r :=
      circleAverage_fun_smul (a := (2 : ℝ))
    rw [he, hm, circleAverage_const]
    norm_num
  rw [← hav]
  apply circleAverage_mono hc2 hcn
  intro z _
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg ((deriv F z).re-1), sq_nonneg (deriv F z).im]

end CircleDomainRigidity

end

end OAI
