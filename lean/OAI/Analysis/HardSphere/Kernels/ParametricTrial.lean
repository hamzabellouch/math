import Mathlib
import OAI.Analysis.HardSphere.Kernels.TrialKernel
import OAI.Analysis.HardSphere.Bridges.GaussianMixture
import OAI.Analysis.HardSphere.Comparison.FiberNormalize

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

@[fun_prop] lemma trialPath_joint_continuous (t : ℝ) :
    Continuous (fun p : (Point×Point×Point)×(Noise×Noise) ↦
      trialPath t p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ((Point×Point×Point)×(Noise×Noise))×Time ↦ fun j ↦
    (mean p.1.1.1 p.1.1.2.2 (leftTime p.2) j+Real.sqrt (2*t)*center (p.1.2.1 j) (leftTime p.2))+
    (mean p.1.1.2.1 p.1.1.2.2 (reverseTime (rightTime p.2)) j+
      Real.sqrt (2*t)*center (p.1.2.2 j) (reverseTime (rightTime p.2)))-p.1.1.2.2 j)
  unfold mean
  have hl := leftTime_continuous
  have hr := reverseTime.continuous.comp rightTime_continuous
  have hc := center_continuous
  fun_prop

def allEndpointTrialKernel (t : ℝ) : Kernel (Point×Point×Point) C(Time,Point) :=
  ((Kernel.deterministic id measurable_id).prod (Kernel.const _ (law.prod law))).map
    (fun p ↦ trialPath t p.1.1 p.1.2.1 p.1.2.2 p.2)
instance allEndpointTrialKernel_markov (t : ℝ) : IsMarkovKernel (allEndpointTrialKernel t) := by
  unfold allEndpointTrialKernel
  exact Kernel.IsMarkovKernel.map _ (trialPath_joint_continuous t).measurable
lemma allEndpointTrialKernel_apply (t : ℝ) (y z u : Point) :
    allEndpointTrialKernel t (y,z,u)=trialKernel t y z u := by
  rw [allEndpointTrialKernel,Kernel.map_apply _ (trialPath_joint_continuous t).measurable,
    Kernel.prod_apply,Kernel.deterministic_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (trialPath_joint_continuous t).measurable
      (show Measurable (Prod.mk (id (y,z,u))) from measurable_prodMk_left),trialKernel_apply]
  rfl

variable {W : Type*} [MeasurableSpace W]
def parameterTrial (t : ℝ) (y z : W→Point) (hy : Measurable y) (hz : Measurable z) :
    Kernel (W×Point) C(Time,Point) :=
  (allEndpointTrialKernel t).comap (fun p ↦ (y p.1,z p.1,p.2))
    ((hy.comp measurable_fst).prodMk ((hz.comp measurable_fst).prodMk measurable_snd))
instance parameterTrial_markov (t : ℝ) (y z : W→Point) (hy : Measurable y) (hz : Measurable z) :
    IsMarkovKernel (parameterTrial t y z hy hz) := by unfold parameterTrial; infer_instance
lemma parameterTrial_apply (t : ℝ) (y z : W→Point) (hy : Measurable y) (hz : Measurable z)
    (w : W) (u : Point) : parameterTrial t y z hy hz (w,u)=trialKernel t (y w) (z w) u :=
  allEndpointTrialKernel_apply _ _ _ _

def parameterSuccess (t : ℝ) (y z : W→Point) (hy : Measurable y) (hz : Measurable z)
    (S : Set (W×C(Time,Point))) : Kernel (W×Point) C(Time,Point) :=
  fiberNormalize (parameterTrial t y z hy hz) {p | (p.1.1,p.2)∈S}
instance parameterSuccess_finite (t : ℝ) (y z : W→Point) (hy : Measurable y) (hz : Measurable z)
    (S : Set (W×C(Time,Point))) : IsFiniteKernel (parameterSuccess t y z hy hz S) := by
  unfold parameterSuccess; infer_instance
lemma parameterSuccess_apply (t : ℝ) (y z : W→Point) (hy : Measurable y) (hz : Measurable z)
    (S : Set (W×C(Time,Point))) (hS : MeasurableSet S) (w : W) (u : Point) :
    parameterSuccess t y z hy hz S (w,u)=
      successKernel (trialKernel t (y w) (z w)) {f | (w,f)∈S}
        (hS.preimage (measurable_const.prodMk measurable_id)) u := by
  have hC : MeasurableSet {p : (W×Point)×C(Time,Point) | (p.1.1,p.2)∈S} :=
    hS.preimage (measurable_fst.fst.prodMk measurable_snd)
  change (fiberRestrict _ _ (w,u) univ)⁻¹ • fiberRestrict _ _ (w,u)=_
  rw [fiberRestrict_apply _ hC,parameterTrial_apply,Measure.restrict_apply_univ]
  rfl

end HardSphere.Bridge

end
end

end

end OAI
