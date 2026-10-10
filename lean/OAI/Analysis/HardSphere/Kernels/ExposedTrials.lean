import Mathlib
import OAI.Analysis.HardSphere.Bridges.SupplyIntegral

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff
attribute [local irreducible] torusDistance

lemma trialPath_all_continuous (t : ℝ) :
    Continuous (fun p : (Point×(Point×Point))×(Noise×Noise) ↦
      trialPath t p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ((Point×(Point×Point))×(Noise×Noise))×Time ↦ fun j ↦
    (mean p.1.1.1 p.1.1.2.2 (leftTime p.2) j+Real.sqrt (2*t)*center (p.1.2.1 j) (leftTime p.2))+
    (mean p.1.1.2.1 p.1.1.2.2 (reverseTime (rightTime p.2)) j+
      Real.sqrt (2*t)*center (p.1.2.2 j) (reverseTime (rightTime p.2)))-p.1.1.2.2 j)
  unfold mean
  have hl := leftTime_continuous
  have hr := reverseTime.continuous.comp rightTime_continuous
  have hc := center_continuous
  fun_prop

def exposedTrialKernel (t : ℝ) : Kernel (Point×(Point×Point)) C(Time,Point) :=
  ((Kernel.deterministic id measurable_id).prod
      (Kernel.const (Point×(Point×Point)) (law.prod law))).map
    (fun p ↦ trialPath t p.1.1 p.1.2.1 p.1.2.2 p.2)

instance exposedTrialKernel_markov (t : ℝ) : IsMarkovKernel (exposedTrialKernel t) := by
  unfold exposedTrialKernel
  exact Kernel.IsMarkovKernel.map _ (trialPath_all_continuous t).measurable

lemma exposedTrialKernel_apply (t : ℝ) (y z u : Point) :
    exposedTrialKernel t (y,z,u)=trialKernel t y z u := by
  rw [exposedTrialKernel,Kernel.map_apply _ (trialPath_all_continuous t).measurable,
    Kernel.prod_apply,Kernel.deterministic_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (trialPath_all_continuous t).measurable
      (measurable_const.prodMk measurable_id : Measurable (Prod.mk (id (y,z,u)))),
    trialKernel_apply]
  rfl

lemma trialCollision_joint_closed {L : Length} (r : ℝ) :
    IsClosed {p : ConfigurationPath 1 L×C(Time,Point) | TrialCollision r p.1 p.2} := by
  let E : Set ((ConfigurationPath 1 L×C(Time,Point))×Time) :=
    {p | torusDistance L (projectPoint L (p.1.2 p.2)) (p.1.1 p.2 0) ≤ r}
  have hE : IsClosed E := by
    apply isClosed_le _ continuous_const
    apply (torusDistance_continuous_pair L).comp (f := fun p : (ConfigurationPath 1 L×C(Time,Point))×Time ↦
      (projectPoint L (p.1.2 p.2),p.1.1 p.2 0))
    apply Continuous.prodMk
    · change Continuous (fun p : (ConfigurationPath 1 L×C(Time,Point))×Time ↦
        fun j : Fin 3 ↦ (p.1.2 p.2 j:AddCircle L.val))
      fun_prop
    · fun_prop
  convert isClosedMap_fst_of_compactSpace E hE using 1
  ext p
  simp only [TrialCollision,mem_ofPred_eq,mem_image,E]
  exact ⟨fun ⟨s,hs⟩ ↦ ⟨(p,s),hs,rfl⟩,fun ⟨⟨q,s⟩,hs,hq⟩ ↦ by
    change q=p at hq
    subst q
    exact ⟨s,hs⟩⟩

lemma successExcept_joint_measurable {L : Length} {N : ℕ} (n : ℕ)
    (r R C S : ℝ) (w : Time) (v : Point) (i : Fin N) :
    MeasurableSet {p : (Fin N → ConfigurationPath 1 L)×C(Time,Point) |
      p.2∈SuccessExcept n r R C S w v p.1 i} := by
  have hm (j : Fin N) : Measurable (fun p : (Fin N → ConfigurationPath 1 L)×C(Time,Point) ↦
      (p.1 j,p.2)) := ((measurable_pi_apply j).comp measurable_fst).prodMk measurable_snd
  have hh : MeasurableSet {p : (Fin N → ConfigurationPath 1 L)×C(Time,Point) |
      ∀j,j≠i→¬TrialCollision r (p.1 j) p.2} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
      ((trialCollision_joint_closed r).measurableSet.preimage (hm j)).compl
  exact ((trialCutoff_measurable L n r R C w S v).preimage measurable_snd).inter hh

end HardSphere.Bridge

end
end

end

end OAI
