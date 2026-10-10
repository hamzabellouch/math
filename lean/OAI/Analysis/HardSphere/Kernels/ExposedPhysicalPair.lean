import Mathlib
import OAI.Analysis.HardSphere.Kernels.ParameterPair
import OAI.Analysis.HardSphere.Kernels.ExposedTrials
import OAI.Analysis.HardSphere.Bridges.LocalReference

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison
variable {E : Type*} [MeasurableSpace E]

def parameterTrialKernel (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z) :
    Kernel (E×Point) C(Time,Point) :=
  (exposedTrialKernel t).comap (fun p ↦ (y p.1,z p.1,p.2))
    ((hy.comp measurable_fst).prodMk ((hz.comp measurable_fst).prodMk measurable_snd))
instance parameterTrialKernel_markov (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z) :
    IsMarkovKernel (parameterTrialKernel t y z hy hz) := inferInstanceAs
      (IsMarkovKernel ((exposedTrialKernel t).comap _ _))
lemma parameterTrialKernel_apply (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z)
    (e : E) (u : Point) : parameterTrialKernel t y z hy hz (e,u)=trialKernel t (y e) (z e) u :=
  exposedTrialKernel_apply _ _ _ _

def exposedSuccess (S : Set (E×C(Time,Point))) : Set ((E×Point)×C(Time,Point)) :=
  (fun p ↦ (p.1.1,p.2)) ⁻¹' S
lemma exposedSuccess_measurable {S : Set (E×C(Time,Point))} (hS : MeasurableSet S) :
    MeasurableSet (exposedSuccess S) := hS.preimage (by fun_prop)

lemma parameterTrialSuccess_apply (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z)
    (S : Set (E×C(Time,Point))) (hS : MeasurableSet S) (e : E) (u : Point) :
    parameterSuccessKernel (parameterTrialKernel t y z hy hz) (exposedSuccess S)
      (exposedSuccess_measurable hS) (e,u)=
    successKernel (trialKernel t (y e) (z e)) (Prod.mk e ⁻¹' S)
      (hS.preimage measurable_prodMk_left) u := by
  rw [parameterSuccessKernel_apply,successKernel_apply,parameterTrialKernel_apply]
  rfl

def exposedPairedTrialKernel (Q : Kernel E Point) [IsFiniteKernel Q] (t : ℝ)
    (y z y' z' : E→Point) (hy : Measurable y) (hz : Measurable z)
    (hy' : Measurable y') (hz' : Measurable z')
    (S T : Set (E×C(Time,Point))) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    Kernel E (C(Time,Point)×(Point×C(Time,Point))) :=
  (parameterPairedKernel Q (parameterTrialKernel t y z hy hz) (parameterTrialKernel t y' z' hy' hz')
    (exposedSuccess S) (exposedSuccess T) (exposedSuccess_measurable hS) (exposedSuccess_measurable hT)).map
    (fun p ↦ (p.2.1,(p.1,p.2.2)))

lemma exposedPairedTrialKernel_apply (Q : Kernel E Point) [IsFiniteKernel Q] (t : ℝ)
    (y z y' z' : E→Point) (hy : Measurable y) (hz : Measurable z)
    (hy' : Measurable y') (hz' : Measurable z')
    (S T : Set (E×C(Time,Point))) (hS : MeasurableSet S) (hT : MeasurableSet T) (e : E) :
    exposedPairedTrialKernel Q t y z y' z' hy hz hy' hz' S T hS hT e=
      (pairedFactor (Q e) (trialKernel t (y e) (z e)) (trialKernel t (y' e) (z' e))
        (Prod.mk e ⁻¹' S) (Prod.mk e ⁻¹' T)
        (hS.preimage measurable_prodMk_left) (hT.preimage measurable_prodMk_left)).map
        (fun p ↦ (p.2.1,(p.1,p.2.2))) := by
  rw [exposedPairedTrialKernel,Kernel.map_apply _ (by fun_prop)]
  congr 1
  ext B hB
  rw [parameterPairedKernel,Kernel.compProd_apply hB,pairedFactor,Measure.compProd_apply hB]
  apply lintegral_congr
  intro u
  rw [Kernel.prod_apply,Kernel.prod_apply,parameterTrialSuccess_apply,parameterTrialSuccess_apply] <;> assumption

lemma exposedPairedTrialKernel_physical (Q : Kernel E Point) [IsFiniteKernel Q] (t : ℝ)
    (y z y' z' : E→Point) (hy : Measurable y) (hz : Measurable z)
    (hy' : Measurable y') (hz' : Measurable z')
    (S T : Set (E×C(Time,Point))) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (A : E→Set Point) (hQ : ∀e,Q e=targetUniform (A e)) (e : E) :
    exposedPairedTrialKernel Q t y z y' z' hy hz hy' hz' S T hS hT e=
      pairedTrialLaw t (y e) (z e) (y' e) (z' e) (A e)
        (Prod.mk e ⁻¹' S) (Prod.mk e ⁻¹' T)
        (hS.preimage measurable_prodMk_left) (hT.preimage measurable_prodMk_left) := by
  rw [exposedPairedTrialKernel_apply,hQ]
  rfl

end HardSphere.Bridge

end
end

end

end OAI
