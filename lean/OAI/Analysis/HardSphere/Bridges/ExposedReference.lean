import Mathlib
import OAI.Analysis.HardSphere.Kernels.ExposedPhysicalPair

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison
variable {E : Type*} [MeasurableSpace E]

lemma leg_all_continuous (t : ℝ) :
    Continuous (fun p : (Point×Point)×Noise ↦ leg t p.1.1 p.1.2 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ((Point×Point)×Noise)×Time ↦ fun j ↦
    mean p.1.1.1 p.1.1.2 p.2 j+Real.sqrt (2*t)*p.1.2 j p.2)
  unfold mean
  fun_prop

def exposedBridgeKernel (t : ℝ) : Kernel (Point×Point) C(Time,Point) :=
  ((Kernel.deterministic id measurable_id).prod (Kernel.const (Point×Point) law)).map
    (fun p ↦ leg t p.1.1 p.1.2 p.2)
instance exposedBridgeKernel_markov (t : ℝ) : IsMarkovKernel (exposedBridgeKernel t) := by
  unfold exposedBridgeKernel
  exact Kernel.IsMarkovKernel.map _ (leg_all_continuous t).measurable
lemma exposedBridgeKernel_apply (t : ℝ) (y z : Point) :
    exposedBridgeKernel t (y,z)=law.map (leg t y z) := by
  rw [exposedBridgeKernel,Kernel.map_apply _ (leg_all_continuous t).measurable,
    Kernel.prod_apply,Kernel.deterministic_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (leg_all_continuous t).measurable
      (measurable_const.prodMk measurable_id : Measurable (Prod.mk (id (y,z))))]
  rfl

def parameterBridgeKernel (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z) :
    Kernel E C(Time,Point) := (exposedBridgeKernel t).comap (fun e ↦ (y e,z e)) (hy.prodMk hz)
instance parameterBridgeKernel_markov (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z) :
    IsMarkovKernel (parameterBridgeKernel t y z hy hz) := inferInstanceAs
      (IsMarkovKernel ((exposedBridgeKernel t).comap _ _))
lemma parameterBridgeKernel_apply (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z) (e : E) :
    parameterBridgeKernel t y z hy hz e=law.map (leg t (y e) (z e)) := exposedBridgeKernel_apply _ _ _

def parameterIndividualReference (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z)
    (S : Set (E×C(Time,Point))) (hS : MeasurableSet S) : Kernel E C(Time,Point) :=
  parameterSuccessKernel (parameterBridgeKernel (2*t) y z hy hz) S hS
instance parameterIndividualReference_finite (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z)
    (S : Set (E×C(Time,Point))) (hS : MeasurableSet S) :
    IsFiniteKernel (parameterIndividualReference t y z hy hz S hS) := inferInstanceAs
      (IsFiniteKernel (parameterSuccessKernel _ _ _))
lemma parameterIndividualReference_apply (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z)
    (S : Set (E×C(Time,Point))) (hS : MeasurableSet S) (e : E) :
    parameterIndividualReference t y z hy hz S hS e=individualReference t (y e) (z e) (Prod.mk e ⁻¹' S) := by
  rw [parameterIndividualReference,parameterSuccessKernel_apply,parameterBridgeKernel_apply]
  rfl

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison
variable {E : Type*} [MeasurableSpace E]
  [MeasurableSpace.CountableOrCountablyGenerated E C(Time,Point)]

lemma exposed_physical_auxiliary
    (Q : Kernel E Point) [IsFiniteKernel Q] {t C : ℝ} (ht : 0<t) (hC : 0≤C)
    (y z y' z' : E→Point) (hy : Measurable y) (hz : Measurable z)
    (hy' : Measurable y') (hz' : Measurable z')
    (S T : Set (E×C(Time,Point))) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (A : E→Set Point) (hA : ∀e,MeasurableSet (A e))
    (hAf : ∀e,volume (A e)≠⊤) (hQ : ∀e,Q e=targetUniform (A e))
    {a c : ℝ≥0∞} (ha : 0<a) (hc : 0<c) (hvol : ∀e,a≤volume (A e))
    (hb : ∀e u,u∈A e → ‖u-(fun j ↦ (y e j+z e j)/2)‖≤C)
    (hsuccess : ∀e,∀ᵐu ∂targetUniform (A e),c≤trialKernel t (y e) (z e) u (Prod.mk e ⁻¹' S))
    (hother : ∀e,∀ᵐu ∂targetUniform (A e),0<trialKernel t (y' e) (z' e) u (Prod.mk e ⁻¹' T)) :
    ∃ κ : Kernel (E×C(Time,Point)) (Point×C(Time,Point)), IsFiniteKernel κ ∧
      (parameterIndividualReference t y z hy hz S hS).compProd κ=
        exposedPairedTrialKernel Q t y z y' z' hy hz hy' hz' S T hS hT ∧
      (∀e f,κ (e,f) univ≤c⁻¹*(a⁻¹*(midpointLower t C)⁻¹)) ∧
      (∀e,∫⁻f,κ (e,f) univ ∂parameterIndividualReference t y z hy hz S hS e=1) := by
  have hA0 (e : E) : volume (A e)≠0 := (ha.trans_le (hvol e)).ne'
  let P := parameterIndividualReference t y z hy hz S hS
  let ρ := exposedPairedTrialKernel Q t y z y' z' hy hz hy' hz' S T hS hT
  let _ : IsMarkovKernel P := by
    constructor
    intro e
    change IsProbabilityMeasure (parameterIndividualReference t y z hy hz S hS e)
    rw [parameterIndividualReference_apply]
    exact individualReference_probability ht hC (y e) (z e) (hA e) (hA0 e) (hAf e) (hb e)
      (Prod.mk e ⁻¹' S) (hS.preimage measurable_prodMk_left) hc (hsuccess e)
  let _ : IsMarkovKernel ρ := by
    constructor
    intro e
    change IsProbabilityMeasure (exposedPairedTrialKernel Q t y z y' z' hy hz hy' hz' S T hS hT e)
    rw [exposedPairedTrialKernel_physical Q t y z y' z' hy hz hy' hz' S T hS hT A hQ]
    exact pairedTrialLaw_probability t (y e) (z e) (y' e) (z' e) (A e) (hA0 e) (hAf e)
      (Prod.mk e ⁻¹' S) (Prod.mk e ⁻¹' T)
      (hS.preimage measurable_prodMk_left) (hT.preimage measurable_prodMk_left)
      ((hsuccess e).mono (fun _ hu ↦ hc.trans_le hu)) (hother e)
  apply exists_parameter_auxiliary P ρ
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc.ne')
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr ha.ne')
        (ENNReal.inv_ne_top.mpr (midpointLower_pos ht C).ne'))
  · intro e
    change (ρ e).fst≤_ • P e
    dsimp [ρ,P]
    rw [exposedPairedTrialKernel_physical Q t y z y' z' hy hz hy' hz' S T hS hT A hQ,
      parameterIndividualReference_apply,
      pairedTrialLaw_fst t (y e) (z e) (y' e) (z' e) (A e) (hA0 e) (hAf e)
        (Prod.mk e ⁻¹' S) (Prod.mk e ⁻¹' T)
        (hS.preimage measurable_prodMk_left) (hT.preimage measurable_prodMk_left) (hother e)]
    apply (physical_trial_le_reference ht hC (y e) (z e) (hA e) (hAf e) (hb e)
      (Prod.mk e ⁻¹' S) (hS.preimage measurable_prodMk_left) (hsuccess e)).trans
    intro B
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul' (mul_le_mul' le_rfl
      (mul_le_mul' (ENNReal.inv_le_inv.mpr (hvol e)) le_rfl)) le_rfl

end HardSphere.Bridge

end
end

end

end OAI
