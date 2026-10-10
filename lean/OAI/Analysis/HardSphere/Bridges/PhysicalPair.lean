import Mathlib
import OAI.Analysis.HardSphere.Bridges.ExposedReference
import OAI.Analysis.HardSphere.Bridges.PeriodShift

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison

lemma trialConfined_joint_closed (L : Length) :
    IsClosed {p : Point × C(Time,Point) | TrialConfined L p.1 p.2} := by
  have he : {p : Point × C(Time,Point) | TrialConfined L p.1 p.2} =
      ⋂ s : Time, {p : Point × C(Time,Point) |
        ‖p.2 s-p.1‖≤10 ∧ torusDistance L (projectPoint L (p.2 s)) (projectPoint L p.1)≤10} := by
    ext p
    simp only [TrialConfined, mem_ofPred_eq, mem_iInter]
  rw [he]
  apply isClosed_iInter
  intro s
  change IsClosed ({p : Point × C(Time,Point) | ‖p.2 s-p.1‖≤(10:ℝ)} ∩
    {p | torusDistance L (projectPoint L (p.2 s)) (projectPoint L p.1)≤(10:ℝ)})
  apply IsClosed.inter
  · apply isClosed_le _ continuous_const
    fun_prop
  · apply isClosed_le _ continuous_const
    unfold torusDistance projectPoint
    fun_prop

def exposedPermitted {E J : Type*} {L : Length} (n : ℕ) (r R Creg S : ℝ)
    (w : Time) (y z v : E → Point) (F : E → J → ConfigurationPath 1 L) :
    Set (E × C(Time,Point)) :=
  {p | p.2 ∈ permittedPath n r R Creg S w (y p.1) (z p.1) (v p.1) (F p.1)}

lemma exposedPermitted_measurable {E J : Type*} [MeasurableSpace E] [Countable J]
    {L : Length} (n : ℕ) (r R Creg S : ℝ) (w : Time)
    (y z v : E → Point) (F : E → J → ConfigurationPath 1 L)
    (hy : Measurable y) (hz : Measurable z) (hv : Measurable v)
    (hF : ∀j, Measurable (fun e ↦ F e j)) :
    MeasurableSet (exposedPermitted n r R Creg S w y z v F) := by
  apply ((regular_measurable n r R Creg w S).preimage
    ((projectCurve_continuous L).measurable.comp measurable_snd)).inter
  apply ((trialConfined_joint_closed L).measurableSet.preimage
    ((hv.comp measurable_fst).prodMk measurable_snd)).inter
  apply MeasurableSet.inter
  · exact (measurableSet_eq_fun ((continuous_eval_const 0).measurable.comp measurable_snd)
      (hy.comp measurable_fst)).inter
      (measurableSet_eq_fun ((continuous_eval_const 1).measurable.comp measurable_snd)
        (hz.comp measurable_fst))
  · change MeasurableSet {p : E × C(Time,Point) | ∀j, ¬TrialCollision r (F p.1 j) p.2}
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun j ↦ ((trialCollision_joint_closed r).measurableSet.preimage
      (((hF j).comp measurable_fst).prodMk measurable_snd)).compl

lemma exposedPermitted_fiber {E J : Type*} {L : Length} (n : ℕ) (r R Creg S : ℝ)
    (w : Time) (y z v : E → Point) (F : E → J → ConfigurationPath 1 L) (e : E) :
    Prod.mk e ⁻¹' exposedPermitted n r R Creg S w y z v F =
      permittedPath n r R Creg S w (y e) (z e) (v e) (F e) := rfl

lemma individualReference_unshift (t : ℝ) (y z c : Point)
    (S T : Set C(Time,Point)) (hT : MeasurableSet T)
    (hST : ∀f, shiftPath c f ∈ T ↔ f ∈ S) :
    (individualReference t (y+c) (z+c) T).map (shiftPath (-c)) =
      individualReference t y z S := by
  rw [←individualReference_shift t y z c S T hT hST,
    Measure.map_map (shiftPath_continuous (-c)).measurable (shiftPath_continuous c).measurable]
  have he : shiftPath (-c) ∘ shiftPath c = id := by
    funext f
    exact shiftPath_cancel c f
  rw [he, Measure.map_id]

variable {E : Type*} [MeasurableSpace E]

def exposedPeriodPair (Q : Kernel E Point) [IsFiniteKernel Q] (t : ℝ)
    (y z y' z' : E → Point) (hy : Measurable y) (hz : Measurable z)
    (hy' : Measurable y') (hz' : Measurable z') (c : Point)
    (S U : Set (E × C(Time,Point))) (hS : MeasurableSet S) (hU : MeasurableSet U) :
    Kernel E (C(Time,Point) × C(Time,Point)) :=
  (exposedPairedTrialKernel Q t y z (fun e ↦ y' e+c) (fun e ↦ z' e+c)
    hy hz (hy'.add measurable_const) (hz'.add measurable_const) S U hS hU).map
    (fun p ↦ (p.1, shiftPath (-c) p.2.2))

lemma exposedPeriodPair_apply (Q : Kernel E Point) [IsFiniteKernel Q] (t : ℝ)
    (y z y' z' : E → Point) (hy : Measurable y) (hz : Measurable z)
    (hy' : Measurable y') (hz' : Measurable z') (c : Point)
    (S U : Set (E × C(Time,Point))) (hS : MeasurableSet S) (hU : MeasurableSet U)
    (A : E → Set Point) (hQ : ∀e, Q e=targetUniform (A e)) (e : E) :
    exposedPeriodPair Q t y z y' z' hy hz hy' hz' c S U hS hU e =
      (pairedTrialLaw t (y e) (z e) (y' e+c) (z' e+c) (A e)
        (Prod.mk e ⁻¹' S) (Prod.mk e ⁻¹' U)
        (hS.preimage measurable_prodMk_left) (hU.preimage measurable_prodMk_left)).map
          (fun p ↦ (p.1, shiftPath (-c) p.2.2)) := by
  have hm : Measurable (fun p : C(Time,Point) × (Point × C(Time,Point)) ↦
      (p.1, shiftPath (-c) p.2.2)) :=
    measurable_fst.prodMk ((shiftPath_continuous (-c)).measurable.comp
      (measurable_snd.comp measurable_snd))
  rw [exposedPeriodPair, Kernel.map_apply _ hm,
    exposedPairedTrialKernel_physical Q t y z (fun e ↦ y' e+c) (fun e ↦ z' e+c)
      hy hz (hy'.add measurable_const) (hz'.add measurable_const) S U hS hU A hQ]

lemma exposedPeriodPair_physical {L : Length} (Q : Kernel E Point) [IsFiniteKernel Q]
    {t C : ℝ} (ht : 0<t) (hC : 0≤C)
    (y z y' z' : E → Point) (hy : Measurable y) (hz : Measurable z)
    (hy' : Measurable y') (hz' : Measurable z') (c : Point) (hc : projectPoint L c=0)
    (S T U : Set (E × C(Time,Point))) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hTU : ∀e f, (e,shiftPath c f)∈U ↔ (e,f)∈T)
    (A : E → Set Point) (hQ : ∀e, Q e=targetUniform (A e))
    (hA : ∀e, MeasurableSet (A e)) (hAf : ∀e, volume (A e)≠⊤)
    {a b : ℝ≥0∞} (ha : 0<a) (hb : 0<b) (hvol : ∀e, a≤volume (A e))
    (hbound : ∀e u, u∈A e → ‖u-(fun j ↦ (y e j+z e j)/2)‖≤C)
    (hbound' : ∀e u, u∈A e → ‖u-(fun j ↦ ((y' e+c) j+(z' e+c) j)/2)‖≤C)
    (hfirst : ∀e, ∀ᵐu ∂targetUniform (A e), b≤trialKernel t (y e) (z e) u (Prod.mk e ⁻¹' S))
    (hsecond : ∀e, ∀ᵐu ∂targetUniform (A e), b≤trialKernel t (y' e+c) (z' e+c) u (Prod.mk e ⁻¹' U)) :
    let ρ := exposedPeriodPair Q t y z y' z' hy hz hy' hz' c S U hS hU
    let P := parameterIndividualReference t y z hy hz S hS
    let P' := parameterIndividualReference t y' z' hy' hz' T hT
    let G := b⁻¹*(a⁻¹*(midpointLower t C)⁻¹)
    IsMarkovKernel ρ ∧ IsMarkovKernel P ∧ IsMarkovKernel P' ∧
      (∀e, (ρ e).fst≤G • P e ∧ (ρ e).snd≤G • P' e) ∧
      (∀e, ∀ᵐp ∂ρ e,
        projectPoint L (p.1 midpointTime)=projectPoint L (p.2 midpointTime)) := by
  dsimp only
  let ρ := exposedPeriodPair Q t y z y' z' hy hz hy' hz' c S U hS hU
  let μ := parameterIndividualReference t y z hy hz S hS
  let ν := parameterIndividualReference t y' z' hy' hz' T hT
  let G := b⁻¹*(a⁻¹*(midpointLower t C)⁻¹)
  have hA0 (e : E) : volume (A e)≠0 := (ha.trans_le (hvol e)).ne'
  have hμ (e : E) : IsProbabilityMeasure (μ e) := by
    rw [show μ e=individualReference t (y e) (z e) (Prod.mk e ⁻¹' S) from
      parameterIndividualReference_apply ..]
    exact individualReference_probability ht hC (y e) (z e) (hA e) (hA0 e) (hAf e)
      (hbound e) _ (hS.preimage measurable_prodMk_left) hb (hfirst e)
  have hν (e : E) : IsProbabilityMeasure (ν e) := by
    rw [show ν e=individualReference t (y' e) (z' e) (Prod.mk e ⁻¹' T) from
      parameterIndividualReference_apply ..,
      ←individualReference_unshift t (y' e) (z' e) c (Prod.mk e ⁻¹' T) (Prod.mk e ⁻¹' U)
        (hU.preimage measurable_prodMk_left) (hTU e)]
    let _ := individualReference_probability ht hC (y' e+c) (z' e+c) (hA e)
      (hA0 e) (hAf e) (hbound' e) _ (hU.preimage measurable_prodMk_left) hb (hsecond e)
    infer_instance
  have hm : Measurable (fun p : C(Time,Point) × (Point × C(Time,Point)) ↦
      (p.1, shiftPath (-c) p.2.2)) :=
    measurable_fst.prodMk ((shiftPath_continuous (-c)).measurable.comp
      (measurable_snd.comp measurable_snd))
  have hp (e : E) : IsProbabilityMeasure (pairedTrialLaw t (y e) (z e) (y' e+c) (z' e+c)
      (A e) (Prod.mk e ⁻¹' S) (Prod.mk e ⁻¹' U)
      (hS.preimage measurable_prodMk_left) (hU.preimage measurable_prodMk_left)) :=
    pairedTrialLaw_probability t (y e) (z e) (y' e+c) (z' e+c) (A e)
      (hA0 e) (hAf e) _ _ (hS.preimage measurable_prodMk_left)
      (hU.preimage measurable_prodMk_left)
      ((hfirst e).mono (fun _ hu ↦ hb.trans_le hu))
      ((hsecond e).mono (fun _ hu ↦ hb.trans_le hu))
  have hρ (e : E) : IsProbabilityMeasure (ρ e) := by
    rw [show ρ e = _ from exposedPeriodPair_apply Q t y z y' z' hy hz hy' hz' c S U hS hU A hQ e]
    let _ := hp e
    infer_instance
  refine ⟨⟨hρ⟩,⟨hμ⟩,⟨hν⟩,?_,?_⟩
  · intro e
    obtain ⟨h₁,h₂⟩ := pairedTrialLaw_marginals ht hC hC (y e) (z e) (y' e+c) (z' e+c)
      (hA e) (hA0 e) (hAf e) (hbound e) (hbound' e) _ _
      (hS.preimage measurable_prodMk_left) (hU.preimage measurable_prodMk_left)
      hb hb (hfirst e) (hsecond e)
    have hf : (ρ e).fst = (pairedTrialLaw t (y e) (z e) (y' e+c) (z' e+c)
      (A e) (Prod.mk e ⁻¹' S) (Prod.mk e ⁻¹' U)
      (hS.preimage measurable_prodMk_left) (hU.preimage measurable_prodMk_left)).fst := by
      rw [show ρ e = _ from exposedPeriodPair_apply Q t y z y' z' hy hz hy' hz' c S U hS hU A hQ e,
        Measure.fst, Measure.map_map measurable_fst hm]
      rfl
    have hs : (ρ e).snd = ((pairedTrialLaw t (y e) (z e) (y' e+c) (z' e+c)
      (A e) (Prod.mk e ⁻¹' S) (Prod.mk e ⁻¹' U)
      (hS.preimage measurable_prodMk_left) (hU.preimage measurable_prodMk_left)).map
        (fun p ↦ p.2.2)).map (shiftPath (-c)) := by
      rw [show ρ e = _ from exposedPeriodPair_apply Q t y z y' z' hy hz hy' hz' c S U hS hU A hQ e,
        Measure.snd, Measure.map_map measurable_snd hm,
        Measure.map_map (shiftPath_continuous (-c)).measurable (by fun_prop)]
      rfl
    constructor
    · rw [hf, parameterIndividualReference_apply]
      apply h₁.trans
      intro B
      simp only [Measure.smul_apply, smul_eq_mul]
      gcongr
      exact hvol e
    · rw [hs, parameterIndividualReference_apply]
      have H := Measure.map_mono h₂ (shiftPath_continuous (-c)).measurable
      rw [Measure.map_smul _ (shiftPath_continuous (-c)).measurable.aemeasurable,
        individualReference_unshift t (y' e) (z' e) c
        (Prod.mk e ⁻¹' T) (Prod.mk e ⁻¹' U) (hU.preimage measurable_prodMk_left) (hTU e)] at H
      apply H.trans
      intro B
      simp only [Measure.smul_apply, smul_eq_mul]
      gcongr
      exact hvol e
  · intro e
    rw [show ρ e = _ from exposedPeriodPair_apply Q t y z y' z' hy hz hy' hz' c S U hS hU A hQ e]
    apply (ae_map_iff hm.aemeasurable (by measurability)).mpr
    filter_upwards [pairedTrialLaw_midpoint t (y e) (z e) (y' e+c) (z' e+c) (A e)
      (hA0 e) (hAf e) (Prod.mk e ⁻¹' S) (Prod.mk e ⁻¹' U)
      (hS.preimage measurable_prodMk_left) (hU.preimage measurable_prodMk_left)] with p hmid
    have hc' : projectPoint L (-c)=0 := by
      ext j
      change (((-c j):ℝ):AddCircle L.val)=0
      rw [AddCircle.coe_neg]
      have h := congrFun hc j
      change ((c j:ℝ):AddCircle L.val)=0 at h
      rw [h,neg_zero]
    change projectPoint L (p.1 midpointTime)=projectPoint L (p.2.2 midpointTime+(-c))
    rw [projectPoint_shift (-c) hc',hmid.1,hmid.2]

end HardSphere.Bridge
end
end

end OAI
