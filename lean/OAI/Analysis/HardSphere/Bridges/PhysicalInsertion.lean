import Mathlib
import OAI.Analysis.HardSphere.Bridges.JointCollision
import OAI.Analysis.HardSphere.Collisions.Insertion
import OAI.Analysis.HardSphere.Bridges.ReferenceHit
import OAI.Analysis.HardSphere.Conditioning.RestrictedMeasure

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison

def referenceOn (t : ℝ) (y z : Point) (S : Set C(Time,Point)) : Measure S :=
  subtypeConditional (law.map (leg (2*t) y z)) S

lemma referenceOn_map (t : ℝ) (y z : Point) {S : Set C(Time,Point)} (hS : MeasurableSet S) :
    (referenceOn t y z S).map Subtype.val=individualReference t y z S :=
  subtypeConditional_map _ hS

lemma referenceOn_collision {L : Length} (t r : ℝ) (y z : Point)
    {S : Set C(Time,Point)} (hS : MeasurableSet S) (ω : ConfigurationPath 1 L) :
    referenceOn t y z S {f | TrialCollision r ω f.val}=
      individualReference t y z S {f | TrialCollision r ω f} := by
  rw [←referenceOn_map t y z hS,Measure.map_apply measurable_subtype_coe
    (trialCollision_closed r ω).measurableSet]
  rfl

lemma referenceOn_probability {t C : ℝ} (ht : 0<t) (hC : 0≤C) (y z : Point)
    {A : Set Point} (hA : MeasurableSet A) (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (hbound : ∀u∈A,‖u-(fun j ↦ (y j+z j)/2)‖≤C)
    (S : Set C(Time,Point)) (hS : MeasurableSet S) {c : ℝ≥0∞} (hc0 : 0<c)
    (hc : ∀ᵐu ∂targetUniform A,c≤trialKernel t y z u S) :
    IsProbabilityMeasure (referenceOn t y z S) := by
  let _ : IsProbabilityMeasure (individualReference t y z S) :=
    individualReference_probability ht hC y z hA hA0 hAfinite hbound S hS hc0 hc
  constructor
  have h := congrArg (fun μ : Measure C(Time,Point) ↦ μ univ) (referenceOn_map t y z hS)
  simpa only [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    Set.preimage_univ,measure_univ] using h

variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E]
  {L : Length} (S : I→Set C(Time,Point))
  (left right : E→I) (hdiff : ∀e,left e≠right e)

def referenceChecks (r : ℝ) : E→LocalCheck (fun i ↦ S i) :=
  fun e ↦ physicalPairCheck (L:=L) S r (left e) (right e) (hdiff e)

omit [Fintype I] [Fintype E] in
lemma physical_check_failure (r : ℝ) (μ : ∀i,Measure (S i)) (p : I→E→ℝ≥0∞)
    (hcoll : ∀i e,i∈(referenceChecks (L:=L) S left right hdiff r e).support →
      ∀j : I,j≠i→∀g : S j, μ i {f | TrialCollision r (projectCurve L g.val) f.val}≤p i e)
    (i : I) (e : E) (hi : i∈(referenceChecks (L:=L) S left right hdiff r e).support)
    (x : ∀i,S i) :
    μ i {y | ¬(referenceChecks (L:=L) S left right hdiff r e).pass (Function.update x i y)}≤p i e := by
  classical
  have hie : i=left e ∨ i=right e := by simpa [referenceChecks,physicalPairCheck] using hi
  rcases hie with he|he
  · subst i
    have hh : right e≠left e := (hdiff e).symm
    simpa only [referenceChecks,physicalPairCheck,not_not,
      Function.update_self,Function.update_of_ne hh] using
      hcoll (left e) e hi (right e) hh (x (right e))
  · subst i
    have hh : left e≠right e := hdiff e
    have eq : {y : S (right e) | ¬(referenceChecks (L:=L) S left right hdiff r e).pass
        (Function.update x (right e) y)}=
        {y : S (right e) | TrialCollision r (projectCurve L (x (left e)).val) y.val} := by
      ext y
      simp only [mem_ofPred_eq,referenceChecks,physicalPairCheck,not_not,
        Function.update_self,Function.update_of_ne hh]
      exact physicalPairCheck_symmetric r _ _
    rw [eq]
    exact hcoll (right e) e hi (left e) hh (x (left e))

omit [Fintype I] in
lemma physical_reference_insertion (r : ℝ) (μ : ∀i,Measure (S i))
    [∀i,IsProbabilityMeasure (μ i)] (p : I→E→ℝ≥0∞) (a : ℝ≥0∞) (U : Finset I)
    (hcoll : ∀i∈U,∀e,i∈(referenceChecks (L:=L) S left right hdiff r e).support →
      ∀j : I,j≠i→∀g : S j, μ i {f | TrialCollision r (projectCurve L g.val) f.val}≤p i e)
    (htotal : ∀i∈U,a+(∑e∈Finset.univ.filter
      (fun e ↦ i∈(referenceChecks (L:=L) S left right hdiff r e).support),p i e)≤1) :
    UniformInsertionOn (referenceChecks (L:=L) S left right hdiff r) μ a U := by
  apply uniformInsertionOn_of_check_failures _ μ p a U _ htotal
  intro i hi e he x
  have hlocal := physical_check_failure (L:=L) S left right hdiff r μ
    (fun j e ↦ if j=i then p i e else ⊤)
  have H := hlocal (by
    intro j e hj k hk g
    by_cases hj' : j=i
    · subst j
      simpa using hcoll i hi e hj k hk g
    · simp [hj']) i e he x
  simpa using H

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

def fixedEndpoints (y z : Point) : Set C(Time,Point) := {f | f 0=y ∧ f 1=z}
lemma fixedEndpoints_measurable (y z : Point) : MeasurableSet (fixedEndpoints y z) :=
  (measurableSet_eq_fun (continuous_eval_const 0).measurable measurable_const).inter
    (measurableSet_eq_fun (continuous_eval_const 1).measurable measurable_const)

lemma full_bridge_fixedEndpoints (t : ℝ) (y z : Point) :
    ∀ᵐf ∂law.map (leg (2*t) y z),f∈fixedEndpoints y z := by
  apply (ae_map_iff (leg_continuous _ _ _).measurable.aemeasurable (fixedEndpoints_measurable y z)).mpr
  exact leg_endpoints_ae _ _ _

lemma trial_fixedEndpoints (t : ℝ) (y z u : Point) :
    ∀ᵐf ∂trialKernel t y z u,f∈fixedEndpoints y z := by
  rw [trialKernel_apply]
  apply (ae_map_iff ((trialPath_continuous t y z).measurable.comp
    (measurable_const.prodMk measurable_id)).aemeasurable (fixedEndpoints_measurable y z)).mpr
  exact ae_of_all _ (fun β ↦ ⟨trial_zero t y z u β,trial_one t y z u β⟩)

lemma restrict_inter_ae_full {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (S T : Set X) (hT : ∀ᵐx ∂μ,x∈T) : μ.restrict (S∩T)=μ.restrict S := by
  apply Measure.restrict_congr_set
  filter_upwards [hT] with x hx
  apply propext
  change (x∈S ∧ x∈T) ↔ x∈S
  simp only [hx,and_true]

lemma measure_inter_ae_full {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (S T : Set X) (hT : ∀ᵐx ∂μ,x∈T) : μ (S∩T)=μ S := by
  apply measure_congr
  filter_upwards [hT] with x hx
  apply propext
  change (x∈S ∧ x∈T) ↔ x∈S
  simp only [hx,and_true]

lemma individualReference_pin (t : ℝ) (y z : Point) (S : Set C(Time,Point)) :
    individualReference t y z (S∩fixedEndpoints y z)=individualReference t y z S := by
  unfold individualReference
  rw [restrict_inter_ae_full _ _ _ (full_bridge_fixedEndpoints t y z),
    measure_inter_ae_full _ _ _ (full_bridge_fixedEndpoints t y z)]

lemma trialKernel_pin (t : ℝ) (y z u : Point) (S : Set C(Time,Point)) :
    trialKernel t y z u (S∩fixedEndpoints y z)=trialKernel t y z u S :=
  measure_inter_ae_full _ _ _ (trial_fixedEndpoints t y z u)

end HardSphere.Bridge

end
end

end

end OAI
