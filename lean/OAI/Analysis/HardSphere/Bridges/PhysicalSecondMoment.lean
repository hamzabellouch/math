import Mathlib
import OAI.Analysis.HardSphere.Bridges.ReferenceHit
import OAI.Analysis.HardSphere.Comparison.FrozenLikelihood
import OAI.Analysis.HardSphere.Bridges.RouteInsertion

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison Groups CellOrbital
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I → Type*} [∀i,MeasurableSpace (X i)]

theorem physical_route_second_moment {K : ℕ} [NeZero K] (hL : L.val=(K:ℝ))
    (r : ℝ) (anchor : J→Torus L) (cent : I→Fin 3→Fin K)
    (M : ℕ) (hm : ∀v,(Finset.univ.filter (fun i : I ↦ cent i=v)).card≤M)
    (allowed : J→Set C(Time,Point)) (label : J→I) (hl : Function.Injective label)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (σ τ : Equiv.Perm I) (fs ft cs ct os ot : Finset I)
    (hσ : ∀i,i∉fs∪cs → σ i=i) (hτ : ∀i,i∉ft∪ct → τ i=i)
    (hff : Disjoint fs ft) (hfn : Disjoint (fs∪ft) (cs∪ct))
    (hos : Disjoint (fs∪cs) os) (hot : Disjoint (ft∪ct) ot)
    (hosU : (fs∪cs)∪os=(fs∪ft)∪(cs∪ct))
    (hotU : (ft∪ct)∪ot=(fs∪ft)∪(cs∪ct))
    (hc0 : ∀j,torusDistance L (anchor j) (gridCenter L (cent (label j)))≤1)
    (hcσ : ∀j,torusDistance L (anchor j) (gridCenter L (cent (σ (label j))))≤1)
    (hcτ : ∀j,torusDistance L (anchor j) (gridCenter L (cent (τ (label j))))≤1)
    (hfar0 : ∀i∈fs,∀j∈ft,23<torusDistance L (gridCenter L (cent i)) (gridCenter L (cent j)))
    (hfarσ : ∀i∈fs,∀j∈os,23<torusDistance L (gridCenter L (cent i)) (gridCenter L (cent j)))
    (hfarτ : ∀i∈ft,∀j∈ot,23<torusDistance L (gridCenter L (cent i)) (gridCenter L (cent j)))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (X (τ.symm i))) [∀i,IsFiniteKernel (η i)]
    (P : ∀j,Measure (allowed j)) (G q a : ℝ≥0∞) (ha : 0<a) (ha1 : a≤1)
    (hκb : ∀i x,κ i x Set.univ≤G)
    (hκm : ∀i,∫⁻x,κ i x Set.univ ∂μ i=1)
    (hηm : ∀i,∫⁻x,η i x Set.univ ∂μ i=1)
    (hdom0 : ∀j,label j∈(fs∪ft)∪(cs∪ct) → (μ (label j)).map (get j)≤G • P j)
    (hdomσ : ∀b j,routeOwner σ label b j∈fs∪cs →
      ((μ (routeOwner σ label b j)).compProd (κ (routeOwner σ label b j))).map
        (routePath σ (fs∪cs) hσ allowed label get b j)≤G • P j)
    (hdomτ : ∀b j,routeOwner τ label b j∈ft∪ct →
      ((μ (routeOwner τ label b j)).compProd (η (routeOwner τ label b j))).map
        (routePath τ (ft∪ct) hτ allowed label get b j)≤G • P j)
    (hq : ∀j k,j≠k → ∀g : allowed k,P j {f | TrialCollision r (projectCurve L g.val) f.val}≤q)
    (hsmall : a+(4*(49^3*M):ℕ)*(G*q)≤1)
    (hG : G≠⊤) (z : ∀i,X (σ.symm i)) (w : ∀i,X (τ.symm i)) :
    (∫⁻x,conditionalLikelihood (primaryChecks r anchor allowed label get hg)
      (routeChecks σ (fs∪cs) hσ r anchor allowed label get hg) μ κ
      (fs∪cs) (Finset.univ\(fs∪cs)) x z *
      conditionalLikelihood (primaryChecks r anchor allowed label get hg)
      (routeChecks τ (ft∪ct) hτ r anchor allowed label get hg) μ η
      (ft∪ct) (Finset.univ\(ft∪ct)) x w
      ∂conditionedMeasure (Measure.pi μ)
        (retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ))≤
      G^(cs∩ct).card/a^(2*(cs.card+ct.card)) := by
  let U := (fs∪ft)∪(cs∪ct)
  have hsU : fs∪cs⊆U := by rw [show U=(fs∪cs)∪os from hosU.symm];exact Finset.subset_union_left
  have htU : ft∪ct⊆U := by rw [show U=(ft∪ct)∪ot from hotU.symm];exact Finset.subset_union_left
  have hsC : Disjoint (fs∪cs) (Finset.univ\U) := Finset.disjoint_left.mpr
    (fun i hi hic ↦ (Finset.mem_sdiff.mp hic).2 (hsU hi))
  have htC : Disjoint (ft∪ct) (Finset.univ\U) := Finset.disjoint_left.mpr
    (fun i hi hic ↦ (Finset.mem_sdiff.mp hic).2 (htU hi))
  apply frozen_pair_mean_integrates
    (primaryChecks r anchor allowed label get hg)
    (routeChecks σ (fs∪cs) hσ r anchor allowed label get hg)
    (routeChecks τ (ft∪ct) hτ r anchor allowed label get hg)
    μ κ η (fs∪cs) (ft∪ct) os ot U hsU htU hos hot hosU hotU z w
  · intro x hx
    exact routeChecks_outside σ (fs∪cs) hσ r anchor allowed label get hg _ hsC
      (fun i ↦ (x i,z i)) hx
  · intro x hx
    exact routeChecks_outside τ (ft∪ct) hτ r anchor allowed label get hg _ htC
      (fun i ↦ (x i,w i)) hx
  · exact ENNReal.div_ne_top (ENNReal.pow_ne_top hG)
      (pow_ne_zero _ (ne_of_gt ha))
  · intro x hx
    exact physical_route_cancellation hL r anchor cent M hm allowed label hl get hg
      σ τ fs ft cs ct os ot hσ hτ hff hfn hos hot hosU hotU hc0 hcσ hcτ
      hfar0 hfarσ hfarτ μ κ η P G q a ha ha1 hκb hκm hηm hdom0 hdomσ hdomτ
      hq hsmall x z w hx

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking

def pinnedSet (y z : Point) : Set C(Time,Point) := {f | f 0=y ∧ f 1=z}
lemma pinnedSet_closed (y z : Point) : IsClosed (pinnedSet y z) :=
  (isClosed_eq (continuous_eval_const 0) continuous_const).inter
    (isClosed_eq (continuous_eval_const 1) continuous_const)

lemma reference_pinned (t : ℝ) (y z : Point) :
    ∀ᵐf ∂law.map (leg t y z),f∈pinnedSet y z := by
  exact (ae_map_iff (leg_continuous t y z).measurable.aemeasurable (pinnedSet_closed y z).measurableSet).mpr (leg_endpoints_ae t y z)

lemma trial_pinned (t : ℝ) (y z u : Point) :
    ∀ᵐf ∂trialKernel t y z u,f∈pinnedSet y z := by
  rw [trialKernel_apply]
  apply (ae_map_iff (show AEMeasurable (trialPath t y z u) (law.prod law) from (by fun_prop)) (pinnedSet_closed y z).measurableSet).mpr
  exact ae_of_all _ (fun β ↦ ⟨trial_zero _ _ _ _ _,trial_one _ _ _ _ _⟩)

lemma reference_restrict_pinned (t : ℝ) (y z : Point) (E : Set C(Time,Point))
    (hE : MeasurableSet E) :
    (law.map (leg t y z)).restrict (E∩pinnedSet y z)=(law.map (leg t y z)).restrict E := by
  rw [←Measure.restrict_restrict hE,Measure.restrict_eq_self_of_ae_mem (reference_pinned t y z)]

lemma trial_measure_pinned (t : ℝ) (y z u : Point) (E : Set C(Time,Point)) :
    trialKernel t y z u (E∩pinnedSet y z)=trialKernel t y z u E :=
  measure_inter_conull (ae_iff.mp (trial_pinned t y z u))

lemma individualReference_pinned (t : ℝ) (y z : Point) (E : Set C(Time,Point))
    (hE : MeasurableSet E) :
    individualReference t y z (E∩pinnedSet y z)=individualReference t y z E := by
  unfold individualReference
  rw [reference_restrict_pinned (2*t) y z E hE]
  rw [measure_inter_conull (ae_iff.mp (reference_pinned (2*t) y z))]

end HardSphere.Bridge

end
end

end

end OAI
