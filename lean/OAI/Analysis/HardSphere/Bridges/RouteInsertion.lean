import Mathlib
import OAI.Analysis.HardSphere.Bridges.RouteFrozen
import OAI.Analysis.HardSphere.Collisions.FirstCoordinate
import OAI.Analysis.HardSphere.Allocation.SeparatedPhysical

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
lemma route_insertion {K : ℕ} [NeZero K] (hL : L.val=(K:ℝ))
    (r : ℝ) (anchor : J→Torus L) (center : I→Fin 3→Fin K)
    (M : ℕ) (hm : ∀v,(Finset.univ.filter (fun i : I ↦ center i=v)).card≤M)
    (allowed : J→Set C(Time,Point)) (label : J→I) (hl : Function.Injective label)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (σ : Equiv.Perm I) (S : Finset I) (hfix : ∀i,i∉S → σ i=i)
    (hc : ∀b j,torusDistance L (anchor j) (gridCenter L (center (routeOwner σ label b j)))≤1)
    (ν : ∀i,Measure (X i×X (σ.symm i))) [∀i,IsProbabilityMeasure (ν i)]
    (P : ∀j,Measure (allowed j)) (G q a : ℝ≥0∞)
    (hdom : ∀b j,routeOwner σ label b j∈S → (ν (routeOwner σ label b j)).map
      (routePath σ S hfix allowed label get b j)≤G • P j)
    (hq : ∀j k,j≠k → ∀g : allowed k,P j {f | TrialCollision r (projectCurve L g.val) f.val}≤q)
    (hsmall : a+(4*(49^3*M):ℕ)*(G*q)≤1) :
    UniformInsertionOn (routeChecks σ S hfix r anchor allowed label get hg) ν a S := by
  unfold routeChecks
  exact physicalSparseChecks_insertion (V:=fun i ↦ X i×X (σ.symm i)) hL r anchor center M hm allowed (routeOwner σ label)
    (routeOwner_injective σ label hl) hc (routePath σ S hfix allowed label get)
    (routePath_measurable σ S hfix allowed label get hg) ν P G q a S hdom hq hsmall

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma route_frozen_separated (r : ℝ) (anchor : J→Torus L) (center : I→Torus L)
    (allowed : J→Set C(Time,Point)) (label : J→I)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (σ : Equiv.Perm I) (S : Finset I) (hfix : ∀i,i∉S → σ i=i)
    (hc : ∀b j,torusDistance L (anchor j) (center (routeOwner σ label b j))≤1)
    (U s t : Finset I) (x : ∀i,X i×X (σ.symm i))
    (hfar : ∀i∈s,∀j∈t,23<torusDistance L (center i) (center j)) :
    SeparatedChecks (frozenChecks (routeChecks σ S hfix r anchor allowed label get hg) U x) s t := by
  unfold routeChecks
  exact physical_frozen_separated (V:=fun i ↦ X i×X (σ.symm i)) r anchor center allowed (routeOwner σ label) hc
    (routePath σ S hfix allowed label get) (routePath_measurable σ S hfix allowed label get hg) U s t x hfar

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison Groups CellOrbital
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I → Type*} [∀i,MeasurableSpace (X i)]

theorem physical_route_cancellation {K : ℕ} [NeZero K] (hL : L.val=(K:ℝ))
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
    (x : ∀i,X i) (z : ∀i,X (σ.symm i)) (w : ∀i,X (τ.symm i))
    (hx : x∈retainedEvent (primaryChecks r anchor allowed label get hg)
      (Finset.univ\((fs∪ft)∪(cs∪ct)))) :
    let U := (fs∪ft)∪(cs∪ct)
    let Ref := frozenChecks (primaryChecks r anchor allowed label get hg) U x
    let ChS := frozenChecks (routeChecks σ (fs∪cs) hσ r anchor allowed label get hg) U (fun i ↦ (x i,z i))
    let ChT := frozenChecks (routeChecks τ (ft∪ct) hτ r anchor allowed label get hg) U (fun i ↦ (x i,w i))
    lmarginal μ U (fun y ↦ checkWeight Ref U y *
      conditionalLikelihood Ref ChS μ κ (fs∪cs) os y z *
      conditionalLikelihood Ref ChT μ η (ft∪ct) ot y w) x /
      checkNormalizer Ref μ U x≤G^(cs∩ct).card/a^(2*(cs.card+ct.card)) := by
  let U := (fs∪ft)∪(cs∪ct)
  have hsU : fs∪cs⊆U := by change fs∪cs⊆(fs∪ft)∪(cs∪ct);rw [←hosU];exact Finset.subset_union_left
  have htU : ft∪ct⊆U := by change ft∪ct⊆(fs∪ft)∪(cs∪ct);rw [←hotU];exact Finset.subset_union_left
  have hcS : ∀b j,torusDistance L (anchor j) (gridCenter L (cent (routeOwner σ label b j)))≤1 := by
    intro b j;cases b;exact hc0 j;exact hcσ j
  have hcT : ∀b j,torusDistance L (anchor j) (gridCenter L (cent (routeOwner τ label b j)))≤1 := by
    intro b j;cases b;exact hc0 j;exact hcτ j
  let hprobκ : ∀i,IsProbabilityMeasure ((μ i).compProd (κ i)) :=
    fun i ↦ isProbabilityMeasure_compProd_of_mass (μ i) (κ i) (hκm i)
  let hprobη : ∀i,IsProbabilityMeasure ((μ i).compProd (η i)) :=
    fun i ↦ isProbabilityMeasure_compProd_of_mass (μ i) (η i) (hηm i)
  have hRef' : UniformInsertionOn (primaryChecks r anchor allowed label get hg) μ a U :=
    physicalSparseChecks_insertion (V:=X) hL r anchor cent M hm allowed (fun _ ↦ label)
      (fun _ ↦ hl) (fun _ ↦ hc0) (fun _ ↦ get) (fun _ ↦ hg) μ P G q a U
      (fun _ ↦ hdom0) hq hsmall
  have hS' : UniformInsertionOn (routeChecks σ (fs∪cs) hσ r anchor allowed label get hg)
      (fun i ↦ (μ i).compProd (κ i)) a (fs∪cs) :=
    route_insertion hL r anchor cent M hm allowed label hl get hg σ (fs∪cs) hσ hcS _ P G q a hdomσ hq hsmall
  have hT' : UniformInsertionOn (routeChecks τ (ft∪ct) hτ r anchor allowed label get hg)
      (fun i ↦ (μ i).compProd (η i)) a (ft∪ct) :=
    route_insertion hL r anchor cent M hm allowed label hl get hg τ (ft∪ct) hτ hcT _ P G q a hdomτ hq hsmall
  apply conditional_cancellation _ _ _ μ κ η fs ft cs ct os ot hff hfn hos hot hosU hotU
    ha ha1 hκb hκm hηm
  · exact frozen_uniformInsertion _ U x μ hRef'
  · exact frozen_uniformInsertion_on _ U (fs∪cs) hsU _ _ hS'
  · exact frozen_uniformInsertion_on _ U (ft∪ct) htU _ _ hT'
  · exact physical_frozen_separated (V:=X) r anchor (fun i ↦ gridCenter L (cent i)) allowed
      (fun _ ↦ label) (fun _ ↦ hc0) (fun _ ↦ get) (fun _ ↦ hg) U fs ft x hfar0
  · exact route_frozen_separated r anchor (fun i ↦ gridCenter L (cent i)) allowed label get hg σ (fs∪cs) hσ hcS U fs os _ hfarσ
  · exact route_frozen_separated r anchor (fun i ↦ gridCenter L (cent i)) allowed label get hg τ (ft∪ct) hτ hcT U ft ot _ hfarτ
  · exact fun y u hy ↦ routeChecks_frozen_outside σ (fs∪cs) hσ r anchor allowed label get hg
      U os hsU hos x z hx y u hy
  · exact fun y u hy ↦ routeChecks_frozen_outside τ (ft∪ct) hτ r anchor allowed label get hg
      U ot htU hot x w hx y u hy

end HardSphere.Bridge

end
end

end

end OAI
