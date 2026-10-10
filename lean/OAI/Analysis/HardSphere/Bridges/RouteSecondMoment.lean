import Mathlib
import OAI.Analysis.HardSphere.Conditioning.RoutePartition
import OAI.Analysis.HardSphere.Bridges.PhysicalSecondMoment

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison Groups CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I→Type*} [∀i,MeasurableSpace (X i)]

theorem physical_route_encounter_moment {K : ℕ} [NeZero K] (hL : L.val=(K:ℝ))
    (r : ℝ) (anchor : J→Torus L) (cent : I→Fin 3→Fin K)
    (M : ℕ) (hm : ∀v,(Finset.univ.filter (fun i : I ↦ cent i=v)).card≤M)
    (allowed : J→Set C(Time,Point)) (label : J→I) (hl : Function.Injective label)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (σ τ : Equiv.Perm I) (s t : Finset I)
    (hσ : ∀i,i∉s→σ i=i) (hτ : ∀i,i∉t→τ i=i)
    (hc0 : ∀j,torusDistance L (anchor j) (gridCenter L (cent (label j)))≤1)
    (hcσ : ∀j,torusDistance L (anchor j) (gridCenter L (cent (σ (label j))))≤1)
    (hcτ : ∀j,torusDistance L (anchor j) (gridCenter L (cent (τ (label j))))≤1)
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (X (τ.symm i))) [∀i,IsFiniteKernel (η i)]
    (P : ∀j,Measure (allowed j)) (G q a : ℝ≥0∞) (ha : 0<a) (ha1 : a≤1)
    (hκb : ∀i x,κ i x univ≤G)
    (hκm : ∀i,∫⁻x,κ i x univ ∂μ i=1)
    (hηm : ∀i,∫⁻x,η i x univ ∂μ i=1)
    (hdom0 : ∀j,label j∈s∪t→(μ (label j)).map (get j)≤G • P j)
    (hdomσ : ∀b j,routeOwner σ label b j∈s→
      ((μ (routeOwner σ label b j)).compProd (κ (routeOwner σ label b j))).map
        (routePath σ s hσ allowed label get b j)≤G • P j)
    (hdomτ : ∀b j,routeOwner τ label b j∈t→
      ((μ (routeOwner τ label b j)).compProd (η (routeOwner τ label b j))).map
        (routePath τ t hτ allowed label get b j)≤G • P j)
    (hq : ∀j k,j≠k→∀f:allowed k,P j {p | TrialCollision r (projectCurve L f.val) p.val}≤q)
    (hsmall : a+(4*(49^3*M):ℕ)*(G*q)≤1) (hG : G≠⊤)
    (z : ∀i,X (σ.symm i)) (w : ∀i,X (τ.symm i)) :
    let ns := nearSlots (torusNear K 30) (fun i ↦ Groups.gridSite (cent i)) s t
    let nt := nearSlots (torusNear K 30) (fun i ↦ Groups.gridSite (cent i)) t s
    (∫⁻x,conditionalLikelihood (primaryChecks r anchor allowed label get hg)
      (routeChecks σ s hσ r anchor allowed label get hg) μ κ s (Finset.univ\s) x z *
      conditionalLikelihood (primaryChecks r anchor allowed label get hg)
      (routeChecks τ t hτ r anchor allowed label get hg) μ η t (Finset.univ\t) x w
      ∂conditionedMeasure (Measure.pi μ)
        (retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ))≤
      G^(s∩t).card/a^(2*(ns.card+nt.card)) := by
  dsimp only
  let e := torusNear K 30
  let c := fun i ↦ Groups.gridSite (cent i)
  let fs := farSlots e c s t
  let ft := farSlots e c t s
  let cs := nearSlots e c s t
  let ct := nearSlots e c t s
  have he : ∀v,e v v := fun v ↦ torusNear_refl K 30 v
  have hs : fs∪cs=s := far_union_near e c s t
  have ht : ft∪ct=t := far_union_near e c t s
  have hU : (fs∪ft)∪(cs∪ct)=s∪t := route_partition_union e c s t
  have hS : ∀i,i∉fs∪cs→σ i=i := by simpa only [hs] using hσ
  have hT : ∀i,i∉ft∪ct→τ i=i := by simpa only [ht] using hτ
  have hdis := far_partition_disjoint e he c s t
  have pathS : routePath σ (fs∪cs) hS allowed label get = routePath σ s hσ allowed label get := by
    congr 1
  have pathT : routePath τ (ft∪ct) hT allowed label get = routePath τ t hτ allowed label get := by
    congr 1
  have checksS : routeChecks σ (fs∪cs) hS r anchor allowed label get hg = routeChecks σ s hσ r anchor allowed label get hg := by
    congr 1
  have checksT : routeChecks τ (ft∪ct) hT r anchor allowed label get hg = routeChecks τ t hτ r anchor allowed label get hg := by
    congr 1
  have hh := physical_route_second_moment hL r anchor cent M hm allowed label hl get hg
    σ τ fs ft cs ct (t\s) (s\t) hS hT hdis.1 hdis.2
    (by rw [hs]; exact Finset.disjoint_left.mpr (fun i hi hj ↦ (Finset.mem_sdiff.mp hj).2 hi))
    (by rw [ht]; exact Finset.disjoint_left.mpr (fun i hi hj ↦ (Finset.mem_sdiff.mp hj).2 hi))
    (by rw [hs,hU]; ext i; simp)
    (by rw [ht,hU]; ext i; simp; tauto)
    hc0 hcσ hcτ
    (fun i hi j hj ↦ physical_far_slots L hL cent s t i j hi (Finset.sdiff_subset hj))
    (fun i hi j hj ↦ physical_far_slots L hL cent s t i j hi (Finset.mem_sdiff.mp hj).1)
    (fun i hi j hj ↦ physical_far_slots L hL cent t s i j hi (Finset.mem_sdiff.mp hj).1)
    μ κ η P G q a ha ha1 hκb hκm hηm
    (by simpa only [hU] using hdom0)
    (by simpa only [hs,pathS] using hdomσ) (by simpa only [ht,pathT] using hdomτ)
    hq hsmall hG z w
  simpa only [hs,ht,checksS,checksT,show cs∩ct=s∩t from commonSlots_near e he c s t] using hh

end HardSphere.Bridge
end
end

end OAI
