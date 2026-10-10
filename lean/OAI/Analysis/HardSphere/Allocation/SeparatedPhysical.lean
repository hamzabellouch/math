import Mathlib
import OAI.Analysis.HardSphere.Bridges.PhysicalSparse
import OAI.Analysis.HardSphere.Geometry.FrozenChecks

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]
  {X : I → Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] [Fintype C] in
lemma separated_of_no_crossing (checks : C → LocalCheck X) (s t : Finset I)
    (h : ∀c,∀i∈(checks c).support,∀j∈(checks c).support,i∈s → j∈t → False) :
    SeparatedChecks checks s t := by
  intro c hc
  by_cases hs : (checks c).support⊆s
  · exact Or.inl hs
  · right
    obtain ⟨j,hj,hjs⟩ := Finset.not_subset.mp hs
    have hjt := (Finset.mem_union.mp (hc hj)).resolve_left hjs
    intro i hi
    exact (Finset.mem_union.mp (hc hi)).resolve_left (fun his ↦ h c i hi j hj his hjt)

omit [Fintype I] [Fintype C] in
lemma frozen_separated_of_no_crossing (checks : C → LocalCheck X) (U s t : Finset I)
    (x : ∀i,X i)
    (h : ∀c,∀i∈(checks c).support,∀j∈(checks c).support,i∈s → j∈t → False) :
    SeparatedChecks (frozenChecks checks U x) s t := by
  apply separated_of_no_crossing
  intro c i hi j hj his hjt
  exact h c.val i (Finset.mem_inter.mp hi).1 j (Finset.mem_inter.mp hj).1 his hjt
end HardSphere.Comparison
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison Groups CellOrbital
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {V : I → Type*} [∀i,MeasurableSpace (V i)]

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma physical_support_near (r : ℝ) (anchor : J → Torus L) (center : I → Torus L)
    (allowed : J → Set C(Time,Point)) (owner : Bool → J → I)
    (hc : ∀b j,torusDistance L (anchor j) (center (owner b j))≤1)
    (path : ∀b j,V (owner b j)→allowed j) (hm : ∀b j,Measurable (path b j))
    (e : physicalEdges anchor) (i j : I)
    (hi : i∈(physicalSparseChecks r anchor allowed owner path hm e).support)
    (hj : j∈(physicalSparseChecks r anchor allowed owner path hm e).support) :
    torusDistance L (center i) (center j)≤23 := by
  have hbound := incident_centers_close anchor (fun k ↦ center (owner e.1 k)) id
    (hc e.1) e.2.val.1 e.2.val.2 e.2.property.2
  have hie : i=owner e.1 e.2.val.1 ∨ i=owner e.1 e.2.val.2 := by
    simpa only [physicalSparseChecks,factorPathCheck,dependentCheck,Finset.mem_insert,Finset.mem_singleton] using hi
  have hje : j=owner e.1 e.2.val.1 ∨ j=owner e.1 e.2.val.2 := by
    simpa only [physicalSparseChecks,factorPathCheck,dependentCheck,Finset.mem_insert,Finset.mem_singleton] using hj
  rcases hie with rfl|rfl <;> rcases hje with rfl|rfl
  · simp [torusDistance]
  · exact hbound
  · simpa only [id_eq,torusDistance_comm L (center (owner e.1 e.2.val.2))] using hbound
  · simp [torusDistance]

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma physical_frozen_separated (r : ℝ) (anchor : J → Torus L) (center : I → Torus L)
    (allowed : J → Set C(Time,Point)) (owner : Bool → J → I)
    (hc : ∀b j,torusDistance L (anchor j) (center (owner b j))≤1)
    (path : ∀b j,V (owner b j)→allowed j) (hm : ∀b j,Measurable (path b j))
    (U s t : Finset I) (x : ∀i,V i)
    (hfar : ∀i∈s,∀j∈t,23<torusDistance L (center i) (center j)) :
    SeparatedChecks (frozenChecks (physicalSparseChecks r anchor allowed owner path hm) U x) s t := by
  apply frozen_separated_of_no_crossing
  intro e i hi j hj his hjt
  exact (not_le_of_gt (hfar i his j hjt)) (physical_support_near r anchor center allowed owner hc path hm e i j hi hj)

end HardSphere.Bridge

end
end

end

end OAI
