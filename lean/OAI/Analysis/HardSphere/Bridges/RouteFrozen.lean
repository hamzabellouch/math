import Mathlib
import OAI.Analysis.HardSphere.Conditioning.ReferenceResample
import OAI.Analysis.HardSphere.Bridges.SelectedReverse

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I → Type*} [∀i,MeasurableSpace (X i)]
  (σ : Equiv.Perm I) (S : Finset I) (hfix : ∀i,i∉S → σ i=i)
  (r : ℝ) (anchor : J → Torus L) (allowed : J → Set C(Time,Point))
  (label : J → I) (get : ∀j,X (label j) → allowed j) (hg : ∀j,Measurable (get j))

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma routeChecks_primary_weight (u : Finset I) (p : ∀i,X i×X (σ.symm i)) :
    checkWeight (routeChecks σ S hfix r anchor allowed label get hg) u p≤
      checkWeight (primaryChecks r anchor allowed label get hg) u (fun i ↦ (p i).1) := by
  by_cases hp : p∈retainedEvent (routeChecks σ S hfix r anchor allowed label get hg) u
  · rw [checkWeight,Set.indicator_of_mem hp,checkWeight,
      Set.indicator_of_mem (routeChecks_primary σ S hfix r anchor allowed label get hg u p hp)]
  · rw [checkWeight,Set.indicator_of_notMem hp]
    exact bot_le

omit [Fintype J] [DecidableEq J] in
lemma routeChecks_frozen_outside (U o : Finset I) (hSU : S⊆U) (hSo : Disjoint S o)
    (x : ∀i,X i) (z : ∀i,X (σ.symm i))
    (hx : x∈retainedEvent (primaryChecks r anchor allowed label get hg) (Finset.univ\U))
    (y : ∀i,X i) (u : ∀i,X (σ.symm i))
    (hy : y∈retainedEvent (frozenChecks (primaryChecks r anchor allowed label get hg) U x) o) :
    (fun i ↦ (y i,u i))∈retainedEvent (frozenChecks (routeChecks σ S hfix r anchor allowed label get hg)
      U (fun i ↦ (x i,z i))) o := by
  have hSc : Disjoint S (Finset.univ\U) := Finset.disjoint_left.mpr (fun i hi hic ↦
    (Finset.mem_sdiff.mp hic).2 (hSU hi))
  have hz := routeChecks_outside σ S hfix r anchor allowed label get hg (Finset.univ\U) hSc
    (fun i ↦ (x i,z i)) hx
  apply (frozen_retained _ U o _ _ hz).mpr
  have hyo := (frozen_retained _ U o _ _ hx).mp hy
  apply routeChecks_outside σ S hfix r anchor allowed label get hg (o∪(Finset.univ\U))
    (Finset.disjoint_union_right.mpr ⟨hSo,hSc⟩)
  convert hyo using 1
  funext i
  by_cases hi : i∈U <;> simp only [freezeOutside,hi,ite_true,ite_false]

omit [Fintype J] [DecidableEq J] in
lemma routeChecks_frozen_primary (U o : Finset I) (hSU : S⊆U)
    (x : ∀i,X i) (z : ∀i,X (σ.symm i))
    (hx : x∈retainedEvent (primaryChecks r anchor allowed label get hg) (Finset.univ\U))
    (y : ∀i,X i) (u : ∀i,X (σ.symm i)) :
    checkWeight (frozenChecks (routeChecks σ S hfix r anchor allowed label get hg) U (fun i ↦ (x i,z i))) o
      (fun i ↦ (y i,u i))≤checkWeight (frozenChecks (primaryChecks r anchor allowed label get hg) U x) o y := by
  have hSc : Disjoint S (Finset.univ\U) := Finset.disjoint_left.mpr (fun i hi hic ↦
    (Finset.mem_sdiff.mp hic).2 (hSU hi))
  have hz := routeChecks_outside σ S hfix r anchor allowed label get hg (Finset.univ\U) hSc
    (fun i ↦ (x i,z i)) hx
  rw [frozen_checkWeight _ U o _ _ hz,frozen_checkWeight _ U o _ _ hx]
  convert routeChecks_primary_weight σ S hfix r anchor allowed label get hg (o∪(Finset.univ\U))
    (freezeOutside U (fun i ↦ (x i,z i)) (fun i ↦ (y i,u i))) using 1
  congr 2
  funext i
  by_cases hi : i∈U <;> simp only [freezeOutside,hi,ite_true,ite_false]

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

lemma proposalKernel_reverse {L : Length}
    (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (X (σ i))) [∀i,IsFiniteKernel (η i)]
    (he : ∀j:s,((μ (σ j)).compProd (κ (σ j))).map (reverseFactor (X:=X) σ j)=
        (ν j).compProd (η j))
    (z : ∀i,X (σ.symm i)) (w : ∀i,X (σ i)) :
    (proposalKernel (routeChecks σ s hf r anchor allowed label get hg) μ κ s (Finset.univ\s) z).map
      (reverseSelected σ s hf)=
    proposalKernel (routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg)
      ν η s (Finset.univ\s) w := by
  ext x B hB
  rw [Kernel.map_apply _ (reverseSelected σ s hf).measurable x,
    proposalKernel_apply,proposalKernel_apply]
  change ((conditionedMeasure (Measure.pi fun i:s ↦ (μ i).compProd (κ i))
    {p | Function.updateFinset (fun i ↦ (x i,z i)) s p∈
      retainedEvent (routeChecks σ s hf r anchor allowed label get hg) (s∪(Finset.univ\s))}).map
      (reverseSelected σ s hf)) B=_
  simp only [Finset.union_sdiff_of_subset (Finset.subset_univ s)]
  rw [selected_reverse_same_outside σ s hf r anchor allowed label get hg x z w]
  simp_rw [show ∀j:s,((μ ((selectedPerm σ s hf) j)).compProd (κ ((selectedPerm σ s hf) j))).map
      (reverseFactor (X:=X) σ j)=(ν j).compProd (η j) from he]
  simp only [proposalFiber, Finset.union_sdiff_of_subset (Finset.subset_univ s)]
  rfl

lemma full_paired_reverse {L : Length}
    (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (X (σ i))) [∀i,IsFiniteKernel (η i)]
    (he : ∀j:s,((μ (σ j)).compProd (κ (σ j))).map (reverseFactor (X:=X) σ j)=
        (ν j).compProd (η j))
    (z : ∀i,X (σ.symm i)) (w : ∀i,X (σ i))
    (ξ : Measure (∀i,X i)) [SFinite ξ] :
    (ξ.compProd (proposalKernel (routeChecks σ s hf r anchor allowed label get hg) μ κ s (Finset.univ\s) z)).map
      (Prod.map id (reverseSelected σ s hf))=
    ξ.compProd (proposalKernel (routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg)
      ν η s (Finset.univ\s) w) := by
  rw [←Measure.compProd_map (reverseSelected σ s hf).measurable,
    proposalKernel_reverse σ s hf r anchor allowed label get hg μ ν κ η he z w]

end HardSphere.Bridge

end
end

end

end OAI
