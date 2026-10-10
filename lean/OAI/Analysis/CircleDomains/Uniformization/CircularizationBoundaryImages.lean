import OAI.Analysis.CircleDomains.Topology.SphereCompactFrontier
import OAI.Analysis.CircleDomains.Reflection.AnalyticCoreIteration

namespace OAI

/-! Every boundary curve keeps its label under the actual extended
one-hole circularization. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {I:Type*} [Finite I] {C:FiniteJordanConfiguration I} {j:I}

omit [Finite I] in
lemma Step.other_boundary_image (q:Step C j) {i:I} (hij:i≠j) :
    q.map '' frontier (closedTerminalCap (C.hole i))=
      frontier (closedTerminalCap (q.target.hole i)) := by
  let U := (closedTerminalCap (C.hole j))ᶜ
  have hU : IsOpen U := (isCompact_closedTerminalCap _).isClosed.isOpen_compl
  have hsub : closedTerminalCap (C.hole i)⊆U := by
    intro p hp hpj
    exact Set.disjoint_left.mp (disjoint_closedTerminalCaps C.hole C.disjoint hij) hp hpj
  rw [←q.others i hij]
  exact sphere_frontier_image_of_open_embedding
    (fun p hp => (q.exterior_conformal.1 p hp).1.continuousWithinAt)
    (fun _ hS hSU => q.exterior_conformal.1.isOpen_image hU hS hSU)
    hU q.exterior_conformal.bijOn.injOn (isCompact_closedTerminalCap _) hsub

omit [Finite I] in
lemma Step.extended_boundary_images (q:Step C j)
    (ha:IsAnalyticJordanCap (C.hole j)) :
    let U := (closedTerminalCap (C.hole j))ᶜ
    let T := exteriorDiskNormalization q.center q.radius q.radius_pos
    let E := T.symm ∘ extendFrom U (T ∘ q.map)
    ∀i, E '' frontier (closedTerminalCap (C.hole i))=
      frontier (closedTerminalCap (q.target.hole i)) := by
  dsimp only
  let U := (closedTerminalCap (C.hole j))ᶜ
  let T := exteriorDiskNormalization q.center q.radius q.radius_pos
  let E := T.symm ∘ extendFrom U (T ∘ q.map)
  obtain ⟨_,he,hi,himage⟩ := analytic_closed_exterior_extension ha q.radius_pos q.exterior_conformal
  change EqOn E q.map U at he
  change InjOn E (closure U) at hi
  intro i
  by_cases hij : i=j
  · subst i
    have htarget : closedTerminalCap (q.target.hole j)=
        ((↑):ℂ→Sphere) '' closedBall q.center q.radius := by
      change ((↑):ℂ→Sphere) '' closure (jordanInterior (q.target.hole j))=_
      rw [q.selected,closure_ball _ q.radius_pos.ne']
    rw [htarget,←frontier_compl,←frontier_compl (s:=((↑):ℂ→Sphere) '' closedBall _ _)]
    apply frontier_image_of_closed_extension
      (isCompact_closedTerminalCap _).isClosed.isOpen_compl
      ((isCompact_closedBall _ _).image OnePoint.continuous_coe).isClosed.isOpen_compl hi himage
    rw [image_congr he]
    exact q.exterior_conformal.bijOn.image_eq
  · have hsub : frontier (closedTerminalCap (C.hole i))⊆U := by
      intro p hp hpj
      have hpC := frontier_subset_closure hp
      rw [(isCompact_closedTerminalCap (C.hole i)).isClosed.closure_eq] at hpC
      exact Set.disjoint_left.mp (disjoint_closedTerminalCaps C.hole C.disjoint hij) hpC hpj
    rw [image_congr (he.mono hsub)]
    exact q.other_boundary_image hij

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
