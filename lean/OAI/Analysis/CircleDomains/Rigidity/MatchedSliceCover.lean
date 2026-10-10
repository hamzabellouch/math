import OAI.Analysis.CircleDomains.Rigidity.MatchedIntervalCoverage
import OAI.Analysis.CircleDomains.Rigidity.MatchedCommonPoints

namespace OAI

/-! Scalar values across an axial segment are covered by actual domain
images, common-point traces and the corresponding remaining target disks. -/
open Set Function Filter
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem scalar_slice_cover
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {γ : ℝ → ℂ} (hγ : Continuous γ) {φ : Sphere → ℝ} (hφ : Continuous φ)
    {a b : ℝ} (hab : a ≤ b) (F : Finset D.IndexedMatchedPair)
    (havoid : ∀ x ∈ Icc a b, ∀ j ∈ F, (γ x : Sphere) ∉ j.val.1) :
    uIcc (φ (D.selectedTarget hG.1 hf (γ a : Sphere)))
      (φ (D.selectedTarget hG.1 hf (γ b : Sphere))) ⊆
      (fun x => φ (f (γ x : Sphere))) '' {x ∈ Icc a b | (γ x : Sphere) ∈ G} ∪
      (fun x => φ (D.selectedTarget hG.1 hf (γ x : Sphere))) ''
        {x ∈ Icc a b | γ x ∈ D.commonPointPlane} ∪
      ⋃ j : {j : D.IndexedMatchedPair // j ∉ F},
        if (∃ x ∈ Icc a b, (γ x : Sphere) ∈ j.val.val.1) then φ '' j.val.val.2 else ∅ := by
  classical
  intro t ht
  obtain ⟨x,hx,p,hp,rfl⟩ := D.interval_scalar_coverage hG.1 hf
    (OnePoint.continuous_coe.comp hγ) hφ hab ht
  by_cases hxG : (γ x : Sphere) ∈ G
  · apply Or.inl
    apply Or.inl
    refine ⟨x,⟨hx,hxG⟩,?_⟩
    rw [D.componentRelation_on_domain hxG hp]
  by_cases hj : ∃ j : D.IndexedMatchedPair, (γ x : Sphere) ∈ j.val.1
  · obtain ⟨j,hxj⟩ := hj
    have hjF : j ∉ F := fun h => havoid x hx j h hxj
    apply Or.inr
    apply mem_iUnion.mpr
    refine ⟨⟨j,hjF⟩,?_⟩
    rw [ite_eq_left (show ∃ z ∈ Icc a b, (γ z : Sphere) ∈ j.val.1 from ⟨x,hx,hxj⟩)]
    refine ⟨p,?_,rfl⟩
    rw [← j.property.1.2.2 (γ x : Sphere) hxj]
    exact hp
  · apply Or.inl
    apply Or.inr
    have hxC : γ x ∈ D.commonPointPlane := ⟨hxG,fun j hj' => hj ⟨j,hj'⟩⟩
    have hsingle := (D.plane_fiber_singleton_or_indexed hG hinf hf hH hinf' (γ x)).resolve_right hj
    exact ⟨x,⟨hx,hxC⟩,congrArg φ (hsingle p hp).symm⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
