import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.IndividualGridSplits
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CrossingCellActions
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalLaws
import OAI.GroupTheory.SimpleAmenable.CentralCovers.InitialGridActions
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.InwardPlanarGerms

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PrimitiveStarCoherence
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem primitiveStar_eq_of_predicate (hlarge : 15 < m+1) (j : Fin 5)
    (u v : CutRing × CutRing)
    (he : spatialTranslate u (initialTest a r j)=spatialTranslate v (initialTest a r j)) :
    A.primitiveStar hlarge (j,u)=A.primitiveStar hlarge (j,v) := by
  unfold primitiveStar
  rw [he]
  apply B.fullGeometricSector_shared_test hlarge _ _ (Sum.inl j) (Sum.inl j)
  · rfl
  · simpa only [translatedTemplate,initialPatchPrimitives,Sum.elim_inl,add_zero] using he
  · intro x y hh
    have h := hh ()
    simpa only [primitiveTests,primitiveFamilyTests,translatedTemplate,initialPatchPrimitives,
      Sum.elim_inl,add_zero,he] using h

theorem primitiveStar_periodic (hlarge : 15 < m+1) (j : Fin 5)
    (u : CutRing × CutRing) (k : Fin 2 → ℤ) :
    A.primitiveStar hlarge (j,u+((k 0:CutRing),(k 1:CutRing)))=
      A.primitiveStar hlarge (j,u) := by
  apply A.primitiveStar_eq_of_predicate hlarge j
  rw [spatialTranslate_add,spatialTranslate_integral]

theorem concurrent_primitiveStar (hlarge : 15 < m+1)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing) (j : Fin 4) :
    B.fullGeometricSector hlarge (A.concurrentPrimitives t u) (A.concurrentLaw t u)
      (A.geometry.positiveDecision t u j)=
    A.primitiveStar hlarge (⟨j.val+1,by omega⟩,u+A.geometry.anchors t j) := by
  unfold primitiveStar
  apply B.fullGeometricSector_shared_test hlarge _ _ (Sum.inl j)
    (Sum.inl ⟨j.val+1,by omega⟩)
  · rfl
  · simp only [concurrentPrimitives,translatedTemplate,Sum.elim_inl,initialPatchPrimitives,add_zero]
  · intro x y hh
    have h := hh ()
    simpa [primitiveTests,primitiveFamilyTests,concurrentPrimitives,translatedTemplate,
      ConcurrentGeometry.positiveDecision,initialTest] using h

theorem concurrent_slope (hlarge : 15 < m+1)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing) (d : Fin 2) :
    B.fullGeometricSector hlarge (A.concurrentPrimitives t u) (A.concurrentLaw t u)
      (A.geometry.positiveDecision t u (slopeDirection d))=
      A.rectangles.slope hlarge d (u+A.geometry.anchors t (slopeDirection d)) := by
  have h := A.concurrent_primitiveStar hlarge t u (slopeDirection d)
  have he : (⟨(slopeDirection d).val+1,by omega⟩:Fin 5)=slopeTestIndex d := rfl
  rw [he,A.primitiveStar_slope] at h
  exact h

end InitialCoverSystem.PatchAtlas
end PrimitiveStarCoherence

end SimpleAmenable
end
end

end OAI
