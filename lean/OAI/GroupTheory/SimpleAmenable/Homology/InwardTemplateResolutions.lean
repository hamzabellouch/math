import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CrossingCellActions
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentInwardModel

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section InwardTemplateResolutions
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem concurrent_margin_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentPrimitives t u) i).val)
      (A.geometry.marginPolygon t u).val := by
  intro x y hh
  exact translatedTemplate_resolved (Sum.elim
    (fun j : Fin 4 => (⟨j.val+1,by omega⟩,A.geometry.anchors t j))
    (coordinateWindowPrimitives A.geometry.window A.geometry.start))
    (coordinateRectangle a (A.geometry.margins t).lower (A.geometry.margins t).upper)
    (fun x y hh => A.geometry.margin_resolved t x y (fun i => hh (Sum.inr i))) u x y hh

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem concurrent_positive_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (j : Fin 4) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentPrimitives t u) i).val)
      (A.geometry.positiveDecision t u j).val := by
  intro x y hh
  exact hh (Sum.inl j)

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem concurrent_inward_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentPrimitives t u) i).val)
      (A.geometry.inwardMargin t u z).val := by
  intro x y hh
  have hgate k : x ∈ (A.geometry.inwardGate t u z k).val ↔ y ∈ (A.geometry.inwardGate t u z k).val := by
    dsimp only [ConcurrentGeometry.inwardGate]
    split_ifs
    · exact A.concurrent_positive_resolved t u (axisDirection k) x y hh
    · exact not_congr (A.concurrent_positive_resolved t u (axisDirection k) x y hh)
    · exact Iff.rfl
  exact and_congr (and_congr (A.concurrent_margin_resolved t u x y hh) (hgate 0)) (hgate 1)

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem concurrent_localDecision_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) (j : Fin 4) (c : CutRing) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentPrimitives t u) i).val)
      (A.geometry.localDecision t u z j c).val := by
  intro x y hh
  dsimp only [ConcurrentGeometry.localDecision]
  split_ifs
  · exact not_congr (A.concurrent_positive_resolved t u j x y hh)
  · exact Iff.rfl
  · exact Iff.rfl

end InitialCoverSystem.PatchAtlas

theorem polygonBooleanPullback_resolved {a : ℕ} {ι κ : Type*} [Finite κ]
    (U : ι → polygonAlgebra a) (V : κ → polygonAlgebra a)
    (h : ∀ i, ResolvedBy (fun j => (U j).val) (V i).val) (S : Set (κ → Bool)) :
    ResolvedBy (fun j => (U j).val) (polygonBooleanPullback V S).val := by
  intro x y hxy
  have he : polygonAssignment V x=polygonAssignment V y :=
    (polygonAssignment_eq_iff V x y).mpr (fun i => h i x y hxy)
  change polygonAssignment V x ∈ S ↔ polygonAssignment V y ∈ S
  rw [he]

end InwardTemplateResolutions

end SimpleAmenable
end
end

end OAI
