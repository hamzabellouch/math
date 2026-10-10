import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CoordinateTemplateControl
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CrossingCellActions
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentInwardModel

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConcurrentCoordinateGates
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

def concurrentCoordinateEmbedding :
    Sum (Fin 2) (Fin 2 × Fin (A.geometry.window-1)) →
      Sum (Fin 4) (Fin 2 × Fin (A.geometry.window-1)) :=
  Sum.map axisDirection id

noncomputable def concurrentCoordinates (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) := A.concurrentPrimitives t u ∘ A.concurrentCoordinateEmbedding

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem concurrentCoordinates_eq (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) :
    A.concurrentCoordinates t u=fun i =>
      (coordinateTestIndex (Sum.elim id Prod.fst i),
        Sum.elim (fun k => u+A.geometry.anchors t (axisDirection k))
          (fun k => u+(coordinateWindowPrimitives A.geometry.window A.geometry.start k).2) i) := by
  funext i
  cases i <;> rfl

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem coordinate_margin_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentCoordinates t u) i).val)
      (A.geometry.marginPolygon t u).val := by
  intro x y hh
  apply translatedTemplate_resolved (coordinateWindowPrimitives A.geometry.window A.geometry.start)
    (coordinateRectangle a (A.geometry.margins t).lower (A.geometry.margins t).upper)
    (A.geometry.margin_resolved t) u x y
  intro i
  exact hh (Sum.inr i)

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem coordinate_positive_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (k : Fin 2) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentCoordinates t u) i).val)
      (A.geometry.positiveDecision t u (axisDirection k)).val := by
  intro x y hh
  exact hh (Sum.inl k)

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem coordinate_inward_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentCoordinates t u) i).val)
      (A.geometry.inwardMargin t u z).val := by
  intro x y hh
  have hgate k : x ∈ (A.geometry.inwardGate t u z k).val ↔ y ∈ (A.geometry.inwardGate t u z k).val := by
    dsimp only [ConcurrentGeometry.inwardGate]
    split_ifs
    · exact A.coordinate_positive_resolved t u k x y hh
    · exact not_congr (A.coordinate_positive_resolved t u k x y hh)
    · exact Iff.rfl
  exact and_congr (and_congr (A.coordinate_margin_resolved t u x y hh) (hgate 0)) (hgate 1)

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem coordinate_localDecision_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) (k : Fin 2) (c : CutRing) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentCoordinates t u) i).val)
      (A.geometry.localDecision t u z (axisDirection k) c).val := by
  intro x y hh
  dsimp only [ConcurrentGeometry.localDecision]
  split_ifs
  · exact not_congr (A.coordinate_positive_resolved t u k x y hh)
  · exact Iff.rfl
  · exact Iff.rfl

theorem coordinate_control_inward_gate (hlarge : 20 ≤ m+1)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentCoordinates t u) i).val) V.val)
    (n : ℕ) (q : Fin 2 → ℤ) (W : polygonAlgebra a)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (coordinateWindowPrimitives n q) i).val) W.val)
    (hinc : W ≤ V)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q W)) :
    SmallControlled B.c f (B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u) V) := by
  apply B.coordinate_control_to_template hlarge A.rectangles.rectangles _ (A.concurrentLaw t u)
    (Sum.elim id Prod.fst)
    (Sum.elim (fun k => u+A.geometry.anchors t (axisDirection k))
      (fun k => u+(coordinateWindowPrimitives A.geometry.window A.geometry.start k).2))
    A.concurrentCoordinateEmbedding (A.concurrentCoordinates_eq t u) V _ n q W hW hinc f hf hc
  simpa only [← A.concurrentCoordinates_eq t u] using hV

end InitialCoverSystem.PatchAtlas
end ConcurrentCoordinateGates

end SimpleAmenable
end
end

end OAI
