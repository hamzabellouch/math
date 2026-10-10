import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.VaryingCellClassification
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SupportedCellPatching

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConcurrentCellDecisions
namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

theorem cell_axis_eq (q : Fin 2 → ℤ) (cell : Fin 2 → Fin C.mesh)
    (j : Fin 2) (v : CutRing × CutRing) (c : CutRing) (positive : Bool)
    (hc : ∀ p ∈ (windowRectangle a C.mesh q cell).val,
      (p ∈ (spatialTranslate v (coordinatePrimitive a j)).val ↔
        if positive then ordinary c≤realCoordinate (windowPlanarLift q p) j
        else realCoordinate (windowPlanarLift q p) j<ordinary c))
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (haxis : integralCutForm a (axisDirection j) (u+C.anchors t (axisDirection j))=c)
    (hmargin : ∀ p : ℝ × ℝ,
      (∀ k, ordinary (windowCut C.mesh (q k) (cell k).castSucc)≤realCoordinate p k ∧
        realCoordinate p k≤ordinary (windowCut C.mesh (q k) (cell k).succ)) →
      ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)<realCoordinate p k ∧
        realCoordinate p k<ordinary ((C.margins t).upper k+pointCoordinate u k))
    (hnear : ∀ p : ℝ × ℝ,
      (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)≤realCoordinate p k ∧
        realCoordinate p k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
      ∀ k, |realCoordinate p k-ordinary (pointCoordinate (u+C.anchors t (axisDirection j)) k)|<3*C.epsilon) :
    spatialTranslate v (coordinatePrimitive a j) ⊓ windowRectangle a C.mesh q cell =
      (if positive then spatialTranslate (u+C.anchors t (axisDirection j)) (coordinatePrimitive a j)
        else (spatialTranslate (u+C.anchors t (axisDirection j)) (coordinatePrimitive a j))ᶜ) ⊓
      windowRectangle a C.mesh q cell := by
  apply Subtype.ext
  ext p
  change (p ∈ (spatialTranslate v (coordinatePrimitive a j)).val ∧
      p ∈ (windowRectangle a C.mesh q cell).val) ↔ _
  by_cases hp : p ∈ (windowRectangle a C.mesh q cell).val
  · have hz := hmargin (windowPlanarLift q p) (fun k =>
      ⟨((windowRectangle_mem C.mesh C.mesh_large q cell p).mp hp k).1,
        ((windowRectangle_mem C.mesh C.mesh_large q cell p).mp hp k).2.le⟩)
    have hh := C.axis_on_margin j u (u+C.anchors t (axisDirection j)) t hnear p
      (windowPlanarLift q p) (windowPlanarLift_spec q p) (fun k => ⟨(hz k).1.le,(hz k).2.le⟩)
    rw [integralCutForm_axis] at haxis
    rw [haxis] at hh
    cases positive <;> simp only [Bool.false_eq_true,↓reduceIte] at hc ⊢
    · change (_ ∧ _) ↔ (¬ p ∈ (spatialTranslate (u+C.anchors t (axisDirection j)) (coordinatePrimitive a j)).val ∧ _)
      exact and_congr ((hc p hp).trans ((not_le).symm.trans (not_congr hh).symm)) Iff.rfl
    · change (_ ∧ _) ↔ (p ∈ (spatialTranslate (u+C.anchors t (axisDirection j)) (coordinatePrimitive a j)).val ∧ _)
      exact and_congr ((hc p hp).trans hh.symm) Iff.rfl
  · change (_ ∧ _) ↔ (_ ∧ _)
    simp only [hp,and_false]

end ConcurrentGeometry
end ConcurrentCellDecisions

end SimpleAmenable
end
end

end OAI
