import Mathlib
import OAI.GroupTheory.SimpleAmenable.Arithmetic.PropagationArithmetic
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TangentChartTemplates
import OAI.GroupTheory.SimpleAmenable.Homology.ChartControlChain

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section LabelShiftedCharts

noncomputable def pointCoordinate (z : CutRing × CutRing) (j : Fin 2) : CutRing :=
  if j=0 then z.1 else z.2

noncomputable def pointLabel (z : CutRing × CutRing) (j : Fin 2) : ℤ := endpointLabel (pointCoordinate z j)

@[simp] theorem pointCoordinate_add (z w : CutRing × CutRing) (j : Fin 2) :
    pointCoordinate (z+w) j = pointCoordinate z j+pointCoordinate w j := by
  fin_cases j <;> rfl

@[simp] theorem pointLabel_add (z w : CutRing × CutRing) (j : Fin 2) :
    pointLabel (z+w) j = pointLabel z j+pointLabel w j := by
  simp only [pointLabel,pointCoordinate_add,endpointLabel_add]

@[simp] theorem endpointLabel_int_mul_tau (i : ℤ) :
    endpointLabel ((i : CutRing)*cutTau) = i := by simp [endpointLabel,cutTau]

@[simp] theorem coordinateWindow_pointLabel (k : ℕ) (p : Fin 2 → ℤ)
    (i : Fin 2 × Fin (k-1)) :
    pointLabel (coordinateWindowPrimitives k p i).2 i.1 = p i.1+(i.2.val:ℤ) := by
  simp only [coordinateWindowPrimitives,pointLabel,pointCoordinate,coordinateShift]
  split <;> rw [← Int.cast_add, endpointLabel_int_mul_tau]

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangentChartSector_eq_window (hlarge : 15 < m+1)
    (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k p u)
    (n : ℕ) (hn : k ≤ n) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (e : Fin 5) (z : CutRing × CutRing)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, p j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < p j+k)
    (hv : ∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+k) :
    B.fullGeometricSector hlarge
      (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z) (h d e z)
      (spatialTranslate z (coordinateRectangle a l v)) =
    B.windowSector hlarge n g (fun j => pointLabel z j+p j)
      (spatialTranslate z (coordinateRectangle a l v)) := by
  apply B.chartCoordinateSector_eq_window hlarge n g (fun j => pointLabel z j+p j)
    _ (h d e z) Sum.inr Prod.fst (fun i => z+(coordinateWindowPrimitives k p i).2)
  · intro i
    rfl
  · intro i
    change pointLabel z i.1+p i.1 ≤ pointLabel (z+(coordinateWindowPrimitives k p i).2) i.1
    simp only [pointLabel_add,coordinateWindow_pointLabel]
    omega
  · intro i
    change pointLabel (z+(coordinateWindowPrimitives k p i).2) i.1 <
      pointLabel z i.1+p i.1+(n-1:ℕ)
    simp only [pointLabel_add,coordinateWindow_pointLabel]
    have hi := i.2.isLt
    omega
  · intro x y he
    apply (translatedTemplate_resolved (a := a) (r := r) (coordinateWindowPrimitives k p)
      (coordinateRectangle a l v) (fun x y he => and_congr
        (coordinateLabelWindow_resolved k p 0 (l 0) (v 0) (hl 0) (hv 0) x y he)
        (coordinateLabelWindow_resolved k p 1 (l 1) (v 1) (hl 1) (hv 1) x y he)) z) x y
    simpa only [primitiveTests,primitiveFamilyTests,translatedTemplate,coordinateWindowPrimitives,
      initialTest_coordinate] using he

end InitialCoverSystem
end LabelShiftedCharts

end SimpleAmenable
end
end

end OAI
