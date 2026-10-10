import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FiniteNestedLaw

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section OldRectangles

structure LabelledRectangle (n : ℕ) where
  length : Fin 2 → ℕ
  length_le : ∀ j, length j ≤ n
  start : Fin 2 → ℤ
  lower : Fin 2 → CutRing
  upper : Fin 2 → CutRing
  ordered : ∀ j, ordinary (lower j) ≤ ordinary (upper j)
  lower_label : ∀ j, start j ≤ endpointLabel (lower j) ∧ endpointLabel (lower j) < start j+length j
  upper_label : ∀ j, start j ≤ endpointLabel (upper j) ∧ endpointLabel (upper j) < start j+length j

namespace LabelledRectangle
variable {n : ℕ} (R : LabelledRectangle n)

noncomputable def polygon (a : ℕ) : polygonAlgebra a := coordinateRectangle a R.lower R.upper

theorem resolved (a : ℕ) (r : CutRing) :
    ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n R.start) i).val) (R.polygon a).val := by
  have hl (j : Fin 2) : R.start j ≤ endpointLabel (R.lower j) ∧ endpointLabel (R.lower j) < R.start j+n := by
    have hh := R.lower_label j; have hh' := R.length_le j; omega
  have hv (j : Fin 2) : R.start j ≤ endpointLabel (R.upper j) ∧ endpointLabel (R.upper j) < R.start j+n := by
    have hh := R.upper_label j; have hh' := R.length_le j; omega
  intro x y he
  exact and_congr (coordinateLabelWindow_resolved n R.start 0 _ _ (hl 0) (hv 0) x y he)
    (coordinateLabelWindow_resolved n R.start 1 _ _ (hl 1) (hv 1) x y he)

structure ChartFit (s : CutRing) (z : CutRing × CutRing) where
  window : Fin 2 → ℤ
  source_start : ∀ j, window j ≤ R.start j
  source_end : ∀ j, R.start j+R.length j ≤ window j+n
  chart_start : ∀ j, window j ≤ pointLabel z j+symmetricWindowStart s j
  chart_end : ∀ j, pointLabel z j+symmetricWindowStart s j+symmetricWindowLength s ≤ window j+n

theorem chartFit_of_near_labels (s : CutRing) (z : CutRing × CutRing)
    (v : Fin 2 → ℤ) (d : Fin 2 → ℕ)
    (hv : ∀ j, R.start j ≤ v j ∧ v j < R.start j+R.length j)
    (hz : ∀ j, (pointLabel z j-v j).natAbs ≤ d j)
    (hsize : ∀ j, R.length j+2*d j+2*(endpointLabel s).natAbs+2 ≤ n) :
    Nonempty (R.ChartFit s z) := by
  have hh (j : Fin 2) := source_chart_containing_window n (R.length j) (R.start j)
    (pointLabel z j) (v j) (endpointLabel s).natAbs (d j) (hv j) (hz j) (hsize j)
  refine ⟨⟨fun j => R.start j ⊓ (pointLabel z j-((endpointLabel s).natAbs:ℤ)),
    fun j => (hh j).1,fun j => (hh j).2.1,?_,?_⟩⟩
  · intro j
    simpa only [symmetricWindowStart,sub_eq_add_neg] using (hh j).2.2.1
  · intro j
    simpa only [symmetricWindowStart,symmetricWindowLength,sub_eq_add_neg] using (hh j).2.2.2

end LabelledRectangle

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

noncomputable def rectangleCopy (hlarge : 15 < m+1) {n : ℕ}
    (g : B.CoordinateWindowLaw n) (R : LabelledRectangle n) :
    TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.windowSector hlarge n g R.start (R.polygon a)

theorem rectangleCopy_supported (hlarge : 15 < m+1) {n : ℕ}
    (g : B.CoordinateWindowLaw n) (R : LabelledRectangle n) :
    B.AlignedSmallSupported (B.rectangleCopy hlarge g R) :=
  B.fullGeometricSector_supported hlarge _ _ _ (R.resolved a r)

theorem rectangleCopy_axes_control (hlarge : 15 < m+1) {n : ℕ}
    (g : B.CoordinateWindowLaw n) (R : LabelledRectangle n) (j : Fin 2) :
    SmallControlled B.c (B.rectangleCopy hlarge g R)
      (B.axisSector hlarge n g j (R.length j) (R.length_le j) (R.start j)
        (coordinateInterval a j (R.lower j) (R.upper j))) := by
  rw [B.axisSector_in_window hlarge n g j _ (R.length_le j) _ R.start le_rfl
    (by have hh := R.length_le j; omega) _
    (axisInterval_resolved j _ _ _ _ (R.lower_label j) (R.upper_label j))]
  apply B.fullGeometricSector_small_control
  fin_cases j
  · exact inf_le_left
  · exact inf_le_right

theorem rectangleCopy_quadrant_control (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s u : CutRing) (hs : 0 < ordinary s ∧ ordinary s < ordinary r)
    (h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) u)
    {n : ℕ} (g : B.CoordinateWindowLaw n) (R : LabelledRectangle n)
    (d : Fin 2) (z : CutRing × CutRing) (positive : Bool) (fit : R.ChartFit s z)
    (hlo : ∀ j, ordinary (signQuadrantLower s d positive j)+ordinary (pointCoordinate z j) ≤ ordinary (R.lower j))
    (hup : ∀ j, ordinary (R.upper j) ≤ ordinary (signQuadrantUpper s d positive j)+ordinary (pointCoordinate z j)) :
    SmallControlled B.c (B.rectangleCopy (by omega) g R)
      (B.tangentSign (by omega) (symmetricWindowLength s) (symmetricWindowStart s) u h d z positive) :=
  B.tangentSign_quadrant_control hlarge hr s u hs h n g R.length R.length_le R.start
    fit.window fit.source_start fit.source_end d z positive fit.chart_start fit.chart_end
    R.lower R.upper R.ordered R.lower_label R.upper_label hlo hup _
    (B.rectangleCopy_supported (by omega) g R) (B.rectangleCopy_axes_control (by omega) g R)

end InitialCoverSystem
end OldRectangles

end SimpleAmenable
end
end

end OAI
