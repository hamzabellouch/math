import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeTopGroup
import OAI.Geometry.HyperbolicGroups.ConeDecorationGroup
import OAI.Geometry.HyperbolicGroups.PolygonBoundaryList

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- The actual indexed polygon words. Radial edges are not silently equated
or turned into extra letter relators. This bouquet presentation has extra
free factors relative to the graph fundamental group, but the original
letter relations still hold in it, which is all the disk producer needs. -/
abbrev PolygonGroup := PresentedGroup (FreeGroup.mk '' Set.range (boundary n w d).attachingWord)

def polygonValue (e : Dart n w) : PolygonGroup n w d := PresentedGroup.mk _ (FreeGroup.mk [e])

lemma polygonValue_rev (e : Dart n w) :
    polygonValue n w d (rev n w e) = (polygonValue n w d e)⁻¹ := by
  unfold polygonValue
  rw [← map_inv]
  congr 1

lemma polygonValue_word (z : List (Dart n w)) :
    PresentedGroup.mk (FreeGroup.mk '' Set.range (boundary n w d).attachingWord)
      (FreeGroup.mk z) = (z.map (polygonValue n w d)).prod := by
  induction z with
  | nil => exact map_one _
  | cons a z ih =>
    change PresentedGroup.mk _ (FreeGroup.mk ([a]++z)) = _
    rw [← FreeGroup.mul_mk,map_mul,ih]
    rfl

lemma polygonValue_cell (a : Cell n w d) :
    (List.ofFn (fun i => polygonValue n w d (side n w d a i))).prod = 1 := by
  have he := PresentedGroup.one_of_mem (show FreeGroup.mk (List.ofFn (side n w d a)) ∈
      FreeGroup.mk '' Set.range (boundary n w d).attachingWord from
    ⟨(boundary n w d).attachingWord a,⟨a,rfl⟩,rfl⟩)
  rw [polygonValue_word,List.map_ofFn] at he
  exact he

def freeComparison : FreeGroup (Fin (n+1)) →* PolygonGroup n w d :=
  (PresentedGroup.mk _).comp (FreeGroup.map (Sum.inl : Fin (n+1) → Edge n w))

lemma freeComparison_letter (a : Alphabet n) :
    freeComparison n w d (freeLetter n a) = polygonValue n w d (letterDart n w a) := by
  rw [freeLetter_mk]
  simp only [freeComparison,MonoidHom.comp_apply,FreeGroup.map.mk,List.map_cons,List.map_nil]
  rfl

lemma freeComparison_word (z : List (Alphabet n)) :
    freeComparison n w d (FreeGroup.mk z) =
    PresentedGroup.mk (FreeGroup.mk '' Set.range (boundary n w d).attachingWord)
      (FreeGroup.mk (z.map (letterDart n w))) := by
  simp only [freeComparison,MonoidHom.comp_apply,FreeGroup.map.mk]
  rfl

/-- Both arbitrary closed-walk relator families, including the exceptional
loose edge, and both decoration families are consequences of the literal
fan triangles and simple macro polygons. -/
lemma freeComparison_relator (r : FreeGroup (Fin (n+1))) (hr : Relator n w d r) :
    freeComparison n w d r = 1 := by
  have hc := polygonValue_rev n w d
  have hcell := polygonValue_cell n w d
  cases hr with
  | fan l i present v p fields =>
    rw [MasterGraph.Path.eval_map]
    simp only [freeComparison_letter]
    exact fan_relator_value n w d (polygonValue n w d) hc hcell l i present v p fields
  | top l present fans v p core =>
    rw [MasterGraph.Path.eval_map]
    simp only [freeComparison_letter]
    exact top_relator_value n w d (polygonValue n w d) hc hcell l present fans v p core
  | square l τ present =>
    rw [MasterGraph.squareWord_map]
    simp only [freeComparison_letter]
    exact square_relator_value n w d (polygonValue n w d) hc hcell l τ present
  | six x present =>
    rw [map_list_prod,List.map_ofFn]
    simp only [Function.comp_def,freeComparison_letter]
    exact six_relator_value n w d (polygonValue n w d) hcell x present

lemma relator_normalClosure_le :
    Subgroup.normalClosure (Relator n w d) ≤ (freeComparison n w d).ker := by
  apply Subgroup.normalClosure_le_normal
  intro r hr
  exact freeComparison_relator n w d r hr

/-- No round trip or presentation-equivalence assumption: every original
null letter word is an actual cone-polygon nullword. -/
theorem nullWord_to_polygon (z : List (Alphabet n))
    (hz : PresentedGroup.mk (Relator n w d) (FreeGroup.mk z) = 1) :
    PresentedGroup.mk (FreeGroup.mk '' Set.range (boundary n w d).attachingWord)
      (FreeGroup.mk (z.map (letterDart n w))) = 1 := by
  have hh := relator_normalClosure_le n w d (PresentedGroup.mk_eq_one_iff.mp hz)
  change freeComparison n w d (FreeGroup.mk z) = 1 at hh
  rwa [freeComparison_word] at hh

end HyperbolicObstruction.ConeSkeleton
end

end OAI
