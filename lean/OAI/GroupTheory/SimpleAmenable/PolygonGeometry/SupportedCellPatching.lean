import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.InvariantPatching
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.LocalCoordinateClassifier
import OAI.GroupTheory.SimpleAmenable.CentralCovers.SmallFormalGlobal
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentGeometry
import OAI.GroupTheory.SimpleAmenable.CentralCovers.SmallStarRelators

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SupportedCellPatching
variable {α ι D H : Type*} [Fintype α] [DecidableEq α] [Finite ι] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

theorem supported_cell_patching
    (F : Option ι → TrackStar α →* H)
    (f : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (hspec : ∀ I i, (F i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val)))
    (P : D → Subgroup H)
    (hgen : (copyFamilyEval F).range ≤ ⨆ d, P d)
    (hinv : ∀ d i s, F i s ∈ Subgroup.normalizer (P d : Set H))
    (G : D → Option ι → TrackStar α →* H)
    (hact : ∀ d (I : FiveAlphabet α) i s,
      ∀ x ∈ P d,
        F i (universalMap (subtypeAlternatingHom I.val) s)*x*
          (F i (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
        G d i (universalMap (subtypeAlternatingHom I.val) s)*x*
          (G d i (universalMap (subtypeAlternatingHom I.val) s))⁻¹)
    (hlocal : ∀ d (S : Finset α), S.card ≤ 15 → ∀ w ∈ smallFamilyLocal (ι := ι) S,
      smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}) w=1 →
      ∀ x ∈ P d, Commute (copyFamilyEval (G d) (smallFamilyStarWord w)) x)
    (hα : 5 ≤ Fintype.card α) :
    HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval f).rangeRestrict := by
  classical
  let f₀ : SmallFamilyLabel α ι → H := fun l => f l.1 l.2.1 l.2.2
  have hfs (I : FiveAlphabet α) (i : Option ι) (s : alternatingGroup I.val) :
      f I i s=F i (alphabetStarLift I s) := by
    have hh := DFunLike.congr_fun (hspec I i)
      (Classical.choose (universalProjection_surjective (alternatingGroup I.val) s))
    simpa only [MonoidHom.comp_apply,alphabetStarLift,
      Classical.choose_spec (universalProjection_surjective (alternatingGroup I.val) s)] using hh.symm
  have hgen' : (FreeGroup.lift f₀).range ≤ ⨆ d, P d := by
    rintro x ⟨w,rfl⟩
    apply hgen
    refine ⟨smallFamilyStarWord w,?_⟩
    exact DFunLike.congr_fun (smallFamilyStarWord_eval F f hspec) w
  apply smallFamily_assignment_law _ ?_ f ?_ hα
  · intro σ τ h
    funext i
    exact Bool.eq_iff_iff.mpr (h i)
  · intro S hS w hw hrel v _hv
    have hc := patching_centrality f₀ P hgen' (fun d l => by
      rw [show f₀ l=F l.2.1 (alphabetStarLift l.1 l.2.2) from hfs _ _ _]
      exact hinv _ _ _) w ?_
    · exact hc _ ⟨v,rfl⟩
    · intro d
      let g : SmallFamilyLabel α ι → H := fun l => G d l.2.1 (alphabetStarLift l.1 l.2.2)
      have hg : (FreeGroup.lift g)=(copyFamilyEval (G d)).comp smallFamilyStarWord := by
        apply FreeGroup.ext_hom
        rintro ⟨I,i,s⟩
        simp [g,smallFamilyStarWord]
      refine ⟨g,?_,?_⟩
      · intro l x hx
        rw [show f₀ l=F l.2.1 (alphabetStarLift l.1 l.2.2) from hfs _ _ _]
        exact hact d l.1 l.2.1 _ x hx
      · rw [hg]
        intro x hx
        exact (hlocal d S hS w hw hrel x hx).eq.symm

end SupportedCellPatching

section ConcurrentAxisDecisions

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

theorem axis_on_margin (j : Fin 2) (u b : CutRing × CutRing)
    (t : VertexType (commonVertexDenominator a))
    (hnear : ∀ z : ℝ × ℝ,
      (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)≤realCoordinate z k ∧
        realCoordinate z k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
      ∀ k, |realCoordinate z k-ordinary (pointCoordinate b k)|<3*C.epsilon)
    (p : GenericSquare a) (z : ℝ × ℝ) (hz : p.val=(Int.fract z.1,Int.fract z.2))
    (hcell : ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)≤realCoordinate z k ∧
      realCoordinate z k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) :
    p ∈ (spatialTranslate b (coordinatePrimitive a j)).val ↔
      ordinary (pointCoordinate b j)≤realCoordinate z j := by
  have hh := abs_lt.mp (hnear z hcell j)
  apply translated_coordinate_planar j b p z hz
  · have hg := C.second_gap
    have hp := C.positive
    linarith
  · have hg := C.first_gap
    have hp := C.positive
    linarith

theorem cell_le_margin (hr : ordinary r<1/2)
    (q : Fin 2 → ℤ) (cell : Fin 2 → Fin C.mesh)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (hmargin : ∀ z : ℝ × ℝ,
      (∀ k, ordinary (windowCut C.mesh (q k) (cell k).castSucc)≤realCoordinate z k ∧
        realCoordinate z k≤ordinary (windowCut C.mesh (q k) (cell k).succ)) →
      ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)<realCoordinate z k ∧
        realCoordinate z k<ordinary ((C.margins t).upper k+pointCoordinate u k)) :
    windowRectangle a C.mesh q cell ≤
      spatialTranslate u (coordinateRectangle a (C.margins t).lower (C.margins t).upper) := by
  rw [spatialTranslate_coordinateRectangle]
  intro p hp
  have hmb := hmargin (windowPlanarLift q p) (fun k =>
    ⟨((windowRectangle_mem C.mesh C.mesh_large q cell p).mp hp k).1,
      ((windowRectangle_mem C.mesh C.mesh_large q cell p).mp hp k).2.le⟩)
  have hc (j : Fin 2) : p ∈ (coordinateInterval a j
      ((C.margins t).lower j+pointCoordinate u j)
      ((C.margins t).upper j+pointCoordinate u j)).val := by
    have hw := (C.margins t).width C.positive j
    have hrad := C.radius
    have hwidth : 0≤ordinary ((C.margins t).upper j+pointCoordinate u j)-
        ordinary ((C.margins t).lower j+pointCoordinate u j) ∧
        ordinary ((C.margins t).upper j+pointCoordinate u j)-
        ordinary ((C.margins t).lower j+pointCoordinate u j)<1 := by
      simp only [map_add]
      constructor <;> linarith
    rw [coordinateInterval_planar j _ _ hwidth p _ (windowPlanarLift_spec q p)]
    rw [Int.fract_eq_self.mpr (show 0≤realCoordinate (windowPlanarLift q p) j-
          ordinary ((C.margins t).lower j+pointCoordinate u j) ∧
        realCoordinate (windowPlanarLift q p) j-
          ordinary ((C.margins t).lower j+pointCoordinate u j)<1 from
        ⟨by linarith [(hmb j).1],by linarith [(hmb j).2,hwidth.2]⟩)]
    linarith [(hmb j).2]
  exact ⟨hc 0,hc 1⟩

end ConcurrentGeometry
end ConcurrentAxisDecisions

end SimpleAmenable
end
end

end OAI
