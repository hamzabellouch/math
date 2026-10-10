import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.InactiveQuadrantAction
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.InactiveQuadrantAnchors
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentInwardModel
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.InwardMargins

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section InactiveNeighborhoodActions

theorem strict_rectangle_ball (l v : Fin 2 → ℝ) (z : ℝ × ℝ)
    (hz : ∀ k, l k<realCoordinate z k ∧ realCoordinate z k<v k) :
    ∃ δ : ℝ, 0<δ ∧ ∀ y : ℝ × ℝ, dist y z<δ → ∀ k,
      l k<realCoordinate y k ∧ realCoordinate y k<v k := by
  let O : Set (ℝ × ℝ) := ⋂ k : Fin 2, {y | l k<realCoordinate y k} ∩ {y | realCoordinate y k<v k}
  have hO : IsOpen O := by
    apply isOpen_iInter_of_finite
    intro k
    have hc : Continuous (fun y : ℝ × ℝ => realCoordinate y k) := by
      fin_cases k
      · exact continuous_fst
      · exact continuous_snd
    exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hO z (Set.mem_iInter.mpr hz)
  exact ⟨δ,hδ,fun y hy => Set.mem_iInter.mp (hball hy)⟩

namespace InitialCoverSystem.RectangularAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.RectangularAtlas)

theorem inactive_near_action_neighborhood (hlarge : 20 ≤ m+1)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (d : Fin 2)
    (v : CutRing × CutRing) (z : ℝ × ℝ)
    (hinactive : cutForm a (slopeDirection d) z ≠ ordinary (integralCutForm a (slopeDirection d) v))
    (hnear : |cutForm a (slopeDirection d) z-ordinary (integralCutForm a (slopeDirection d) v)|
      <ordinary A.radius) :
    ∃ δ : ℝ, 0<δ ∧ ∃ positive : Bool,
      (positive=true ↔ ordinary (integralCutForm a (slopeDirection d) v)<cutForm a (slopeDirection d) z) ∧
      ∀ L V : Fin 2 → CutRing,
      (∀ k, ordinary (L k) ≤ ordinary (V k)) →
      (∀ k, -ordinary r ≤ ordinary (L k)-ordinary (pointCoordinate v k) ∧
        ordinary (V k)-ordinary (pointCoordinate v k) ≤ ordinary r) →
      (∀ k, |ordinary (L k)-realCoordinate z k|<δ ∧ |ordinary (V k)-realCoordinate z k|<δ) →
      ∀ n q,
      ResolvedBy (fun e => (primitiveTests (a := a) (r := r)
        (coordinateWindowPrimitives n q) e).val) (coordinateRectangle a L V).val →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles n) q (coordinateRectangle a L V)) →
      ∀ (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)),
      ∀ x ∈ f.range,
        A.slope (by omega) d v (universalMap (subtypeAlternatingHom I.val) s)*x*
          (A.slope (by omega) d v (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
        (if positive then B.c (subtypeAlternatingHom I.val (universalProjection _ s)) else 1)*x*
          (if positive then B.c (subtypeAlternatingHom I.val (universalProjection _ s)) else 1)⁻¹ := by
  obtain ⟨u,positive,hline,hsign,hquad⟩ := inactive_slope_quadrant_anchor a d
    (integralCutForm a (slopeDirection d) v) A.radius z hinactive hnear
  obtain ⟨δ,hδ,hball⟩ := strict_rectangle_ball
    (fun k => ordinary (pointCoordinate u k)+ordinary (signQuadrantLower A.radius d positive k))
    (fun k => ordinary (pointCoordinate u k)+ordinary (signQuadrantUpper A.radius d positive k)) z hquad
  refine ⟨δ,hδ,positive,hsign,?_⟩
  intro L V hLV hclip hsmall n q hW f hf hc I s x hx
  have hL : dist (ordinary (L 0),ordinary (L 1)) z<δ := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff]
    exact ⟨(hsmall 0).1,(hsmall 1).1⟩
  have hV : dist (ordinary (V 0),ordinary (V 1)) z<δ := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff]
    exact ⟨(hsmall 0).2,(hsmall 1).2⟩
  have hlo (k : Fin 2) := (hball (ordinary (L 0),ordinary (L 1)) hL k).1.le
  have hup (k : Fin 2) := (hball (ordinary (V 0),ordinary (V 1)) hV k).2.le
  exact A.inactive_quadrant_action hlarge hr d v u positive hline.symm L V hLV hclip
    (fun k => by have he : realCoordinate (ordinary (L 0),ordinary (L 1)) k=ordinary (L k) := by fin_cases k <;> rfl
                 simpa only [he] using hlo k)
    (fun k => by have he : realCoordinate (ordinary (V 0),ordinary (V 1)) k=ordinary (V k) := by fin_cases k <;> rfl
                 simpa only [he] using hup k) n q hW f hf hc I s x hx

end InitialCoverSystem.RectangularAtlas
end InactiveNeighborhoodActions

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r) {ι : Type*}

def InwardChartNeighborhood (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (z : ℝ × ℝ) : Prop :=
  ∀ y : ℝ × ℝ, dist y z<C.epsilon/2 → ∀ k,
    ordinary ((C.margins t).lower k+pointCoordinate u k)<realCoordinate y k ∧
    realCoordinate y k<ordinary ((C.margins t).upper k+pointCoordinate u k)

def InwardChartAnchor (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ) : Prop :=
  ∀ i, cutForm a (j i) z=ordinary (c i) →
    integralCutForm a (j i) (u+C.anchors t (j i))=c i

def InwardChartBound (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ) : Prop :=
  ∀ i, cutForm a (j i) z=ordinary (c i) → ∀ y : ℝ × ℝ,
    (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)≤realCoordinate y k ∧
      realCoordinate y k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
    ∀ k, |realCoordinate y k-ordinary (pointCoordinate (u+C.anchors t (j i)) k)|<3*C.epsilon

def InwardChartBoundaryAnchor (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (z : ℝ × ℝ) : Prop :=
  ∀ k, realCoordinate z k=0 ∨ realCoordinate z k=1 →
    ordinary (pointCoordinate (u+C.anchors t (axisDirection k)) k)=realCoordinate z k

def InwardChartBoundaryBound (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (z : ℝ × ℝ) : Prop :=
  ∀ d, realCoordinate z d=0 ∨ realCoordinate z d=1 → ∀ y : ℝ × ℝ,
    (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)≤realCoordinate y k ∧
      realCoordinate y k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
    ∀ k, |realCoordinate y k-ordinary (pointCoordinate (u+C.anchors t (axisDirection d)) k)|<3*C.epsilon

def InwardChart (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ) :=
  {p : VertexType (commonVertexDenominator a) × (CutRing × CutRing) //
    C.InwardChartNeighborhood p.1 p.2 z ∧ C.InwardChartAnchor p.1 p.2 j c z ∧
    C.InwardChartBound p.1 p.2 j c z ∧ C.InwardChartBoundaryAnchor p.1 p.2 z ∧
    C.InwardChartBoundaryBound p.1 p.2 z}

namespace InwardChart
variable {C} {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ} (T : C.InwardChart j c z)
def vertex : VertexType (commonVertexDenominator a) := T.val.1
def offset : CutRing × CutRing := T.val.2
theorem neighborhood : C.InwardChartNeighborhood T.vertex T.offset z := T.property.1
theorem active_anchor : C.InwardChartAnchor T.vertex T.offset j c z := T.property.2.1
theorem active_bound : C.InwardChartBound T.vertex T.offset j c z := T.property.2.2.1
theorem boundary_anchor : C.InwardChartBoundaryAnchor T.vertex T.offset z := T.property.2.2.2.1
theorem boundary_bound : C.InwardChartBoundaryBound T.vertex T.offset z := T.property.2.2.2.2
end InwardChart

theorem inwardChart_exists (ha : 0<a) (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ) :
    Nonempty (C.InwardChart j c z) := by
  classical
  let J : Sum ι (Fin 2 × Bool) → Fin 4 := Sum.elim j (fun d => axisDirection d.1)
  let K : Sum ι (Fin 2 × Bool) → CutRing := Sum.elim c (fun d => if d.2 then 1 else 0)
  obtain ⟨t,u,hcell,hactive⟩ := C.simultaneous_active_neighborhood ha J K z
  have hb (k : Fin 2) (hk : realCoordinate z k=0 ∨ realCoordinate z k=1) :
      ∃ b : Bool, cutForm a (J (.inr (k,b))) z=ordinary (K (.inr (k,b))) := by
    have haxis : cutForm a (axisDirection k) z=realCoordinate z k := by fin_cases k <;> rfl
    rcases hk with hk | hk
    · exact ⟨false,by simpa only [J,K,Sum.elim_inr,Bool.false_eq_true,↓reduceIte,map_zero,haxis] using hk⟩
    · exact ⟨true,by simpa only [J,K,Sum.elim_inr,↓reduceIte,map_one,haxis] using hk⟩
  refine ⟨⟨(t,u),hcell,(fun i hi => (hactive (.inl i) hi).1),
    (fun i hi => (hactive (.inl i) hi).2),?_,?_⟩⟩
  · intro k hk
    obtain ⟨b,hb⟩ := hb k hk
    have he := congrArg ordinary (hactive (.inr (k,b)) hb).1
    have haxis : cutForm a (axisDirection k) z=realCoordinate z k := by fin_cases k <;> rfl
    change ordinary (integralCutForm a (axisDirection k) (u+C.anchors t (axisDirection k)))=_ at he
    rw [integralCutForm_axis] at he
    exact he.trans (by simpa only [J,Sum.elim_inr,haxis] using hb.symm)
  · intro k hk
    obtain ⟨b,hb⟩ := hb k hk
    exact (hactive (.inr (k,b)) hb).2

namespace InwardChart
variable {C} {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ} (T : C.InwardChart j c z)

theorem canonical_mem (hr : 0<ordinary r ∧ ordinary r<1/2)
    (p : GenericSquare a) (hp : dist p.val z<C.epsilon/2) :
    p ∈ (C.inwardMargin T.vertex T.offset z).val :=
  C.mem_inwardMargin_of_planar hr T.vertex T.offset z T.boundary_anchor T.boundary_bound p
    (fun k => ⟨(T.neighborhood p.val hp k).1.le,(T.neighborhood p.val hp k).2⟩)

theorem assignment_realized [Finite ι] (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (p : GenericSquare a) (hp : p ∈ (C.inwardMargin T.vertex T.offset z).val)
    (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N) :
    ∃ q : GenericSquare a, q.val ∈ N ∧
      polygonAssignment (fun i => cutPolygon a (j i) (c i)) q=
        polygonAssignment (fun i => C.localDecision T.vertex T.offset z (j i) (c i)) p :=
  C.localDecision_assignment_realized hr T.vertex T.offset j c z hz₁ hz₂
    T.active_anchor T.boundary_anchor T.active_bound T.boundary_bound p hp N hN hz

theorem local_decisions_eq (hr : 0<ordinary r ∧ ordinary r<1/2)
    (p : GenericSquare a) (hp : dist p.val z<C.epsilon/2) :
    polygonAssignment (fun i => C.localDecision T.vertex T.offset z (j i) (c i)) p=
      polygonAssignment (localCutFamily j c z) p := by
  classical
  have hy : p.val=(Int.fract p.val.1,Int.fract p.val.2) := by
    rw [Int.fract_eq_self.mpr p.property.1,Int.fract_eq_self.mpr p.property.2.1]
  have hcell k := (T.neighborhood p.val hp k).imp le_of_lt le_of_lt
  funext i
  apply decide_eq_decide.mpr
  by_cases hi : cutForm a (j i) z=ordinary (c i)
  · have hd := C.positiveDecision_planar hr T.vertex T.offset (j i) (T.active_bound i hi) p p.val hy hcell
    rw [T.active_anchor i hi] at hd
    simp only [localDecision,localCutFamily,ite_eq_left hi]
    change (p ∉ (C.positiveDecision T.vertex T.offset (j i)).val) ↔ cutForm a (j i) p.val<ordinary (c i)
    exact (not_congr hd).trans not_le
  · simp only [localDecision,localCutFamily,ite_eq_right hi]

noncomputable def polygons [Finite ι] {κ : Type*} (R : κ → polygonAlgebra a) (i : κ) : polygonAlgebra a :=
  polygonBooleanPullback (fun i => C.localDecision T.vertex T.offset z (j i) (c i))
    (polygonFormalMask (fun i => cutPolygon a (j i) (c i)) (R i))

theorem polygons_assignment_realized [Finite ι] {κ : Type*}
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (R : κ → polygonAlgebra a)
    (hR : ∀ k, ResolvedBy (fun i => halfPlane a (j i) (c i)) (R k).val)
    (p : GenericSquare a) (hp : p ∈ (C.inwardMargin T.vertex T.offset z).val)
    (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N) :
    ∃ q : GenericSquare a, q.val ∈ N ∧ polygonAssignment R q=polygonAssignment (T.polygons R) p := by
  obtain ⟨q,hq,he⟩ := T.assignment_realized hr hz₁ hz₂ p hp N hN hz
  refine ⟨q,hq,?_⟩
  funext k
  apply decide_eq_decide.mpr
  change (q ∈ (R k).val) ↔ polygonAssignment (fun i => C.localDecision T.vertex T.offset z (j i) (c i)) p ∈
    polygonFormalMask (fun i => cutPolygon a (j i) (c i)) (R k)
  rw [← he]
  exact (polygonFormalMask_mem _ (R k) (hR k) q).symm

theorem polygons_locally_eq [Finite ι] {κ : Type*}
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (R : κ → polygonAlgebra a)
    (hR : ∀ k, ResolvedBy (fun i => halfPlane a (j i) (c i)) (R k).val) :
    ∃ N : Set (ℝ × ℝ), IsOpen N ∧ z ∈ N ∧ ∀ p : GenericSquare a, p.val ∈ N →
      p ∈ (C.inwardMargin T.vertex T.offset z).val ∧ ∀ k, p ∈ (T.polygons R k).val ↔ p ∈ (R k).val := by
  obtain ⟨O,hO,hz,hlocal⟩ := localPolygonFamily_locally_eq j c z R hR
  refine ⟨O ∩ Metric.ball z (C.epsilon/2),hO.inter Metric.isOpen_ball,
    ⟨hz,by simp only [Metric.mem_ball,dist_self]; linarith [C.positive]⟩,?_⟩
  intro p hp
  refine ⟨T.canonical_mem hr p hp.2,fun k => ?_⟩
  have he := T.local_decisions_eq hr p hp.2
  change polygonAssignment (fun i => C.localDecision T.vertex T.offset z (j i) (c i)) p ∈
    polygonFormalMask (fun i => cutPolygon a (j i) (c i)) (R k) ↔ _
  rw [he]
  exact hlocal p hp.1 k

end InwardChart
end ConcurrentGeometry

end SimpleAmenable

end OAI
