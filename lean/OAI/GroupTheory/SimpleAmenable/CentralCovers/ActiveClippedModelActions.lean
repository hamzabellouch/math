import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.InitialGridActions
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveStarCoherence
import OAI.GroupTheory.SimpleAmenable.CentralCovers.SelectedInwardActions
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ClippedGerms

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem inward_model_resolved {ι κ : Type*} [Finite ι]
    {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ}
    (T : A.geometry.InwardChart j c z) (R : κ → polygonAlgebra a) (i : κ) :
    ResolvedBy (fun e => (primitiveTests (a := a) (r := r) (A.concurrentPrimitives T.vertex T.offset) e).val)
      (T.polygons R i).val :=
  polygonBooleanPullback_resolved _ _
    (fun e => A.concurrent_localDecision_resolved T.vertex T.offset z (j e) (c e)) _

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem concurrent_coordinateGate_resolved {κ : Type*} [Finite κ]
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing) (z : ℝ × ℝ)
    (j : κ → Fin 2) (c : κ → CutRing) (σ : κ → Bool) :
    ResolvedBy (fun e => (primitiveTests (a := a) (r := r) (A.concurrentPrimitives t u) e).val)
      (A.geometry.coordinateGate t u z j c σ).val :=
  fun x y hh => A.coordinateGate_resolved t u z j c σ x y
    (fun i => hh (A.concurrentCoordinateEmbedding i))

theorem active_clipped_model_action {ι : Type*} [Finite ι]
    (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (d : Fin 2) (u : CutRing × CutRing) (z : ℝ × ℝ)
    (G : ClippedGerm a r (slopeDirection d) u z)
    {j : ι → Fin 4} {c : ι → CutRing} (T : A.geometry.InwardChart j c z)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (lo hi : Fin 2 → ι) (slope : ι)
    (hlo : ∀ k, j (lo k)=axisDirection k ∧ c (lo k)=pointCoordinate G.offset k-r)
    (hhi : ∀ k, j (hi k)=axisDirection k ∧ c (hi k)=pointCoordinate G.offset k+r)
    (hs : j slope=slopeDirection d ∧ c slope=integralCutForm a (slopeDirection d) G.offset)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i))
      (spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))).val)
    (hactive : cutForm a (j slope) z=ordinary (c slope))
    (σ : Fin 2 × Bool → Bool) (hσ : ∀ k, σ (k,false)=false ∧ σ (k,true)=true)
    (L V : Fin 2 → CutRing) (hLV : ∀ k, ordinary (L k) ≤ ordinary (V k))
    (hclip : ∀ k, -ordinary r≤ordinary (L k)-ordinary (pointCoordinate G.offset k) ∧
      ordinary (V k)-ordinary (pointCoordinate G.offset k)≤ordinary r)
    (hnear : ∀ k, |ordinary (L k)-realCoordinate z k|<A.geometry.epsilon/2 ∧
      |ordinary (V k)-realCoordinate z k|<A.geometry.epsilon/2)
    (n : ℕ) (q : Fin 2 → ℤ)
    (hW : ResolvedBy (fun e => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) e).val) (coordinateRectangle a L V).val)
    (hinc : coordinateRectangle a L V ≤
      A.geometry.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q
      (coordinateRectangle a L V)))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (x : BoundedRelationCover M (alternatingGenerator a r m hm)) (hx : x ∈ f.range) :
    A.primitiveStar (by omega) (slopeTestIndex d,u) (universalMap (subtypeAlternatingHom I.val) s)*x*
      (A.primitiveStar (by omega) (slopeTestIndex d,u) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
      (T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))) ())
        (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
        (T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))) ())
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  have hperiod := A.primitiveStar_periodic (by omega) (slopeTestIndex d) u G.period
  change A.primitiveStar (by omega) (slopeTestIndex d,G.offset)=_ at hperiod
  rw [← hperiod,A.primitiveStar_slope]
  have ha := A.selected_active_slope_actions hlarge hr T slope hactive d hs.1 G.offset hs.2.symm
    L V hLV hclip hnear n q hW f hf hc I s x hx
  rw [hs.1,← A.concurrent_slope] at ha
  apply ha.trans
  have he := G.model_restrict_gate T hr hz₁ hz₂ lo hi slope hlo hhi hs hR σ
  rw [ite_eq_left hσ] at he
  have hactive' : cutForm a (slopeDirection d) z=ordinary (c slope) := by
    simpa only [hs.1] using hactive
  simp only [ConcurrentGeometry.localDecision,hs.1,hactive',↓reduceIte,compl_compl] at he
  exact B.chart_action_transfer hlarge _ (A.concurrentLaw T.vertex T.offset) _ _ _
    (A.concurrent_positive_resolved T.vertex T.offset (slopeDirection d))
    (A.inward_model_resolved T _ ())
    (A.concurrent_coordinateGate_resolved T.vertex T.offset z Prod.fst G.axialCut σ) he.symm f hf
    (A.coordinateGate_control hlarge T.vertex T.offset z Prod.fst G.axialCut σ n q _ hW hinc f hf hc)
    I s x hx

end InitialCoverSystem.PatchAtlas

section CoordinateGerms

theorem coordinatePrimitive_interval {a : ℕ} (j : Fin 2) :
    coordinatePrimitive a j=coordinateInterval a j 0 (cutTau-1) := by
  apply Subtype.ext
  rw [← coordinateArc_tau]
  have hzero : coordinateShift j 0=0 := by fin_cases j <;> simp [coordinateShift]
  ext p
  simp only [coordinateInterval,coordinateBetween,sub_zero,hzero,neg_zero,translate_zero,
    Set.mem_preimage,coordinateArc,map_sub,map_one,Int.fract_sub_one]

theorem local_coordinate_formula {a : ℕ} (d : Fin 2) (u : CutRing × CutRing) (z : ℝ × ℝ) :
    ∃ k : ℤ, ∃ δ : ℝ, 0<δ ∧ ∀ p : GenericSquare a, dist p.val z<δ →
      (p ∈ (spatialTranslate u (coordinatePrimitive a d)).val ↔
        ordinary (pointCoordinate u d+(k:CutRing))≤realCoordinate p.val d ∧
        realCoordinate p.val d<ordinary (pointCoordinate u d+(k:CutRing)+(cutTau-1))) := by
  let l := pointCoordinate u d
  let h := pointCoordinate u d+(cutTau-1)
  have hp : ordinary l<ordinary h := by
    dsimp only [l,h]
    simp only [map_add,map_sub,map_one,ordinary_cutTau]
    linarith [Real.one_lt_goldenRatio]
  have hw : ordinary h-ordinary l<1 := by
    dsimp only [l,h]
    simp only [map_add,map_sub,map_one,ordinary_cutTau]
    linarith [Real.goldenRatio_lt_two]
  obtain ⟨k,hk⟩ := local_periodic_interval (a := a) d l h hp hw (realCoordinate z d)
  refine ⟨k,(1-(ordinary h-ordinary l))/4,by linarith,?_⟩
  intro p hnear
  have hsmall : |coordinate d p-realCoordinate z d|<(1-(ordinary h-ordinary l))/4 := by
    have hg := (max_lt_iff.mp (show max (dist p.val.1 z.1) (dist p.val.2 z.2) < _ by
      simpa only [Prod.dist_eq] using hnear))
    fin_cases d
    · simpa [coordinate,realCoordinate,Real.dist_eq] using hg.1
    · simpa [coordinate,realCoordinate,Real.dist_eq] using hg.2
  rw [coordinatePrimitive_interval,spatialTranslate_coordinateInterval]
  have he : 0+(if d=0 then u.1 else u.2)=l := by simp [l,pointCoordinate]
  have he' : cutTau-1+(if d=0 then u.1 else u.2)=h := by dsimp [h,pointCoordinate]; ring
  rw [he,he',hk p hsmall]
  have hcoord : coordinate d p=realCoordinate p.val d := by fin_cases d <;> rfl
  simp only [l,h,map_add,map_sub,map_intCast,map_one,hcoord]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

end CoordinateGerms

namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem coordinate_concurrent_action (hlarge : 20 ≤ m+1)
    (d : Fin 2) (v : CutRing × CutRing)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentCoordinates t u) i).val) V.val)
    (n : ℕ) (q : Fin 2 → ℤ) (W : polygonAlgebra a)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (coordinateWindowPrimitives n q) i).val) W.val)
    (he : spatialTranslate v (coordinatePrimitive a d) ⊓ W=V ⊓ W)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (x : BoundedRelationCover M (alternatingGenerator a r m hm)) (hx : x ∈ f.range) :
    A.primitiveStar (by omega) (coordinateTestIndex d,v) (universalMap (subtypeAlternatingHom I.val) s)*x*
      (A.primitiveStar (by omega) (coordinateTestIndex d,v) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u) V
      (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u) V
        (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  let P := translatedTemplate (initialPatchPrimitives r A.geometry.mesh) v
  let h := fun J (_ : J.card ≤ 15) b hb => A.initial v J b hb
  let R : Unit → Fin 5 × (CutRing × CutRing) := fun _ => (coordinateTestIndex d,v)
  let hR := fun J (_ : J.card ≤ 15) b hb =>
    B.coordinateFamilyLaw_all A.rectangles.rectangles (fun _ : Unit => d) (fun _ => v) J b hb
  have horig := B.fullGeometricSector_shared_primitive (by omega) P R (Sum.inl (coordinateTestIndex d)) ()
    (by simp [P,R,translatedTemplate,initialPatchPrimitives]) h hR
    (spatialTranslate v (coordinatePrimitive a d))
    (by intro y z hh; simpa only [P,primitiveTests,primitiveFamilyTests,translatedTemplate,
      initialPatchPrimitives,Sum.elim_inl,add_zero,initialTest_coordinate] using hh ())
  let J : Sum (Fin 2) (Fin 2 × Fin (A.geometry.window-1)) → Fin 2 := Sum.elim id Prod.fst
  let Z : Sum (Fin 2) (Fin 2 × Fin (A.geometry.window-1)) → CutRing × CutRing :=
    Sum.elim (fun k => u+A.geometry.anchors t (axisDirection k))
      (fun k => u+(coordinateWindowPrimitives A.geometry.window A.geometry.start k).2)
  let Q := fun i => (coordinateTestIndex (J i),Z i)
  let hQ := fun K (_ : K.card ≤ 15) b hb => B.coordinateFamilyLaw_all A.rectangles.rectangles J Z K b hb
  have hQe : Q=A.concurrentCoordinates t u := (A.concurrentCoordinates_eq t u).symm
  have hv : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) Q i).val) V.val := by
    rw [hQe]; exact hV
  have htarget := B.fullGeometricSector_subfamily (by omega) (A.concurrentPrimitives t u) Q
    A.concurrentCoordinateEmbedding (by rw [hQe]; rfl) (A.concurrentLaw t u) hQ V hv
  change B.fullGeometricSector (by omega) P h (spatialTranslate v (initialTest a r (coordinateTestIndex d)))
    (universalMap (subtypeAlternatingHom I.val) s)*x*
    (B.fullGeometricSector (by omega) P h (spatialTranslate v (initialTest a r (coordinateTestIndex d)))
      (universalMap (subtypeAlternatingHom I.val) s))⁻¹ = _
  rw [initialTest_coordinate,horig,← htarget]
  exact B.coordinate_charts_action hlarge A.rectangles.rectangles (fun _ : Unit => d) (fun _ => v)
    J Z _ V W (fun y z hh => by simpa only [primitiveTests,primitiveFamilyTests,initialTest_coordinate] using hh ())
    hv n q hW he f hf hc I s x hx

end InitialCoverSystem.PatchAtlas

end SimpleAmenable

end OAI
