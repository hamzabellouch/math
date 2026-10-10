import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalLaws
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PhaseClippedModels
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CoordinateModels
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.LocalClippedBoxFormula
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.RefinedLocalDecisions

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem refined_clipped_model_action_neighborhood {ι : Type*} [Finite ι]
    (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (d : Fin 2) (u : CutRing × CutRing) (z : ℝ × ℝ)
    (G : ClippedGerm a r (slopeDirection d) u z) (hbox : G.BoxValid)
    {j : ι → Fin 4} {c : ι → CutRing} (T : A.geometry.InwardChart j c z)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (lo hi : Fin 2 → ι) (slope : ι)
    (hlo : ∀ k, j (lo k)=axisDirection k ∧ c (lo k)=pointCoordinate G.offset k-r)
    (hhi : ∀ k, j (hi k)=axisDirection k ∧ c (hi k)=pointCoordinate G.offset k+r)
    (hs : j slope=slopeDirection d ∧ c slope=integralCutForm a (slopeDirection d) G.offset)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i))
      (spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))).val)
    (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4)
    : ∃ δ : ℝ, 0<δ ∧ ∀ (N : ℕ) (e : Fin (N+1) → CutRing),
    StrictMono (fun i => ordinary (e i)) → e 0=0 → e (Fin.last N)=1 →
    (∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1) →
    (∀ k, cutFraction (pointCoordinate G.offset k-r) ∈ Set.range e) →
    (∀ k, cutFraction (pointCoordinate G.offset k+r) ∈ Set.range e) →
    ∀ cell : Fin 2 → Fin N,
    (∀ k, |ordinary (e (cell k).castSucc)-realCoordinate z k|<δ ∧
      |ordinary (e (cell k).succ)-realCoordinate z k|<δ) →
    ∀ (n : ℕ) (q : Fin 2 → ℤ),
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) (refinedGridRectangle a N e cell).val →
    ∀ initial : Fin 2 → Fin A.geometry.mesh,
    refinedGridRectangle a N e cell ≤ spatialTranslate G.offset
      (windowRectangle a A.geometry.mesh (symmetricWindowStart r) initial) →
    ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
    B.AlignedSmallSupported f →
    SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q
      (refinedGridRectangle a N e cell)) →
    ∀ (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)),
    ∀ x ∈ f.range,
    A.primitiveStar (by omega) (slopeTestIndex d,u) (universalMap (subtypeAlternatingHom I.val) s)*x*
      (A.primitiveStar (by omega) (slopeTestIndex d,u) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
      (T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))) ())
        (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
        (T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))) ())
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  obtain ⟨δ₀,hδ₀,hdecisions⟩ := T.refined_cells_locally_decided hr
  obtain ⟨δ₁,hδ₁,hact⟩ := A.uniform_clipped_model_action_neighborhood hlarge hr d u z G hbox T hz₁ hz₂
    lo hi slope hlo hhi hs hR hmesh
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro N e he hzero hlast hmesh' hlor hhir cell hnear n q hW initial hinitial f hf hc I s x hx
  have hnear₀ k := And.intro ((hnear k).1.trans_le (min_le_left δ₀ δ₁))
    ((hnear k).2.trans_le (min_le_left δ₀ δ₁))
  have hnear₁ k := And.intro ((hnear k).1.trans_le (min_le_right δ₀ δ₁))
    ((hnear k).2.trans_le (min_le_right δ₀ δ₁))
  have hlocal := hdecisions N e he hzero hlast hmesh' cell hnear₀
  let idx (k : Fin 2 × Bool) : ι := if k.2 then hi k.1 else lo k.1
  have hidx (k : Fin 2 × Bool) : j (idx k)=axisDirection k.1 ∧ c (idx k)=G.axialCut k := by
    obtain ⟨k,b⟩ := k
    cases b
    · exact hlo k
    · exact hhi k
  have hends (k : Fin 2 × Bool) : cutFraction (G.axialCut k) ∈ Set.range e := by
    obtain ⟨k,b⟩ := k
    cases b
    · exact hlor k
    · exact hhir k
  obtain ⟨σ,hgate⟩ := T.refined_coordinate_phase e he hzero hlast hmesh' cell Prod.fst G.axialCut idx hidx hends hlocal
  obtain ⟨p,hp⟩ := refinedGridRectangle_nonempty e he hzero hlast hmesh' cell
  apply hact σ (fun k => e (cell k).castSucc) (fun k => e (cell k).succ)
    (fun k => (he (Fin.castSucc_lt_succ (i := cell k))).le) ?_ hnear₁ n q hW hgate initial hinitial p hp
    (refinedGridRectangle_point_near e he hzero hlast hmesh' cell z δ₁ hnear₁ p hp)
    ((refinedGridRectangle_mem e he hzero hlast hmesh' cell p).mp hp) f hf hc I s x hx
  intro hσ
  exact T.refined_interior_phase_bounds e he hzero hlast hmesh' cell G.offset lo hi hlo hhi hlor hhir σ hσ
    hgate (fun p hp => (hlocal p hp).2)

end InitialCoverSystem.PatchAtlas

section PrimitiveGerms

inductive PrimitiveGerm (a : ℕ) (r : CutRing) (z : ℝ × ℝ) :
    Fin 5 × (CutRing × CutRing) → Type
  | constant (u : CutRing × CutRing) : PrimitiveGerm a r z (0,u)
  | coordinate (d : Fin 2) (u : CutRing × CutRing) (g : CoordinateGerm a d u z) :
      PrimitiveGerm a r z (coordinateTestIndex d,u)
  | slope (d : Fin 2) (u : CutRing × CutRing)
      (g : ClippedGerm a r (slopeDirection d) u z) (box : g.BoxValid) :
      PrimitiveGerm a r z (slopeTestIndex d,u)

namespace PrimitiveGerm
variable {a : ℕ} {r : CutRing} {z : ℝ × ℝ} {p : Fin 5 × (CutRing × CutRing)}

theorem nonempty (hr : 0<ordinary r ∧ ordinary r<1/2) (p : Fin 5 × (CutRing × CutRing)) :
    Nonempty (PrimitiveGerm a r z p) := by
  obtain ⟨j,u⟩ := p
  fin_cases j
  · exact ⟨.constant u⟩
  · obtain ⟨g⟩ := coordinateGerm_nonempty (a := a) 0 u z
    exact ⟨.coordinate 0 u g⟩
  · obtain ⟨g⟩ := coordinateGerm_nonempty (a := a) 1 u z
    exact ⟨.coordinate 1 u g⟩
  · obtain ⟨g,hg⟩ := clippedGerm_exists_box_valid (a := a) r (slopeDirection 0) hr u z
    exact ⟨.slope 0 u g hg⟩
  · obtain ⟨g,hg⟩ := clippedGerm_exists_box_valid (a := a) r (slopeDirection 1) hr u z
    exact ⟨.slope 1 u g hg⟩

def Index : PrimitiveGerm a r z p → Type
  | .constant _ => Unit
  | .coordinate _ _ _ => Bool
  | .slope _ _ _ _ => Sum (Fin 2 × Bool) Unit

instance (G : PrimitiveGerm a r z p) : Finite G.Index := by
  cases G <;> dsimp only [Index] <;> infer_instance

noncomputable def cuts (G : PrimitiveGerm a r z p) : G.Index → Fin 4 × CutRing := by
  cases G with
  | constant u => exact fun _ => (0,0)
  | coordinate d u g => exact fun b : Bool => (axisDirection d,if b then g.upper else g.lower)
  | slope d u g box =>
    exact Sum.elim
      (fun k : Fin 2 × Bool => (axisDirection k.1,if k.2 then pointCoordinate g.offset k.1+r else pointCoordinate g.offset k.1-r))
      (fun _ => (slopeDirection d,integralCutForm a (slopeDirection d) g.offset))

noncomputable def oldOffset : PrimitiveGerm a r z p → CutRing × CutRing
  | .constant _ => 0
  | .coordinate _ _ _ => 0
  | .slope _ _ g _ => g.offset

end PrimitiveGerm
end PrimitiveGerms

namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem constant_model_action {ι : Type*} [Finite ι]
    (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ}
    (T : A.geometry.InwardChart j c z)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (u : CutRing × CutRing)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.fullGeometricSector (by omega)
      (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
      (A.geometry.inwardMargin T.vertex T.offset z)))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (x : BoundedRelationCover M (alternatingGenerator a r m hm)) (hx : x ∈ f.range) :
    A.primitiveStar (by omega) (0,u) (universalMap (subtypeAlternatingHom I.val) s)*x*
      (A.primitiveStar (by omega) (0,u) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
      (T.polygons (fun _ : Unit => spatialTranslate u (initialTest a r 0)) ())
        (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
        (T.polygons (fun _ : Unit => spatialTranslate u (initialTest a r 0)) ())
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  let R : Unit → polygonAlgebra a := fun _ => spatialTranslate u (initialTest a r 0)
  have hR : R ()=wholePolygon a := by simp [R,initialTest]
  have hresolve : ResolvedBy (fun i => halfPlane a (j i) (c i)) (R ()).val := by
    rw [hR]; exact fun _ _ _ => Iff.rfl
  have he : wholePolygon a ⊓ A.geometry.inwardMargin T.vertex T.offset z =
      T.polygons R () ⊓ A.geometry.inwardMargin T.vertex T.offset z := by
    apply Subtype.ext
    ext p
    change (True ∧ _) ↔ (_ ∧ _)
    by_cases hp : p ∈ (A.geometry.inwardMargin T.vertex T.offset z).val
    · obtain ⟨q,_,hh⟩ := T.polygons_assignment_realized hr hz₁ hz₂ R (fun _ => hresolve)
        p hp Set.univ isOpen_univ (Set.mem_univ z)
      have hval : p ∈ (T.polygons R ()).val := by
        have hq : q ∈ (R ()).val := by rw [hR]; trivial
        exact (show q ∈ (R ()).val ↔ p ∈ (T.polygons R ()).val by
          simpa only [polygonAssignment,decide_eq_true_eq] using Bool.eq_iff_iff.mp (congrFun hh ())).mp hq
      simp only [hp,hval]
    · simp only [hp,and_false]
  have hpstar : A.primitiveStar (by omega) (0,u)=
      B.c.comp (universalProjection (alternatingGroup (Fin (m+1)))) := by
    unfold primitiveStar
    have hu : spatialTranslate u (initialTest a r 0)=wholePolygon a := hR
    rw [hu,B.fullGeometricSector_whole]
  rw [hpstar]
  have hh := B.chart_action_transfer hlarge (A.concurrentPrimitives T.vertex T.offset)
    (A.concurrentLaw T.vertex T.offset) (wholePolygon a) (T.polygons R ())
    (A.geometry.inwardMargin T.vertex T.offset z) (fun _ _ _ => Iff.rfl)
    (A.inward_model_resolved T R ()) (A.concurrent_inward_resolved T.vertex T.offset z) he f hf hc I s x hx
  rw [B.fullGeometricSector_whole] at hh
  exact hh

end InitialCoverSystem.PatchAtlas

end SimpleAmenable

end OAI
