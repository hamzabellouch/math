import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ExteriorClippedModels
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FarClippedModels
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalLaws
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ClippedGerms
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ExteriorPhaseGeometry

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem phase_clipped_model_action_neighborhood {ι : Type*} [Finite ι]
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
    (σ : Fin 2 × Bool → Bool)
    : ∃ δ : ℝ, 0<δ ∧ ∀ L V : Fin 2 → CutRing,
    (∀ k, ordinary (L k) ≤ ordinary (V k)) →
    ((∀ k, σ (k,false)=false ∧ σ (k,true)=true) →
      ∀ k, -ordinary r≤ordinary (L k)-ordinary (pointCoordinate G.offset k) ∧
      ordinary (V k)-ordinary (pointCoordinate G.offset k)≤ordinary r) →
    (∀ k, |ordinary (L k)-realCoordinate z k|<δ ∧
      |ordinary (V k)-realCoordinate z k|<δ) →
    ∀ (n : ℕ) (q : Fin 2 → ℤ),
    (ResolvedBy (fun e => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) e).val) (coordinateRectangle a L V).val) →
    (coordinateRectangle a L V ≤
      A.geometry.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ) →
    ∀ (cell : Fin 2 → Fin A.geometry.mesh),
    (coordinateRectangle a L V ≤ spatialTranslate G.offset
      (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell)) →
    ∀ p : GenericSquare a, p ∈ (coordinateRectangle a L V).val → dist p.val z<δ →
    (∀ k, ordinary (L k)≤realCoordinate p.val k ∧ realCoordinate p.val k<ordinary (V k)) →
    ∀ (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm)),
    B.AlignedSmallSupported f →
    (SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q
      (coordinateRectangle a L V))) →
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
  by_cases hσ : ∀ k, σ (k,false)=false ∧ σ (k,true)=true
  · obtain ⟨δ,hδ,hact⟩ := A.interior_clipped_model_action_neighborhood hlarge hr d u z G T hz₁ hz₂
      lo hi slope hlo hhi hs hR hmesh σ hσ
    refine ⟨δ,hδ,?_⟩
    intro L V hLV hclip hnear n q hW hinc cell hinitial p hp hpδ hpoint f hf hc I s x hx
    exact hact L V hLV (hclip hσ) hnear n q hW hinc cell hinitial p hp hpδ hpoint f hf hc I s x hx
  · obtain ⟨O,hO,hz,hlocal⟩ := T.decisions_locally_eq hr
    obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hO z hz
    refine ⟨min δ G.radius,lt_min hδ G.radius_pos,?_⟩
    intro L V hLV hclip hnear n q hW hinc cell hinitial p hp hpδ hpoint f hf hc I s x hx
    have hperiod (P : polygonAlgebra a) : spatialTranslate G.offset P=spatialTranslate u P := by
      change spatialTranslate (u+((G.period 0:CutRing),(G.period 1:CutRing))) P=_
      rw [spatialTranslate_add,spatialTranslate_integral]
    have hinitial' : coordinateRectangle a L V≤ spatialTranslate u
        (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell) := by
      simpa only [hperiod] using hinitial
    have hb (k : Fin 2) : symmetricWindowStart r k≤endpointLabel (-r) ∧
        endpointLabel (-r)<symmetricWindowStart r k+A.geometry.mesh := by
      have hh := (symmetricWindow_labels r k).1
      have hclip := A.geometry.clipping
      constructor
      · exact hh.1
      · omega
    have hu (k : Fin 2) : symmetricWindowStart r k≤endpointLabel r ∧
        endpointLabel r<symmetricWindowStart r k+A.geometry.mesh := by
      have hh := (symmetricWindow_labels r k).2.2
      have hclip := A.geometry.clipping
      constructor
      · exact hh.1
      · omega
    have hout := G.exterior_old_cell T hr hbox lo hi hlo hhi σ hσ p (hinc hp)
      (hpδ.trans_le (min_le_right _ _))
      (hlocal p (hball (hpδ.trans_le (min_le_left _ _)))).2
      A.geometry.mesh A.geometry.mesh_large (symmetricWindowStart r) cell hb hu (hinitial' hp)
    exact A.exterior_clipped_model_action hlarge hr d u z G T hz₁ hz₂ lo hi slope hlo hhi hs hR
      σ hσ cell hout n q (coordinateRectangle a L V) hW hinc hinitial' f hf hc I s x hx

theorem uniform_clipped_model_action_neighborhood {ι : Type*} [Finite ι]
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
    : ∃ δ : ℝ, 0<δ ∧ ∀ σ : Fin 2 × Bool → Bool, ∀ L V : Fin 2 → CutRing,
    (∀ k, ordinary (L k) ≤ ordinary (V k)) →
    ((∀ k, σ (k,false)=false ∧ σ (k,true)=true) →
      ∀ k, -ordinary r≤ordinary (L k)-ordinary (pointCoordinate G.offset k) ∧
      ordinary (V k)-ordinary (pointCoordinate G.offset k)≤ordinary r) →
    (∀ k, |ordinary (L k)-realCoordinate z k|<δ ∧
      |ordinary (V k)-realCoordinate z k|<δ) →
    ∀ (n : ℕ) (q : Fin 2 → ℤ),
    (ResolvedBy (fun e => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) e).val) (coordinateRectangle a L V).val) →
    (coordinateRectangle a L V ≤
      A.geometry.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ) →
    ∀ (cell : Fin 2 → Fin A.geometry.mesh),
    (coordinateRectangle a L V ≤ spatialTranslate G.offset
      (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell)) →
    ∀ p : GenericSquare a, p ∈ (coordinateRectangle a L V).val → dist p.val z<δ →
    (∀ k, ordinary (L k)≤realCoordinate p.val k ∧ realCoordinate p.val k<ordinary (V k)) →
    ∀ (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm)),
    B.AlignedSmallSupported f →
    (SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q
      (coordinateRectangle a L V))) →
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
  classical
  have hall σ := A.phase_clipped_model_action_neighborhood hlarge hr d u z G hbox T hz₁ hz₂
    lo hi slope hlo hhi hs hR hmesh σ
  choose δ hδ hact using hall
  obtain ⟨σ₀,_,hmin⟩ := Finset.univ.exists_min_image δ
    (show (Finset.univ : Finset (Fin 2 × Bool → Bool)).Nonempty from Finset.univ_nonempty)
  refine ⟨δ σ₀,hδ σ₀,?_⟩
  intro σ L V hLV hclip hnear n q hW hinc cell hinitial p hp hpδ hpoint f hf hc I s x hx
  have hb : δ σ₀≤δ σ := hmin σ (Finset.mem_univ σ)
  exact hact σ L V hLV hclip (fun k => ⟨(hnear k).1.trans_le hb,(hnear k).2.trans_le hb⟩)
    n q hW hinc cell hinitial p hp (hpδ.trans_le hb) hpoint f hf hc I s x hx

end InitialCoverSystem.PatchAtlas

end SimpleAmenable

end OAI
