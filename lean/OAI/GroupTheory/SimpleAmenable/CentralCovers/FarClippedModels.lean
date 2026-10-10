import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ClippedGerms
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FarClippingGeometry
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CoordinateModels
import OAI.GroupTheory.SimpleAmenable.CentralCovers.InitialGridActions
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveStarCoherence

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem far_grid_action_at_point (hlarge : 20 ≤ m+1)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (d : Fin 2) (v₀ : CutRing × CutRing)
    (cell : Fin 2 → Fin A.geometry.mesh)
    (n : ℕ) (q : Fin 2 → ℤ) (W : polygonAlgebra a)
    (hW : ResolvedBy (fun e => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) e).val) W.val)
    (hinitial : W ≤ spatialTranslate v₀ (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell))
    (p : GenericSquare a) (hp : p ∈ W.val)
    (hpclip : ∀ k, -ordinary r≤realCoordinate p.val k-ordinary (pointCoordinate v₀ k) ∧
      realCoordinate p.val k-ordinary (pointCoordinate v₀ k)<ordinary r)
    (hfar : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ)) <
      |cutForm a (slopeDirection d) p.val-ordinary (integralCutForm a (slopeDirection d) v₀)|)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (x : BoundedRelationCover M (alternatingGenerator a r m hm)) (hx : x ∈ f.range) :
    A.rectangles.slope (by omega) d v₀ (universalMap (subtypeAlternatingHom I.val) s)*x*
      (A.rectangles.slope (by omega) d v₀ (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    (if 0 ≤ cutForm a (slopeDirection d) p.val-ordinary (integralCutForm a (slopeDirection d) v₀)
      then B.c (subtypeAlternatingHom I.val (universalProjection _ s)) else 1)*x*
      (if 0 ≤ cutForm a (slopeDirection d) p.val-ordinary (integralCutForm a (slopeDirection d) v₀)
      then B.c (subtypeAlternatingHom I.val (universalProjection _ s)) else 1)⁻¹ := by
  let p' := translate a (-v₀) p
  let v : ℝ × ℝ := p.val-(ordinary v₀.1,ordinary v₀.2)
  have hp' : p' ∈ (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell).val := hinitial hp
  have hv : p'.val=(Int.fract v.1,Int.fract v.2) := by
    simp only [p',v,translate_val,Prod.fst_neg,Prod.snd_neg,map_neg,sub_eq_add_neg,Prod.fst_add,Prod.snd_add,Prod.fst_neg,Prod.snd_neg]
  have hvclip (k : Fin 2) : -ordinary r≤realCoordinate v k ∧ realCoordinate v k<ordinary r := by
    have h := hpclip k
    fin_cases k <;> exact h
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
  obtain ⟨k,hk,he⟩ := windowRectangle_clipping_chart_at_lift r A.geometry.mesh A.geometry.mesh_large
    (symmetricWindowStart r) cell hb hu p' hp' v hv hvclip
  have hform : cutForm a (slopeDirection d) (windowPlanarLift (symmetricWindowStart r) p')+
      cutForm a (slopeDirection d) ((k 0:ℝ),(k 1:ℝ))=
        cutForm a (slopeDirection d) p.val-ordinary (integralCutForm a (slopeDirection d) v₀) := by
    rw [← cutForm_add,he]
    dsimp only [v]
    rw [cutForm_sub,cutForm_ordinary]
  have hw := (windowRectangle_mem A.geometry.mesh A.geometry.mesh_large (symmetricWindowStart r) cell p').mp hp'
  have hact := A.far_grid_action hlarge hr d v₀ cell k hk
    (windowPlanarLift (symmetricWindowStart r) p') (fun k => ⟨(hw k).1,(hw k).2.le⟩)
    (by rw [hform]; exact hfar) n q W hW hinitial f hf hc I s x hx
  simpa only [hform] using hact

theorem far_clipped_model_action_neighborhood {ι : Type*} [Finite ι]
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
    (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4)
    (hfarline : ordinary A.rectangles.radius≤|cutForm a (slopeDirection d) z-ordinary (integralCutForm a (slopeDirection d) G.offset)|)
    (σ : Fin 2 × Bool → Bool) (hσ : ∀ k, σ (k,false)=false ∧ σ (k,true)=true)
    : ∃ δ : ℝ, 0<δ ∧ ∀ (cell : Fin 2 → Fin A.geometry.mesh)
    (n : ℕ) (q : Fin 2 → ℤ) (W : polygonAlgebra a),
    ResolvedBy (fun e => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) e).val) W.val →
    W ≤ A.geometry.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ →
    W ≤ spatialTranslate G.offset (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell) →
    ∀ p : GenericSquare a, p ∈ W.val → dist p.val z<δ →
    (∀ k, -ordinary r≤realCoordinate p.val k-ordinary (pointCoordinate G.offset k) ∧
      realCoordinate p.val k-ordinary (pointCoordinate G.offset k)<ordinary r) →
    ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
    B.AlignedSmallSupported f →
    SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q W) →
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
  obtain ⟨δ,hδ,hδspec⟩ := far_cut_neighborhood a (slopeDirection d) z
    (ordinary (integralCutForm a (slopeDirection d) G.offset)) (ordinary A.rectangles.radius)
    ((1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))) A.rectangles.radius_pos hmesh hfarline
  refine ⟨δ,hδ,?_⟩
  intro cell n q W hW hinc hinitial p hp hpδ hpclip f hf hc I s x hx
  have hfar := hδspec p.val hpδ
  have hact := A.far_grid_action_at_point hlarge hr d G.offset cell n q W hW hinitial
    p hp hpclip hfar.1 f hf hc I s x hx
  simp only [hfar.2] at hact
  have hperiod := A.primitiveStar_periodic (by omega) (slopeTestIndex d) u G.period
  change A.primitiveStar (by omega) (slopeTestIndex d,G.offset)=_ at hperiod
  rw [← hperiod,A.primitiveStar_slope]
  apply hact.trans
  symm
  have hinactive : cutForm a (slopeDirection d) z ≠ ordinary (integralCutForm a (slopeDirection d) G.offset) := by
    intro he
    rw [he,sub_self,abs_zero] at hfarline
    linarith [A.rectangles.radius_pos]
  let b : Bool := decide (ordinary (integralCutForm a (slopeDirection d) G.offset)<cutForm a (slopeDirection d) z)
  have hconst := B.cell_constant_action hlarge _ (A.concurrentLaw T.vertex T.offset) _ _
    (A.inward_model_resolved T _ ())
    (A.concurrent_coordinateGate_resolved T.vertex T.offset z Prod.fst G.axialCut σ) b
    (by rw [G.inactive_model_restrict_gate T hr hz₁ hz₂ lo hi slope hlo hhi hs hR hinactive σ];
        simp only [hσ,forall_const,true_and,b,decide_eq_true_eq]) f hf
    (A.coordinateGate_control hlarge T.vertex T.offset z Prod.fst G.axialCut σ n q _ hW hinc f hf hc) I s x hx
  simpa only [b,decide_eq_true_eq] using hconst

theorem interior_clipped_model_action_neighborhood {ι : Type*} [Finite ι]
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
    (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4)
    (σ : Fin 2 × Bool → Bool) (hσ : ∀ k, σ (k,false)=false ∧ σ (k,true)=true)
    : ∃ δ : ℝ, 0<δ ∧ ∀ L V : Fin 2 → CutRing,
    (∀ k, ordinary (L k) ≤ ordinary (V k)) →
    (∀ k, -ordinary r≤ordinary (L k)-ordinary (pointCoordinate G.offset k) ∧
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
  by_cases hactive : cutForm a (slopeDirection d) z=ordinary (integralCutForm a (slopeDirection d) G.offset)
  · refine ⟨A.geometry.epsilon/2,by linarith [A.geometry.positive],?_⟩
    intro L V hLV hclip hnear n q hW hinc cell hinitial p hp hpδ hpoint f hf hc I s x hx
    exact A.active_clipped_model_action hlarge hr d u z G T hz₁ hz₂ lo hi slope hlo hhi hs hR
      (by simpa only [hs.1,hs.2] using hactive) σ hσ L V hLV hclip hnear n q hW hinc f hf hc I s x hx
  by_cases hnearline : |cutForm a (slopeDirection d) z-ordinary (integralCutForm a (slopeDirection d) G.offset)|<ordinary A.rectangles.radius
  · obtain ⟨δ,hδ,hact⟩ := A.inactive_clipped_model_action_neighborhood hlarge hr d u z G T hz₁ hz₂
      lo hi slope hlo hhi hs hR hactive hnearline σ hσ
    refine ⟨δ,hδ,?_⟩
    intro L V hLV hclip hnear n q hW hinc cell hinitial p hp hpδ hpoint f hf hc I s x hx
    exact hact L V hLV hclip hnear n q hW hinc f hf hc I s x hx
  · obtain ⟨δ,hδ,hact⟩ := A.far_clipped_model_action_neighborhood hlarge hr d u z G T hz₁ hz₂
      lo hi slope hlo hhi hs hR hmesh (le_of_not_gt hnearline) σ hσ
    refine ⟨δ,hδ,?_⟩
    intro L V hLV hclip hnear n q hW hinc cell hinitial p hp hpδ hpoint f hf hc I s x hx
    apply hact cell n q _ hW hinc hinitial p hp hpδ ?_ f hf hc I s x hx
    intro k
    constructor <;> linarith [(hclip k).1,(hclip k).2,(hpoint k).1,(hpoint k).2]

end InitialCoverSystem.PatchAtlas

end SimpleAmenable

end OAI
