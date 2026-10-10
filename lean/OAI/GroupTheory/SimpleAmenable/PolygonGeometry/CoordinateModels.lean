import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ActiveClippedModelActions

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section CoordinateModels

structure CoordinateGerm (a : ℕ) (d : Fin 2) (u : CutRing × CutRing) (z : ℝ × ℝ) where
  period : ℤ
  radius : ℝ
  radius_pos : 0<radius
  valid : ∀ p : GenericSquare a, dist p.val z<radius →
    (p ∈ (spatialTranslate u (coordinatePrimitive a d)).val ↔
      ordinary (pointCoordinate u d+(period:CutRing))≤realCoordinate p.val d ∧
      realCoordinate p.val d<ordinary (pointCoordinate u d+(period:CutRing)+(cutTau-1)))

theorem coordinateGerm_nonempty {a : ℕ} (d : Fin 2) (u : CutRing × CutRing) (z : ℝ × ℝ) :
    Nonempty (CoordinateGerm a d u z) := by
  obtain ⟨k,δ,hδ,h⟩ := local_coordinate_formula (a := a) d u z
  exact ⟨⟨k,δ,hδ,h⟩⟩

namespace CoordinateGerm
variable {a : ℕ} {d : Fin 2} {u : CutRing × CutRing} {z : ℝ × ℝ} (G : CoordinateGerm a d u z)
noncomputable def lower : CutRing := pointCoordinate u d+(G.period:CutRing)
noncomputable def upper : CutRing := G.lower+(cutTau-1)

theorem model_formula {r : CutRing} {ι : Type*} [Finite ι] {C : ConcurrentGeometry a r}
    {j : ι → Fin 4} {c : ι → CutRing} (T : C.InwardChart j c z)
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (lo hi : ι) (hlo : j lo=axisDirection d ∧ c lo=G.lower)
    (hhi : j hi=axisDirection d ∧ c hi=G.upper)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i)) (spatialTranslate u (coordinatePrimitive a d)).val)
    (p : GenericSquare a) (hp : p ∈ (C.inwardMargin T.vertex T.offset z).val) :
    p ∈ (T.polygons (fun _ : Unit => spatialTranslate u (coordinatePrimitive a d)) ()).val ↔
      p ∉ (C.localDecision T.vertex T.offset z (j lo) (c lo)).val ∧
      p ∈ (C.localDecision T.vertex T.offset z (j hi) (c hi)).val := by
  obtain ⟨q,hq,he⟩ := T.assignment_realized hr hz₁ hz₂ p hp
    (Metric.ball z G.radius) Metric.isOpen_ball (Metric.mem_ball_self G.radius_pos)
  have hd (i : ι) : q ∈ (cutPolygon a (j i) (c i)).val ↔
      p ∈ (C.localDecision T.vertex T.offset z (j i) (c i)).val := by
    simpa only [polygonAssignment,decide_eq_true_eq] using Bool.eq_iff_iff.mp (congrFun he i)
  have hmodel : p ∈ (T.polygons (fun _ : Unit => spatialTranslate u (coordinatePrimitive a d)) ()).val ↔
      q ∈ (spatialTranslate u (coordinatePrimitive a d)).val := by
    change polygonAssignment (fun i => C.localDecision T.vertex T.offset z (j i) (c i)) p ∈
      polygonFormalMask (fun i => cutPolygon a (j i) (c i)) _ ↔ _
    rw [← he]
    exact polygonFormalMask_mem _ _ hR q
  rw [hmodel,G.valid q hq]
  apply and_congr
  · simpa only [cutPolygon,halfPlane,Set.mem_ofPred_eq,hlo.1,hlo.2,cutForm_axis,not_lt,lower]
      using not_congr (hd lo)
  · simpa only [cutPolygon,halfPlane,Set.mem_ofPred_eq,hhi.1,hhi.2,cutForm_axis,upper,lower]
      using hd hi

end CoordinateGerm

namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem coordinate_model_action_neighborhood {ι : Type*} [Finite ι]
    (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (d : Fin 2) (u : CutRing × CutRing) (z : ℝ × ℝ) (G : CoordinateGerm a d u z)
    {j : ι → Fin 4} {c : ι → CutRing} (T : A.geometry.InwardChart j c z)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (lo hi : ι) (hlo : j lo=axisDirection d ∧ c lo=G.lower)
    (hhi : j hi=axisDirection d ∧ c hi=G.upper)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i)) (spatialTranslate u (coordinatePrimitive a d)).val) :
    ∃ N : Set (ℝ × ℝ), IsOpen N ∧ z ∈ N ∧
      ∀ n q (W : polygonAlgebra a),
      ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (coordinateWindowPrimitives n q) i).val) W.val →
      (∀ p : GenericSquare a, p ∈ W.val → p.val ∈ N) →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q W) →
      ∀ (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)),
      ∀ x ∈ f.range,
      A.primitiveStar (by omega) (coordinateTestIndex d,u) (universalMap (subtypeAlternatingHom I.val) s)*x*
        (A.primitiveStar (by omega) (coordinateTestIndex d,u) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
        (T.polygons (fun _ : Unit => spatialTranslate u (coordinatePrimitive a d)) ())
          (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
          (T.polygons (fun _ : Unit => spatialTranslate u (coordinatePrimitive a d)) ())
            (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  let R : Unit → polygonAlgebra a := fun _ => spatialTranslate u (coordinatePrimitive a d)
  obtain ⟨N,hN,hz,hlocal⟩ := T.polygons_locally_eq hr R (fun _ => hR)
  let V : polygonAlgebra a := (A.geometry.localDecision T.vertex T.offset z (j lo) (c lo))ᶜ ⊓
    A.geometry.localDecision T.vertex T.offset z (j hi) (c hi)
  have hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (A.concurrentCoordinates T.vertex T.offset) i).val) V.val := by
    intro p q hh
    apply and_congr
    · exact not_congr (by simpa only [hlo.1] using
        A.coordinate_localDecision_resolved T.vertex T.offset z d (c lo) p q hh)
    · simpa only [hhi.1] using A.coordinate_localDecision_resolved T.vertex T.offset z d (c hi) p q hh
  have he (p : GenericSquare a) (hp : p ∈ (A.geometry.inwardMargin T.vertex T.offset z).val) :
      p ∈ (T.polygons R ()).val ↔ p ∈ V.val :=
    G.model_formula T hr hz₁ hz₂ lo hi hlo hhi hR p hp
  have hrestrict : V ⊓ A.geometry.inwardMargin T.vertex T.offset z=
      T.polygons R () ⊓ A.geometry.inwardMargin T.vertex T.offset z := by
    apply Subtype.ext
    ext p
    change (_ ∧ _) ↔ (_ ∧ _)
    by_cases hp : p ∈ (A.geometry.inwardMargin T.vertex T.offset z).val
    · simp only [hp,and_true,he p hp]
    · simp only [hp,and_false]
  refine ⟨N,hN,hz,?_⟩
  intro n q W hW hWN f hf hc I s x hx
  have hinc : W ≤ A.geometry.inwardMargin T.vertex T.offset z := fun p hp => (hlocal p (hWN p hp)).1
  have heW : spatialTranslate u (coordinatePrimitive a d) ⊓ W=V ⊓ W := by
    apply Subtype.ext
    ext p
    change (_ ∧ _) ↔ (_ ∧ _)
    by_cases hp : p ∈ W.val
    · have hh := (hlocal p (hWN p hp)).2 ()
      simpa only [hp,and_true] using hh.symm.trans (he p (hinc hp))
    · simp only [hp,and_false]
  apply (A.coordinate_concurrent_action hlarge d u T.vertex T.offset V hV n q W hW heW f hf hc I s x hx).trans
  exact B.chart_action_transfer hlarge _ (A.concurrentLaw T.vertex T.offset) V (T.polygons R ()) _
    (fun p q hh => hV p q (fun i => hh (A.concurrentCoordinateEmbedding i)))
    (A.inward_model_resolved T R ()) (A.concurrent_inward_resolved T.vertex T.offset z) hrestrict f hf
    (A.coordinate_control_inward_gate hlarge T.vertex T.offset _ (A.coordinate_inward_resolved T.vertex T.offset z)
      n q W hW hinc f hf hc) I s x hx

end InitialCoverSystem.PatchAtlas
end CoordinateModels

namespace ClippedGerm
variable {a : ℕ} {r : CutRing} {slope : Fin 4} {u : CutRing × CutRing} {z : ℝ × ℝ}
    (G : ClippedGerm a r slope u z)

theorem inactive_model_restrict_gate {ι : Type*} [Finite ι] {C : ConcurrentGeometry a r}
    {j : ι → Fin 4} {c : ι → CutRing}
    (T : C.InwardChart j c z) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (lo hi : Fin 2 → ι) (s : ι)
    (hlo : ∀ d, j (lo d)=axisDirection d ∧ c (lo d)=pointCoordinate G.offset d-r)
    (hhi : ∀ d, j (hi d)=axisDirection d ∧ c (hi d)=pointCoordinate G.offset d+r)
    (hs : j s=slope ∧ c s=integralCutForm a slope G.offset)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i))
      (spatialTranslate u (clippedSlopePrimitive a r slope)).val)
    (hinactive : cutForm a slope z ≠ ordinary (integralCutForm a slope G.offset))
    (σ : Fin 2 × Bool → Bool) :
    T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r slope)) () ⊓
      C.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ =
    if (∀ d, σ (d,false)=false ∧ σ (d,true)=true) ∧
        ordinary (integralCutForm a slope G.offset)<cutForm a slope z then
      C.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ else ⊥ := by
  classical
  rw [G.model_restrict_gate T hr hz₁ hz₂ lo hi s hlo hhi hs hR σ]
  by_cases hσ : ∀ d, σ (d,false)=false ∧ σ (d,true)=true
  · simp only [hσ,forall_const,true_and,ConcurrentGeometry.localDecision,hs.1,hs.2,ite_eq_right hinactive]
    by_cases h : cutForm a slope z < ordinary (integralCutForm a slope G.offset)
    · simp only [ite_eq_left h,ite_eq_right (not_lt_of_gt h)]
      change (⊤ : polygonAlgebra a)ᶜ ⊓ _ = ⊥
      simp only [compl_top,bot_inf_eq]
    · have hgt := lt_of_le_of_ne (le_of_not_gt h) hinactive.symm
      simp only [ite_eq_right h,ite_eq_left hgt]
      change (⊥ : polygonAlgebra a)ᶜ ⊓ _ = _
      simp only [compl_bot,top_inf_eq]
  · simp only [hσ,false_and,↓reduceIte,bot_inf_eq]

end ClippedGerm

namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem inactive_clipped_model_action_neighborhood {ι : Type*} [Finite ι]
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
    (hinactive : cutForm a (slopeDirection d) z ≠ ordinary (integralCutForm a (slopeDirection d) G.offset))
    (hnearline : |cutForm a (slopeDirection d) z-ordinary (integralCutForm a (slopeDirection d) G.offset)|<ordinary A.rectangles.radius)
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
  obtain ⟨δ,hδ,b,hb,h⟩ := A.rectangles.inactive_near_action_neighborhood hlarge hr d G.offset z hinactive hnearline
  refine ⟨δ,hδ,?_⟩
  intro L V hLV hclip hnear n q hW hinc f hf hc I s x hx
  have hperiod := A.primitiveStar_periodic (by omega) (slopeTestIndex d) u G.period
  change A.primitiveStar (by omega) (slopeTestIndex d,G.offset)=_ at hperiod
  rw [← hperiod,A.primitiveStar_slope]
  apply (h L V hLV hclip hnear n q hW f hf hc I s x hx).trans
  symm
  apply B.cell_constant_action hlarge _ (A.concurrentLaw T.vertex T.offset) _ _
    (A.inward_model_resolved T _ ())
    (A.concurrent_coordinateGate_resolved T.vertex T.offset z Prod.fst G.axialCut σ) b ?_ f hf
    (A.coordinateGate_control hlarge T.vertex T.offset z Prod.fst G.axialCut σ n q _ hW hinc f hf hc) I s x hx
  rw [G.inactive_model_restrict_gate T hr hz₁ hz₂ lo hi slope hlo hhi hs hR hinactive σ]
  simp only [hσ,forall_const,true_and,← hb]

end InitialCoverSystem.PatchAtlas

end SimpleAmenable

end OAI
