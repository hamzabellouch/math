import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ConcurrentCoordinateGates
import OAI.GroupTheory.SimpleAmenable.Homology.InwardTemplateResolutions
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.InwardGermTransport

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section ClippedGerms

structure ClippedGerm (a : ℕ) (r : CutRing) (j : Fin 4)
    (u : CutRing × CutRing) (z : ℝ × ℝ) where
  period : Fin 2 → ℤ
  radius : ℝ
  radius_pos : 0<radius
  valid : let v := u+((period 0:CutRing),(period 1:CutRing))
    ∀ p : GenericSquare a, dist p.val z<radius →
      (p ∈ (spatialTranslate u (clippedSlopePrimitive a r j)).val ↔
        (∀ d, ordinary (pointCoordinate v d-r)≤realCoordinate p.val d ∧
          realCoordinate p.val d<ordinary (pointCoordinate v d+r)) ∧
        ordinary (integralCutForm a j v)≤cutForm a j p.val)

theorem clippedGerm_nonempty {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (u : CutRing × CutRing) (z : ℝ × ℝ) :
    Nonempty (ClippedGerm a r j u z) := by
  obtain ⟨k,δ,hδ,h⟩ := local_clipped_formula r j hr u z
  exact ⟨⟨k,δ,hδ,h⟩⟩

namespace ClippedGerm
variable {a : ℕ} {r : CutRing} {slope : Fin 4} {u : CutRing × CutRing} {z : ℝ × ℝ}
    (G : ClippedGerm a r slope u z)

def offset : CutRing × CutRing := u+((G.period 0:CutRing),(G.period 1:CutRing))

theorem model_formula {ι : Type*} [Finite ι] {C : ConcurrentGeometry a r}
    {j : ι → Fin 4} {c : ι → CutRing}
    (T : C.InwardChart j c z) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (lo hi : Fin 2 → ι) (s : ι)
    (hlo : ∀ d, j (lo d)=axisDirection d ∧ c (lo d)=pointCoordinate G.offset d-r)
    (hhi : ∀ d, j (hi d)=axisDirection d ∧ c (hi d)=pointCoordinate G.offset d+r)
    (hs : j s=slope ∧ c s=integralCutForm a slope G.offset)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i))
      (spatialTranslate u (clippedSlopePrimitive a r slope)).val)
    (p : GenericSquare a) (hp : p ∈ (C.inwardMargin T.vertex T.offset z).val) :
    p ∈ (T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r slope)) ()).val ↔
      (∀ d, p ∉ (C.localDecision T.vertex T.offset z (j (lo d)) (c (lo d))).val ∧
        p ∈ (C.localDecision T.vertex T.offset z (j (hi d)) (c (hi d))).val) ∧
      p ∉ (C.localDecision T.vertex T.offset z (j s) (c s)).val := by
  obtain ⟨q,hq,he⟩ := T.assignment_realized hr hz₁ hz₂ p hp
    (Metric.ball z G.radius) Metric.isOpen_ball (Metric.mem_ball_self G.radius_pos)
  have hd (i : ι) : q ∈ (cutPolygon a (j i) (c i)).val ↔
      p ∈ (C.localDecision T.vertex T.offset z (j i) (c i)).val := by
    simpa only [polygonAssignment,decide_eq_true_eq] using Bool.eq_iff_iff.mp (congrFun he i)
  have hmodel : p ∈ (T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r slope)) ()).val ↔
      q ∈ (spatialTranslate u (clippedSlopePrimitive a r slope)).val := by
    change polygonAssignment (fun i => C.localDecision T.vertex T.offset z (j i) (c i)) p ∈
      polygonFormalMask (fun i => cutPolygon a (j i) (c i)) _ ↔ _
    rw [← he]
    exact polygonFormalMask_mem _ _ hR q
  rw [hmodel,G.valid q hq]
  apply and_congr
  · apply forall_congr'
    intro d
    apply and_congr
    · simpa only [cutPolygon,halfPlane,Set.mem_ofPred_eq,(hlo d).1,(hlo d).2,cutForm_axis,not_lt,offset]
        using not_congr (hd (lo d))
    · simpa only [cutPolygon,halfPlane,Set.mem_ofPred_eq,(hhi d).1,(hhi d).2,cutForm_axis,offset]
        using hd (hi d)
  · simpa only [cutPolygon,halfPlane,Set.mem_ofPred_eq,hs.1,hs.2,not_lt,offset] using not_congr (hd s)

end ClippedGerm
end ClippedGerms

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r) {κ : Type*} [Finite κ]

noncomputable def coordinateGate (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) (j : κ → Fin 2) (c : κ → CutRing) (σ : κ → Bool) : polygonAlgebra a :=
  C.inwardMargin t u z ⊓ polygonBooleanPullback
    (fun i => C.localDecision t u z (axisDirection (j i)) (c i)) {σ}

theorem coordinateGate_mem (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) (j : κ → Fin 2) (c : κ → CutRing) (σ : κ → Bool)
    (p : GenericSquare a) :
    p ∈ (C.coordinateGate t u z j c σ).val ↔ p ∈ (C.inwardMargin t u z).val ∧
      polygonAssignment (fun i => C.localDecision t u z (axisDirection (j i)) (c i)) p=σ := Iff.rfl

end ConcurrentGeometry

namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)
    {κ : Type*} [Finite κ]

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem coordinateGate_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) (j : κ → Fin 2) (c : κ → CutRing) (σ : κ → Bool) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentCoordinates t u) i).val)
      (A.geometry.coordinateGate t u z j c σ).val := by
  intro x y hh
  apply and_congr (A.coordinate_inward_resolved t u z x y hh)
  exact polygonBooleanPullback_resolved _ _
    (fun i => A.coordinate_localDecision_resolved t u z (j i) (c i)) {σ} x y hh

theorem coordinateGate_control (hlarge : 20 ≤ m+1)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing) (z : ℝ × ℝ)
    (j : κ → Fin 2) (c : κ → CutRing) (σ : κ → Bool)
    (n : ℕ) (q : Fin 2 → ℤ) (W : polygonAlgebra a)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (coordinateWindowPrimitives n q) i).val) W.val)
    (hinc : W ≤ A.geometry.coordinateGate t u z j c σ)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q W)) :
    SmallControlled B.c f (B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u)
      (A.geometry.coordinateGate t u z j c σ)) :=
  A.coordinate_control_inward_gate hlarge t u _ (A.coordinateGate_resolved t u z j c σ) n q W hW hinc f hf hc

end InitialCoverSystem.PatchAtlas

namespace ClippedGerm
variable {a : ℕ} {r : CutRing} {slope : Fin 4} {u : CutRing × CutRing} {z : ℝ × ℝ}
    (G : ClippedGerm a r slope u z)

noncomputable def axialCut (i : Fin 2 × Bool) : CutRing :=
  if i.2 then pointCoordinate G.offset i.1+r else pointCoordinate G.offset i.1-r

theorem model_restrict_gate {ι : Type*} [Finite ι] {C : ConcurrentGeometry a r}
    {j : ι → Fin 4} {c : ι → CutRing}
    (T : C.InwardChart j c z) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (lo hi : Fin 2 → ι) (s : ι)
    (hlo : ∀ d, j (lo d)=axisDirection d ∧ c (lo d)=pointCoordinate G.offset d-r)
    (hhi : ∀ d, j (hi d)=axisDirection d ∧ c (hi d)=pointCoordinate G.offset d+r)
    (hs : j s=slope ∧ c s=integralCutForm a slope G.offset)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i))
      (spatialTranslate u (clippedSlopePrimitive a r slope)).val)
    (σ : Fin 2 × Bool → Bool) :
    T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r slope)) () ⊓
      C.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ =
    (if ∀ d, σ (d,false)=false ∧ σ (d,true)=true then
      (C.localDecision T.vertex T.offset z (j s) (c s))ᶜ else ⊥) ⊓
      C.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ := by
  classical
  apply Subtype.ext
  ext p
  by_cases hgate : p ∈ (C.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ).val
  · have hmargin := hgate.1
    have hassign := hgate.2
    have hlo' (d : Fin 2) : p ∉ (C.localDecision T.vertex T.offset z (j (lo d)) (c (lo d))).val ↔
        σ (d,false)=false := by
      have he := congrFun hassign (d,false)
      simpa only [polygonAssignment,axialCut,Bool.false_eq_true,↓reduceIte,Prod.fst,
        (hlo d).1,(hlo d).2,decide_eq_false_iff_not] using (congrArg (fun b => b=false) he).to_iff
    have hhi' (d : Fin 2) : p ∈ (C.localDecision T.vertex T.offset z (j (hi d)) (c (hi d))).val ↔
        σ (d,true)=true := by
      have he := congrFun hassign (d,true)
      simpa only [polygonAssignment,axialCut,↓reduceIte,Prod.fst,
        (hhi d).1,(hhi d).2,decide_eq_true_eq] using (congrArg (fun b => b=true) he).to_iff
    have he := G.model_formula T hr hz₁ hz₂ lo hi s hlo hhi hs hR p hmargin
    have hc : (∀ d, p ∉ (C.localDecision T.vertex T.offset z (j (lo d)) (c (lo d))).val ∧
        p ∈ (C.localDecision T.vertex T.offset z (j (hi d)) (c (hi d))).val) ↔
        ∀ d, σ (d,false)=false ∧ σ (d,true)=true :=
      forall_congr' (fun d => and_congr (hlo' d) (hhi' d))
    change (_ ∧ _) ↔ (_ ∧ _)
    simp only [hgate,and_true]
    rw [he,hc]
    split_ifs with HH <;> simp only [HH,forall_const,true_and,false_and] <;> rfl
  · change (_ ∧ _) ↔ (_ ∧ _)
    simp only [hgate,and_false]

end ClippedGerm

end SimpleAmenable

end OAI
