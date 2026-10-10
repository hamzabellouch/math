import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ClippedGerms
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FarClippingGeometry
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.LocalClippedBoxFormula

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ExteriorPhaseGeometry
namespace ClippedGerm
variable {a : ℕ} {r : CutRing} {slope : Fin 4} {u : CutRing × CutRing} {z : ℝ × ℝ}
    (G : ClippedGerm a r slope u z)

theorem gate_box_iff {ι : Type*} {C : ConcurrentGeometry a r}
    {j : ι → Fin 4} {c : ι → CutRing} (T : C.InwardChart j c z)
    (hbox : G.BoxValid) (lo hi : Fin 2 → ι)
    (hlo : ∀ k, j (lo k)=axisDirection k ∧ c (lo k)=pointCoordinate G.offset k-r)
    (hhi : ∀ k, j (hi k)=axisDirection k ∧ c (hi k)=pointCoordinate G.offset k+r)
    (σ : Fin 2 × Bool → Bool) (p : GenericSquare a)
    (hp : p ∈ (C.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ).val)
    (hpnear : dist p.val z<G.radius)
    (hlocal : ∀ i, p ∈ (C.localDecision T.vertex T.offset z (j i) (c i)).val ↔
      p ∈ (cutPolygon a (j i) (c i)).val) :
    p ∈ (spatialTranslate u (coordinateRectangle a (fun _ => -r) (fun _ => r))).val ↔
      ∀ k, σ (k,false)=false ∧ σ (k,true)=true := by
  classical
  rw [hbox p hpnear]
  apply forall_congr'
  intro k
  have hL := hlocal (lo k)
  have hH := hlocal (hi k)
  rw [(hlo k).1,(hlo k).2] at hL
  rw [(hhi k).1,(hhi k).2] at hH
  have hsL : decide (p ∈ (C.localDecision T.vertex T.offset z (axisDirection k)
      (pointCoordinate G.offset k-r)).val)=σ (k,false) := congrFun hp.2 (k,false)
  have hsH : decide (p ∈ (C.localDecision T.vertex T.offset z (axisDirection k)
      (pointCoordinate G.offset k+r)).val)=σ (k,true) := congrFun hp.2 (k,true)
  change (p ∈ (C.localDecision T.vertex T.offset z (axisDirection k) (pointCoordinate G.offset k-r)).val ↔
    cutForm a (axisDirection k) p.val<ordinary (pointCoordinate G.offset k-r)) at hL
  change (p ∈ (C.localDecision T.vertex T.offset z (axisDirection k) (pointCoordinate G.offset k+r)).val ↔
    cutForm a (axisDirection k) p.val<ordinary (pointCoordinate G.offset k+r)) at hH
  rw [cutForm_axis] at hL hH
  have hL' : σ (k,false)=false ↔ ordinary (pointCoordinate G.offset k-r)≤realCoordinate p.val k := by
    rw [← hsL,decide_eq_false_iff_not,hL,not_lt]
  have hH' : σ (k,true)=true ↔ realCoordinate p.val k<ordinary (pointCoordinate G.offset k+r) := by
    rw [← hsH,decide_eq_true_eq,hH]
  exact and_congr hL'.symm hH'.symm

theorem exterior_old_cell {ι : Type*} {C : ConcurrentGeometry a r}
    {j : ι → Fin 4} {c : ι → CutRing} (T : C.InwardChart j c z)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (hbox : G.BoxValid)
    (lo hi : Fin 2 → ι)
    (hlo : ∀ k, j (lo k)=axisDirection k ∧ c (lo k)=pointCoordinate G.offset k-r)
    (hhi : ∀ k, j (hi k)=axisDirection k ∧ c (hi k)=pointCoordinate G.offset k+r)
    (σ : Fin 2 × Bool → Bool) (hσ : ¬ ∀ k, σ (k,false)=false ∧ σ (k,true)=true)
    (p : GenericSquare a)
    (hp : p ∈ (C.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ).val)
    (hpnear : dist p.val z<G.radius)
    (hlocal : ∀ i, p ∈ (C.localDecision T.vertex T.offset z (j i) (c i)).val ↔
      p ∈ (cutPolygon a (j i) (c i)).val)
    (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (hb : ∀ d, q d≤endpointLabel (-r) ∧ endpointLabel (-r)<q d+n)
    (he : ∀ d, q d≤endpointLabel r ∧ endpointLabel r<q d+n)
    (hinitial : p ∈ (spatialTranslate u (windowRectangle a n q cell)).val) :
    Disjoint (windowRectangle a n q cell) (coordinateRectangle a (fun _ => -r) (fun _ => r)) := by
  have hout : p ∉ (spatialTranslate u (coordinateRectangle a (fun _ => -r) (fun _ => r))).val :=
    fun hh => hσ ((G.gate_box_iff T hbox lo hi hlo hhi σ p hp hpnear hlocal).mp hh)
  exact windowRectangle_exterior_of_point r hr n hn q cell hb he (translate a (-u) p) hinitial hout

end ClippedGerm
end ExteriorPhaseGeometry

end SimpleAmenable
end
end

end OAI
