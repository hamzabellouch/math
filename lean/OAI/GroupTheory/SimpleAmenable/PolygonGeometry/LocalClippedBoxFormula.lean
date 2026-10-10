import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.RefinedEndpointDecisions
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ClippedGerms

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section LocalClippedBoxFormula

theorem local_clipped_formula_with_box {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (u : CutRing × CutRing) (z : ℝ × ℝ) :
    ∃ k : Fin 2 → ℤ, ∃ δ : ℝ, 0<δ ∧
      let v := u+((k 0:CutRing),(k 1:CutRing))
      ∀ p : GenericSquare a, dist p.val z<δ →
        (p ∈ (spatialTranslate u (coordinateRectangle a (fun _ => -r) (fun _ => r))).val ↔
          ∀ d, ordinary (pointCoordinate v d-r)≤realCoordinate p.val d ∧
            realCoordinate p.val d<ordinary (pointCoordinate v d+r)) ∧
        (p ∈ (spatialTranslate u (clippedSlopePrimitive a r j)).val ↔
          (∀ d, ordinary (pointCoordinate v d-r)≤realCoordinate p.val d ∧
            realCoordinate p.val d<ordinary (pointCoordinate v d+r)) ∧
          ordinary (integralCutForm a j v)≤cutForm a j p.val) := by
  let l := fun d => -r+pointCoordinate u d
  let h := fun d => r+pointCoordinate u d
  obtain ⟨k,δ,hδ,hlocal⟩ := local_periodic_rectangle (a := a) l h
    (fun d => by dsimp [l,h]; simp only [map_add,map_neg]; linarith [hr.1])
    (fun d => by dsimp [l,h]; simp only [map_add,map_neg]; linarith [hr.2]) z
  let v := u+((k 0:CutRing),(k 1:CutRing))
  have hperiod : spatialTranslate v (clippedSlopePrimitive a r j)=
      spatialTranslate u (clippedSlopePrimitive a r j) := by
    rw [show v=u+((k 0:CutRing),(k 1:CutRing)) from rfl,spatialTranslate_add,spatialTranslate_integral]
  have hbox : spatialTranslate u (coordinateRectangle a (fun _ => -r) (fun _ => r))=
      coordinateRectangle a l h := by
    simpa only [l,h,pointCoordinate] using spatialTranslate_coordinateRectangle u (fun _ => -r) (fun _ => r)
  have hlift (p : GenericSquare a) (hp : dist p.val z<δ) :
      p ∈ (spatialTranslate u (coordinateRectangle a (fun _ => -r) (fun _ => r))).val ↔
        ∀ d, ordinary (pointCoordinate v d-r)≤realCoordinate p.val d ∧
          realCoordinate p.val d<ordinary (pointCoordinate v d+r) := by
    rw [hbox,hlocal p hp]
    apply forall_congr'
    intro d
    have hv : ordinary (pointCoordinate v d)=ordinary (pointCoordinate u d)+(k d:ℝ) := by
      fin_cases d <;> simp [v,pointCoordinate]
    simp only [l,h,map_add,map_neg,map_sub,hv]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  have hs (p : GenericSquare a)
      (hp : ∀ d, ordinary (pointCoordinate v d-r)≤realCoordinate p.val d ∧
        realCoordinate p.val d<ordinary (pointCoordinate v d+r)) :
      p ∈ (spatialTranslate u (clippedSlopePrimitive a r j)).val ↔
        ordinary (integralCutForm a j v)≤cutForm a j p.val := by
    have hnear (d : Fin 2) : |realCoordinate p.val d-ordinary (pointCoordinate v d)|<ordinary r := by
      have hne : realCoordinate p.val d ≠ ordinary (pointCoordinate v d-r) := by
        have hh := p.property.2.2 (axisDirection d) (pointCoordinate v d-r)
        fin_cases d <;> exact hh
      have hlo := lt_of_le_of_ne (hp d).1 hne.symm
      have hup := (hp d).2
      simp only [map_sub,map_add] at hlo hup
      rw [abs_lt]
      constructor <;> linarith
    rw [← hperiod]
    exact translated_clippedSlope_planar r j hr v p p.val
      (by rw [Int.fract_eq_self.mpr p.property.1,Int.fract_eq_self.mpr p.property.2.1])
      ⟨hnear 0,hnear 1⟩
  refine ⟨k,δ,hδ,?_⟩
  dsimp only
  intro p hp
  refine ⟨hlift p hp,?_⟩
  constructor
  · intro hmem
    have hc : p ∈ (spatialTranslate u (coordinateRectangle a (fun _ => -r) (fun _ => r))).val :=
      clippedSlope_le_box r j hr hmem
    have hc' := (hlift p hp).mp hc
    exact ⟨hc',(hs p hc').mp hmem⟩
  · rintro ⟨hc,hside⟩
    exact (hs p hc).mpr hside

namespace ClippedGerm

def BoxValid {a : ℕ} {r : CutRing} {j : Fin 4} {u : CutRing × CutRing} {z : ℝ × ℝ}
    (G : ClippedGerm a r j u z) : Prop :=
  ∀ p : GenericSquare a, dist p.val z<G.radius →
    (p ∈ (spatialTranslate u (coordinateRectangle a (fun _ => -r) (fun _ => r))).val ↔
      ∀ d, ordinary (pointCoordinate G.offset d-r)≤realCoordinate p.val d ∧
        realCoordinate p.val d<ordinary (pointCoordinate G.offset d+r))
end ClippedGerm

theorem clippedGerm_exists_box_valid {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (u : CutRing × CutRing) (z : ℝ × ℝ) :
    ∃ G : ClippedGerm a r j u z, G.BoxValid := by
  obtain ⟨k,δ,hδ,h⟩ := local_clipped_formula_with_box r j hr u z
  refine ⟨⟨k,δ,hδ,fun p hp => (h p hp).2⟩,?_⟩
  exact fun p hp => (h p hp).1

end LocalClippedBoxFormula

namespace ConcurrentGeometry.InwardChart
variable {a : ℕ} {r : CutRing} {C : ConcurrentGeometry a r} {ι : Type*} [Finite ι]
    {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ} (T : C.InwardChart j c z)

theorem decisions_locally_eq (hr : 0<ordinary r ∧ ordinary r<1/2) :
    ∃ O : Set (ℝ × ℝ), IsOpen O ∧ z ∈ O ∧ ∀ p : GenericSquare a, p.val ∈ O →
      p ∈ (C.inwardMargin T.vertex T.offset z).val ∧
      ∀ i, p ∈ (C.localDecision T.vertex T.offset z (j i) (c i)).val ↔
        p ∈ (cutPolygon a (j i) (c i)).val := by
  obtain ⟨N,hN,hz,hlocal⟩ := localCutFamily_locally_eq j c z
  refine ⟨N ∩ Metric.ball z (C.epsilon/2),hN.inter Metric.isOpen_ball,
    ⟨hz,Metric.mem_ball_self (by linarith [C.positive])⟩,?_⟩
  intro p hp
  refine ⟨T.canonical_mem hr p hp.2,fun i => ?_⟩
  have he := (T.local_decisions_eq hr p hp.2).trans (hlocal p hp.1)
  simpa only [polygonAssignment,decide_eq_true_eq] using Bool.eq_iff_iff.mp (congrFun he i)

omit [Finite ι] in

theorem refined_coordinate_phase {κ : Type*} [Finite κ]
    {N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (d : κ → Fin 2) (v : κ → CutRing) (f : κ → ι)
    (hf : ∀ k, j (f k)=axisDirection (d k) ∧ c (f k)=v k)
    (hv : ∀ k, cutFraction (v k) ∈ Set.range e)
    (hlocal : ∀ p : GenericSquare a, p ∈ (refinedGridRectangle a N e cell).val →
      p ∈ (C.inwardMargin T.vertex T.offset z).val ∧ ∀ i,
      p ∈ (C.localDecision T.vertex T.offset z (j i) (c i)).val ↔
        p ∈ (cutPolygon a (j i) (c i)).val) :
    ∃ σ : κ → Bool, refinedGridRectangle a N e cell ≤
      C.coordinateGate T.vertex T.offset z d v σ := by
  classical
  obtain ⟨x,hx⟩ := refinedGridRectangle_nonempty e he hzero hlast hmesh cell
  let σ := polygonAssignment (fun k => C.localDecision T.vertex T.offset z (axisDirection (d k)) (v k)) x
  refine ⟨σ,fun y hy => ⟨(hlocal y hy).1,?_⟩⟩
  funext k
  apply decide_eq_decide.mpr
  have hxy := finite_grid_endpoint_decision e he hzero hlast (cell (d k)) (v k) (hv k) 0 (d k) y x
    ((refinedGridRectangle_mem e he hzero hlast hmesh cell y).mp hy (d k))
    ((refinedGridRectangle_mem e he hzero hlast hmesh cell x).mp hx (d k))
  have hy' := (hlocal y hy).2 (f k)
  have hx' := (hlocal x hx).2 (f k)
  rw [(hf k).1,(hf k).2] at hy' hx'
  refine Iff.trans hy' (Iff.trans ?_ hx'.symm)
  simpa only [cutPolygon,halfPlane,Set.mem_ofPred_eq,cutForm_axis,coordinate,realCoordinate,
    Int.cast_zero,add_zero] using hxy

omit [Finite ι] in

theorem refined_interior_phase_bounds {N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (v : CutRing × CutRing)
    (lo hi : Fin 2 → ι)
    (hlo : ∀ d, j (lo d)=axisDirection d ∧ c (lo d)=pointCoordinate v d-r)
    (hhi : ∀ d, j (hi d)=axisDirection d ∧ c (hi d)=pointCoordinate v d+r)
    (hlor : ∀ d, cutFraction (pointCoordinate v d-r) ∈ Set.range e)
    (hhir : ∀ d, cutFraction (pointCoordinate v d+r) ∈ Set.range e)
    (σ : Fin 2 × Bool → Bool) (hσ : ∀ d, σ (d,false)=false ∧ σ (d,true)=true)
    (hgate : refinedGridRectangle a N e cell ≤ C.coordinateGate T.vertex T.offset z Prod.fst
      (fun k => if k.2 then pointCoordinate v k.1+r else pointCoordinate v k.1-r) σ)
    (hlocal : ∀ p : GenericSquare a, p ∈ (refinedGridRectangle a N e cell).val → ∀ i,
      p ∈ (C.localDecision T.vertex T.offset z (j i) (c i)).val ↔
        p ∈ (cutPolygon a (j i) (c i)).val) :
    ∀ d, -ordinary r≤ordinary (e (cell d).castSucc)-ordinary (pointCoordinate v d) ∧
      ordinary (e (cell d).succ)-ordinary (pointCoordinate v d)≤ordinary r := by
  obtain ⟨x,hx⟩ := refinedGridRectangle_nonempty e he hzero hlast hmesh cell
  have hassign := (hgate hx).2
  intro d
  have hl := congrFun hassign (d,false)
  have hh := congrFun hassign (d,true)
  have hlocalL := hlocal x hx (lo d)
  have hlocalH := hlocal x hx (hi d)
  rw [(hlo d).1,(hlo d).2] at hlocalL
  rw [(hhi d).1,(hhi d).2] at hlocalH
  have hl' : ¬ x ∈ (C.localDecision T.vertex T.offset z (axisDirection d) (pointCoordinate v d-r)).val := by
    simpa only [polygonAssignment,Bool.false_eq_true,↓reduceIte,(hσ d).1,decide_eq_false_iff_not] using hl
  have hh' : x ∈ (C.localDecision T.vertex T.offset z (axisDirection d) (pointCoordinate v d+r)).val := by
    simpa only [polygonAssignment,↓reduceIte,(hσ d).2,decide_eq_true_eq] using hh
  simp only [cutPolygon,halfPlane,Set.mem_ofPred_eq,cutForm_axis] at hlocalL hlocalH
  have hb : ordinary (pointCoordinate v d-r) ≤ coordinate d x ∧
      coordinate d x < ordinary (pointCoordinate v d+r) := by
    exact ⟨le_of_not_gt (fun h => hl' (hlocalL.mpr h)),hlocalH.mp hh'⟩
  have hf := finite_grid_interval_lift e he hzero hlast (cell d)
    (pointCoordinate v d-r) (pointCoordinate v d+r) (hlor d) (hhir d) (coordinate d x)
    ((refinedGridRectangle_mem e he hzero hlast hmesh cell x).mp hx d) 0
    (by simpa only [Int.cast_zero,add_zero] using hb)
  simp only [Int.cast_zero,add_zero,map_sub,map_add] at hf
  constructor <;> linarith [hf.1,hf.2]

end ConcurrentGeometry.InwardChart

end SimpleAmenable

end OAI
