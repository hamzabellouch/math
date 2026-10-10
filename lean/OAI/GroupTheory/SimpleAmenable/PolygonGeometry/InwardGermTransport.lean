import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.IndividualGridSplits
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.InactiveNeighborhoodActions

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
namespace ConcurrentGeometry.InwardChart
variable {a : ℕ} {r : CutRing} {C : ConcurrentGeometry a r}
    {ι κ : Type*} [Finite ι] {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ}
    (T : C.InwardChart j c z)

theorem germ_rule (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (R : κ → polygonAlgebra a)
    (hR : ∀ k, ResolvedBy (fun i => halfPlane a (j i) (c i)) (R k).val)
    (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N)
    (rule : (κ → Bool) → Prop)
    (h : ∀ q : GenericSquare a, q.val ∈ N → rule (polygonAssignment R q))
    (p : GenericSquare a) (hp : p ∈ (C.inwardMargin T.vertex T.offset z).val) :
    rule (polygonAssignment (T.polygons R) p) := by
  obtain ⟨q,hq,he⟩ := T.polygons_assignment_realized hr hz₁ hz₂ R hR p hp N hN hz
  rw [← he]
  exact h q hq

theorem polygons_cut_on_margin (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (i : ι) (p : GenericSquare a)
    (hp : p ∈ (C.inwardMargin T.vertex T.offset z).val) :
    p ∈ (T.polygons (fun i => cutPolygon a (j i) (c i)) i).val ↔
      p ∈ (C.localDecision T.vertex T.offset z (j i) (c i)).val := by
  obtain ⟨q,_,he⟩ := T.assignment_realized hr hz₁ hz₂ p hp Set.univ isOpen_univ (Set.mem_univ z)
  change polygonAssignment (fun i => C.localDecision T.vertex T.offset z (j i) (c i)) p ∈
    polygonFormalMask (fun i => cutPolygon a (j i) (c i)) (cutPolygon a (j i) (c i)) ↔ _
  rw [← he,polygonFormalMask_mem _ _ (fun x y h => h i) q]
  simpa only [polygonAssignment,decide_eq_true_eq] using (Bool.eq_iff_iff.mp (congrFun he i))

theorem model_mem_iff_germ_rule (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (R : polygonAlgebra a)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i)) R.val)
    (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N)
    (rule : (ι → Bool) → Prop)
    (h : ∀ q : GenericSquare a, q.val ∈ N →
      (q ∈ R.val ↔ rule (polygonAssignment (fun i => cutPolygon a (j i) (c i)) q)))
    (p : GenericSquare a) (hp : p ∈ (C.inwardMargin T.vertex T.offset z).val) :
    p ∈ (T.polygons (fun _ : Unit => R) ()).val ↔
      rule (polygonAssignment (fun i => C.localDecision T.vertex T.offset z (j i) (c i)) p) := by
  obtain ⟨q,hq,he⟩ := T.assignment_realized hr hz₁ hz₂ p hp N hN hz
  change polygonAssignment (fun i => C.localDecision T.vertex T.offset z (j i) (c i)) p ∈
    polygonFormalMask (fun i => cutPolygon a (j i) (c i)) R ↔ _
  rw [← he,polygonFormalMask_mem _ R hR q]
  exact h q hq

end ConcurrentGeometry.InwardChart

section LocalPeriodicIntervals

theorem local_periodic_interval {a : ℕ} (j : Fin 2) (l v : CutRing)
    (hpos : ordinary l<ordinary v) (hwidth : ordinary v-ordinary l<1) (z : ℝ) :
    ∃ k : ℤ, ∀ p : GenericSquare a,
      |coordinate j p-z|<(1-(ordinary v-ordinary l))/4 →
      (p ∈ (coordinateInterval a j l v).val ↔
        ordinary l+(k:ℝ)≤coordinate j p ∧ coordinate j p<ordinary v+(k:ℝ)) := by
  let d := ordinary v-ordinary l
  let mid := (ordinary l+ordinary v)/2
  let k : ℤ := ⌊z-mid+1/2⌋
  have hk₀ : (k:ℝ)≤z-mid+1/2 := Int.floor_le _
  have hk₁ : z-mid+1/2<(k:ℝ)+1 := Int.lt_floor_add_one _
  refine ⟨k,?_⟩
  intro p hp
  have hlo : ordinary v+(k:ℝ)-1<coordinate j p := by
    have hh := (abs_lt.mp hp).1
    dsimp only [mid] at hk₀ hk₁
    linarith
  have hup : coordinate j p<ordinary l+(k:ℝ)+1 := by
    have hh := (abs_lt.mp hp).2
    dsimp only [mid] at hk₀ hk₁
    linarith
  rw [show (coordinateInterval a j l v).val=coordinateBetween a j l v from rfl,
    mem_coordinateBetween_iff j l v hpos.le hwidth]
  constructor
  · rintro ⟨n,hn⟩
    have hb₀ : (-1:ℝ)<(n:ℝ)+(k:ℝ) := by linarith [hn.1]
    have hb₁ : (n:ℝ)+(k:ℝ)<1 := by linarith [hn.2]
    have hb₀' : -1<n+k := by exact_mod_cast hb₀
    have hb₁' : n+k<1 := by exact_mod_cast hb₁
    have he : n=-k := by omega
    subst n
    simp only [Int.cast_neg] at hn
    constructor <;> linarith [hn.1,hn.2]
  · intro hp
    refine ⟨-k,?_⟩
    simp only [Int.cast_neg]
    constructor <;> linarith [hp.1,hp.2]

theorem local_periodic_rectangle {a : ℕ} (l v : Fin 2 → CutRing)
    (hpos : ∀ j, ordinary (l j)<ordinary (v j))
    (hwidth : ∀ j, ordinary (v j)-ordinary (l j)<1) (z : ℝ × ℝ) :
    ∃ k : Fin 2 → ℤ, ∃ δ : ℝ, 0<δ ∧ ∀ p : GenericSquare a, dist p.val z<δ →
      (p ∈ (coordinateRectangle a l v).val ↔
        ∀ j, ordinary (l j)+(k j:ℝ)≤realCoordinate p.val j ∧
          realCoordinate p.val j<ordinary (v j)+(k j:ℝ)) := by
  have hh j := local_periodic_interval (a := a) j (l j) (v j) (hpos j) (hwidth j) (realCoordinate z j)
  choose k hk using hh
  let δ := min ((1-(ordinary (v 0)-ordinary (l 0)))/4) ((1-(ordinary (v 1)-ordinary (l 1)))/4)
  have hδ : 0<δ := lt_min (by linarith [hwidth 0]) (by linarith [hwidth 1])
  refine ⟨k,δ,hδ,?_⟩
  intro p hp
  have hb : |p.val.1-z.1|<δ ∧ |p.val.2-z.2|<δ := by
    simpa only [Prod.dist_eq,Real.dist_eq,max_lt_iff] using hp
  have hsmall j : |coordinate j p-realCoordinate z j|<(1-(ordinary (v j)-ordinary (l j)))/4 := by
    fin_cases j
    · exact hb.1.trans_le (min_le_left _ _)
    · exact hb.2.trans_le (min_le_right _ _)
  constructor
  · intro hp j
    apply (hk j p (hsmall j)).mp
    fin_cases j
    · exact hp.1
    · exact hp.2
  · intro hp
    exact ⟨(hk 0 p (hsmall 0)).mpr (hp 0),(hk 1 p (hsmall 1)).mpr (hp 1)⟩

end LocalPeriodicIntervals

theorem local_clipped_formula {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (u : CutRing × CutRing) (z : ℝ × ℝ) :
    ∃ k : Fin 2 → ℤ, ∃ δ : ℝ, 0<δ ∧
      let v := u+((k 0:CutRing),(k 1:CutRing))
      ∀ p : GenericSquare a, dist p.val z<δ →
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
  constructor
  · intro hmem
    have hc : p ∈ (spatialTranslate u (coordinateRectangle a (fun _ => -r) (fun _ => r))).val :=
      clippedSlope_le_box r j hr hmem
    have hc' := (hlift p hp).mp hc
    exact ⟨hc',(hs p hc').mp hmem⟩
  · rintro ⟨hc,hside⟩
    exact (hs p hc).mpr hside

end SimpleAmenable

end OAI
