import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.WindowRectangles

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section WindowClipping

theorem window_cell_enclosure (n : ℕ) (q : ℤ) (i : Fin n) (b e : CutRing)
    (hb : q≤endpointLabel b ∧ endpointLabel b<q+n)
    (he : q≤endpointLabel e ∧ endpointLabel e<q+n)
    (x : ℝ) (k : ℤ)
    (hx : ordinary (windowCut n q i.castSucc)≤x ∧ x<ordinary (windowCut n q i.succ))
    (hk : ordinary b≤x+(k:ℝ) ∧ x+(k:ℝ)<ordinary e) :
    ordinary b≤ordinary (windowCut n q i.castSucc)+(k:ℝ) ∧
      ordinary (windowCut n q i.succ)+(k:ℝ)≤ordinary e := by
  have hn (z : CutRing) (hz : q≤endpointLabel z ∧ endpointLabel z<q+n) :
      ¬(ordinary (windowCut n q i.castSucc)<ordinary z-(k:ℝ) ∧
        ordinary z-(k:ℝ)<ordinary (windowCut n q i.succ)) := by
    have hl : endpointLabel (z-(k:CutRing))=endpointLabel z := by simp [endpointLabel_sub]
    simpa only [map_sub,map_intCast] using
      windowCut_no_between n q i (z-(k:CutRing)) (by rwa [hl])
  constructor
  · by_contra hh
    exact hn b hb ⟨by linarith,by linarith⟩
  · by_contra hh
    exact hn e he ⟨by linarith,by linarith⟩

theorem clippedSlope_le_box {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0<ordinary r ∧ ordinary r<1/2) :
    clippedSlopePrimitive a r j ≤ coordinateRectangle a (fun _ => -r) (fun _ => r) := by
  intro p hp
  obtain ⟨k,hk,_⟩ := Set.mem_iUnion.mp hp
  have hb := (mem_circularBoxPiece r k p).mp hk
  change (p ∈ coordinateBetween a 0 (-r) r ∧ p ∈ coordinateBetween a 1 (-r) r)
  constructor
  · apply (mem_coordinateBetween_iff 0 (-r) r (by rw [map_neg]; linarith)
      (by rw [map_neg]; linarith) p).mpr
    refine ⟨-(k.1.val:ℤ),?_⟩
    simpa only [coordinate,Matrix.cons_val_zero,Matrix.cons_val_one,map_neg,Int.cast_neg,Int.cast_natCast,← sub_eq_add_neg] using hb.1
  · apply (mem_coordinateBetween_iff 1 (-r) r (by rw [map_neg]; linarith)
      (by rw [map_neg]; linarith) p).mpr
    refine ⟨-(k.2.val:ℤ),?_⟩
    simpa only [coordinate,Matrix.cons_val_zero,Matrix.cons_val_one,map_neg,Int.cast_neg,Int.cast_natCast,← sub_eq_add_neg] using hb.2

theorem windowRectangle_clipping_chart {a : ℕ} (r : CutRing)
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (hb : ∀ j, q j≤endpointLabel (-r) ∧ endpointLabel (-r)<q j+n)
    (he : ∀ j, q j≤endpointLabel r ∧ endpointLabel r<q j+n)
    (p : GenericSquare a) (hp : p ∈ (windowRectangle a n q cell).val)
    (hclip : p ∈ (coordinateRectangle a (fun _ => -r) (fun _ => r)).val) :
    ∃ k : Fin 2 → ℤ, ∀ j,
      -ordinary r≤ordinary (windowCut n (q j) (cell j).castSucc)+(k j:ℝ) ∧
      ordinary (windowCut n (q j) (cell j).succ)+(k j:ℝ)≤ordinary r := by
  have hc (j : Fin 2) : p ∈ coordinateBetween a j (-r) r := by
    fin_cases j
    · exact hclip.1
    · exact hclip.2
  have hi (j : Fin 2) := (mem_coordinateBetween_iff j (-r) r
    (by rw [map_neg]; linarith) (by rw [map_neg]; linarith) p).mp (hc j)
  choose k hk using hi
  refine ⟨fun j => k j+⌊coordinate j p-ordinary ((q j:CutRing)*cutTau)⌋,?_⟩
  intro j
  have hh := window_cell_enclosure n (q j) (cell j) (-r) r (hb j) (he j)
    (realCoordinate (windowPlanarLift q p) j)
    (k j+⌊coordinate j p-ordinary ((q j:CutRing)*cutTau)⌋)
    ((windowRectangle_mem n hn q cell p).mp hp j) ?_
  · simpa only [map_neg] using hh
  · simp only [windowPlanarLift_coordinate,liftedCoordinate,Int.cast_add]
    constructor <;> linarith [(hk j).1,(hk j).2]

theorem windowRectangle_clipped_sign {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (k : Fin 2 → ℤ)
    (hk : ∀ d, -ordinary r≤ordinary (windowCut n (q d) (cell d).castSucc)+(k d:ℝ) ∧
      ordinary (windowCut n (q d) (cell d).succ)+(k d:ℝ)≤ordinary r)
    (p : GenericSquare a) (hp : p ∈ (windowRectangle a n q cell).val) :
    p ∈ (clippedSlopePrimitive a r j).val ↔
      0≤cutForm a j ((windowPlanarLift q p).1+(k 0:ℝ),(windowPlanarLift q p).2+(k 1:ℝ)) := by
  let z := ((windowPlanarLift q p).1+(k 0:ℝ),(windowPlanarLift q p).2+(k 1:ℝ))
  have hz : p.val=(Int.fract z.1,Int.fract z.2) := by
    simpa only [z,Int.fract_add_intCast] using windowPlanarLift_spec q p
  have hbounds (d : Fin 2) : -ordinary r<realCoordinate z d ∧ realCoordinate z d<ordinary r := by
    have hm := (windowRectangle_mem n hn q cell p).mp hp d
    have hh := hk d
    have he : realCoordinate z d=realCoordinate (windowPlanarLift q p) d+(k d:ℝ) := by
      fin_cases d <;> rfl
    have hne := planar_lift_avoidsCuts p z hz (Fin.castLE (by omega) d) (-r)
    have hf : cutForm a (Fin.castLE (by omega) d) z=realCoordinate z d := by
      fin_cases d <;> rfl
    rw [hf,map_neg] at hne
    rw [he] at hne ⊢
    constructor
    · exact lt_of_le_of_ne (by linarith) (Ne.symm hne)
    · linarith
  apply mem_clippedSlope_lift r j hr p z ⟨hbounds 0,hbounds 1⟩ hz

end WindowClipping

section ActualSlopeClassifier

theorem windowRectangle_slope_classifier {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (hb : ∀ d, q d≤endpointLabel (-r) ∧ endpointLabel (-r)<q d+n)
    (he : ∀ d, q d≤endpointLabel r ∧ endpointLabel r<q d+n) :
    (∀ p ∈ (windowRectangle a n q cell).val, p ∉ (clippedSlopePrimitive a r j).val) ∨
    ∃ k : Fin 2 → ℤ,
      (∀ d, -ordinary r≤ordinary (windowCut n (q d) (cell d).castSucc)+(k d:ℝ) ∧
        ordinary (windowCut n (q d) (cell d).succ)+(k d:ℝ)≤ordinary r) ∧
      ∀ p ∈ (windowRectangle a n q cell).val,
        p ∈ (clippedSlopePrimitive a r j).val ↔
          ordinary (-integralCutForm a j ((k 0:CutRing),(k 1:CutRing))) ≤
            cutForm a j (windowPlanarLift q p) := by
  classical
  by_cases h : ∃ p ∈ (windowRectangle a n q cell).val, p ∈ (clippedSlopePrimitive a r j).val
  · obtain ⟨p,hp,hp'⟩ := h
    obtain ⟨k,hk⟩ := windowRectangle_clipping_chart r hr n hn q cell hb he p hp
      (clippedSlope_le_box r j hr hp')
    refine Or.inr ⟨k,hk,?_⟩
    intro t ht
    rw [windowRectangle_clipped_sign r j hr n hn q cell k hk t ht]
    have hadd := cutForm_add a j (windowPlanarLift q t) ((k 0:ℝ),(k 1:ℝ))
    have hord := cutForm_ordinary a j ((k 0:CutRing),(k 1:CutRing))
    simp only [map_intCast] at hord
    rw [map_neg]
    change 0 ≤ cutForm a j (windowPlanarLift q t+((k 0:ℝ),(k 1:ℝ))) ↔ _
    rw [hadd,hord]
    exact neg_le_iff_add_nonneg.symm
  · exact Or.inl (fun p hp hpp => h ⟨p,hp,hpp⟩)

theorem windowRectangle_crossing_line_point {a : ℕ}
    (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (j : Fin 4) (c : CutRing) (x y : GenericSquare a)
    (hx : x ∈ (windowRectangle a n q cell).val)
    (hy : y ∈ (windowRectangle a n q cell).val)
    (hcx : cutForm a j (windowPlanarLift q x)≤ordinary c)
    (hcy : ordinary c≤cutForm a j (windowPlanarLift q y)) :
    ∃ z : ℝ × ℝ, cutForm a j z=ordinary c ∧ ∀ d,
      ordinary (windowCut n (q d) (cell d).castSucc)≤realCoordinate z d ∧
      realCoordinate z d≤ordinary (windowCut n (q d) (cell d).succ) := by
  rw [cutForm_normal] at hcx hcy
  obtain ⟨z,hz,hb⟩ := line_point_in_box (ordinary (lineNormal a j).1)
    (ordinary (lineNormal a j).2) (ordinary c)
    (fun d => ordinary (windowCut n (q d) (cell d).castSucc))
    (fun d => ordinary (windowCut n (q d) (cell d).succ))
    (windowPlanarLift q x) (windowPlanarLift q y)
    (fun d => ⟨((windowRectangle_mem n hn q cell x).mp hx d).1,
      ((windowRectangle_mem n hn q cell x).mp hx d).2.le⟩)
    (fun d => ⟨((windowRectangle_mem n hn q cell y).mp hy d).1,
      ((windowRectangle_mem n hn q cell y).mp hy d).2.le⟩) hcx hcy
  exact ⟨z,by rwa [cutForm_normal],hb⟩

end ActualSlopeClassifier

end SimpleAmenable
end
end

end OAI
