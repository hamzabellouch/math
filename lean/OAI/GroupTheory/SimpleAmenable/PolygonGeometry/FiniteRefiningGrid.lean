import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.RectangularBound

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteRefiningGrid
attribute [local instance] cutOrdinaryOrder

theorem finite_refining_grid (S : Finset CutRing) (n : ℕ) (_hn : 0<n) :
    ∃ N : ℕ, 0<N ∧ ∃ e : Fin (N+1) → CutRing,
      StrictMono (fun i => ordinary (e i)) ∧ e 0=0 ∧ e (Fin.last N)=1 ∧
      (∀ c ∈ S, cutFraction c ∈ Set.range e) ∧
      (∀ i : Fin (n+1), windowCut n 0 i ∈ Set.range e) := by
  classical
  let T : Finset CutRing := insert 1 (insert 0 ((S.image cutFraction) ∪ windowEndpointSet n))
  have h0 : (0:CutRing) ∈ T := by simp [T]
  have h1 : (1:CutRing) ∈ T := by simp [T]
  have hcard : 2 ≤ T.card := by
    have hh : ({0,1} : Finset CutRing) ⊆ T := by simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]; exact ⟨h0,h1⟩
    have hh' := Finset.card_le_card hh
    simpa only [Finset.card_insert_of_notMem (by simp : (0:CutRing) ∉ ({1} : Finset CutRing)),Finset.card_singleton] using hh'
  let N := T.card-1
  have hN : 0<N := by dsimp [N]; omega
  have hc : T.card=N+1 := by dsimp [N]; omega
  let e : Fin (N+1) ↪o CutRing := T.orderEmbOfFin hc
  have he (c : CutRing) : c ∈ Set.range e ↔ c ∈ T := by
    rw [Finset.range_orderEmbOfFin]; rfl
  have hb (i : Fin (N+1)) : 0≤ordinary (e i) ∧ ordinary (e i)≤1 := by
    have hi := Finset.orderEmbOfFin_mem T hc i
    change e i ∈ T at hi
    simp only [T,Finset.mem_insert,Finset.mem_union,Finset.mem_image] at hi
    rcases hi with hi | hi | ⟨c,hc,heq⟩ | hi
    · simp only [hi,map_one,zero_le_one,le_refl,and_self]
    · simp only [hi,map_zero,le_refl,zero_le_one,and_self]
    · rw [← heq,ordinary_cutFraction]; exact ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
    · rw [windowEndpointSet,Finset.mem_image] at hi
      obtain ⟨c,_,heq⟩ := hi
      rw [← heq,ordinary_cutFraction]; exact ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
  have hzero : e 0=0 := by
    obtain ⟨i,hi⟩ := (he 0).mpr h0
    apply ordinary_injective
    have hh : ordinary (e 0)≤ordinary (e i) := e.monotone (Fin.zero_le i)
    rw [hi,map_zero ordinary] at hh
    simpa only [map_zero ordinary] using le_antisymm hh (hb 0).1
  have hlast : e (Fin.last N)=1 := by
    obtain ⟨i,hi⟩ := (he 1).mpr h1
    apply ordinary_injective
    have hh : ordinary (e i)≤ordinary (e (Fin.last N)) := e.monotone (Fin.le_last i)
    rw [hi,map_one] at hh
    simpa only [map_one ordinary] using le_antisymm (hb (Fin.last N)).2 hh
  refine ⟨N,hN,e,e.strictMono,hzero,hlast,?_,?_⟩
  · intro c hc
    apply (he _).mpr
    simp only [T,Finset.mem_insert,Finset.mem_union]
    exact Or.inr (Or.inr (Or.inl (Finset.mem_image.mpr ⟨c,hc,rfl⟩)))
  · intro i
    apply (he _).mpr
    by_cases hi : i.val<n
    · have hh : windowCut n 0 i=windowInterior n ⟨i.val,hi⟩ := by simp [windowCut,hi]
      rw [hh]
      simp only [T,Finset.mem_insert,Finset.mem_union]
      exact Or.inr (Or.inr (Or.inr (windowInterior_mem n _)))
    · have hi' : i=Fin.last n := by apply Fin.ext; change i.val=n; omega
      rw [hi',windowCut_last]
      simpa using h1

theorem finite_grid_no_between {N : ℕ} {e : Fin (N+1) → CutRing}
    (he : StrictMono (fun i => ordinary (e i))) (i : Fin N) {c : CutRing}
    (hc : c ∈ Set.range e) :
    ¬(ordinary (e i.castSucc)<ordinary c ∧ ordinary c<ordinary (e i.succ)) := by
  obtain ⟨j,rfl⟩ := hc
  rintro ⟨hl,hu⟩
  have h₁ := he.lt_iff_lt.mp hl
  have h₂ := he.lt_iff_lt.mp hu
  change i.val < j.val at h₁
  change j.val < i.val+1 at h₂
  omega

theorem finite_grid_refines_window {N n : ℕ} (hn : 0<n)
    (e : Fin (N+1) → CutRing) (he : StrictMono (fun i => ordinary (e i)))
    (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hcuts : ∀ j : Fin (n+1), windowCut n 0 j ∈ Set.range e) (i : Fin N) :
    ∃ j : Fin n,
      ordinary (windowCut n 0 j.castSucc)≤ordinary (e i.castSucc) ∧
      ordinary (e i.succ)≤ordinary (windowCut n 0 j.succ) := by
  have h0 : 0≤ordinary (e i.castSucc) := by
    have hh := he.monotone (Fin.zero_le i.castSucc); simpa only [hzero,map_zero] using hh
  have h1 : ordinary (e i.castSucc)<1 := by
    have hh := he (show i.castSucc<Fin.last N from by exact i.isLt)
    simpa only [hlast,map_one] using hh
  have hz : ordinary (windowCut n 0 0)=0 := by simp [windowCut_zero n 0 hn]
  have ht : ordinary (windowCut n 0 (Fin.last n))=1 := by simp [windowCut_last]
  obtain ⟨j,hj⟩ := finite_interval_cell hn (ordinary (e i.castSucc))
    (x := fun j => ordinary (windowCut n 0 j)) (by rwa [hz]) (by rwa [ht])
  refine ⟨j,hj.1,?_⟩
  exact le_of_not_gt (fun h => finite_grid_no_between he i (hcuts j.succ) ⟨hj.2,h⟩)

end FiniteRefiningGrid

section RefinementPartition

theorem coordinateInterval_mem_preferred {a : ℕ} (j : Fin 2) (u v : CutRing)
    (hlo : 0≤ordinary u) (huv : ordinary u≤ordinary v) (hup : ordinary v≤1)
    (hlen : ordinary v-ordinary u<1) (p : GenericSquare a) :
    p ∈ (coordinateInterval a j u v).val ↔
      ordinary u≤coordinate j p ∧ coordinate j p<ordinary v := by
  change p ∈ coordinateBetween a j u v ↔ _
  rw [mem_coordinateBetween_iff j u v huv hlen p]
  constructor
  · rintro ⟨k,hk,hk'⟩
    have hp := coordinate_bounds j p
    have hk₁ : (-1:ℝ)<k := by linarith [hp.2]
    have hk₂ : (k:ℝ)<1 := by linarith [hp.1]
    have hk₁' : (-1:ℤ)<k := by exact_mod_cast hk₁
    have hk₂' : k<(1:ℤ) := by exact_mod_cast hk₂
    have hk0 : k=0 := by omega
    simpa only [hk0,Int.cast_zero,add_zero] using And.intro hk hk'
  · exact fun h => ⟨0,by simpa using h.1,by simpa using h.2⟩

noncomputable def refinedGridRectangle (a N : ℕ) (e : Fin (N+1) → CutRing)
    (cell : Fin 2 → Fin N) : polygonAlgebra a :=
  coordinateRectangle a (fun j => e (cell j).castSucc) (fun j => e (cell j).succ)

theorem refinedGridRectangle_mem {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (p : GenericSquare a) :
    p ∈ (refinedGridRectangle a N e cell).val ↔ ∀ j : Fin 2,
      ordinary (e (cell j).castSucc)≤coordinate j p ∧ coordinate j p<ordinary (e (cell j).succ) := by
  have h (j : Fin 2) := coordinateInterval_mem_preferred j (e (cell j).castSucc) (e (cell j).succ)
    (by have hh := he.monotone (Fin.zero_le (cell j).castSucc); simpa only [hzero,map_zero] using hh)
    (he (Fin.castSucc_lt_succ (i := cell j))).le
    (by have hh := he.monotone (Fin.le_last (cell j).succ); simpa only [hlast,map_one] using hh)
    (hmesh (cell j)) p
  change (p ∈ (coordinateInterval a 0 _ _).val ∧ p ∈ (coordinateInterval a 1 _ _).val) ↔ _
  rw [h 0,h 1,Fin.forall_fin_two]

theorem refinedGridRectangle_cover {a N : ℕ} (hN : 0<N) (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (p : GenericSquare a) : ∃ cell : Fin 2 → Fin N, p ∈ (refinedGridRectangle a N e cell).val := by
  have h (j : Fin 2) : ∃ i : Fin N,
      ordinary (e i.castSucc)≤coordinate j p ∧ coordinate j p<ordinary (e i.succ) := by
    exact finite_interval_cell (x := fun i => ordinary (e i)) hN (coordinate j p)
      (by simpa only [hzero,map_zero] using (coordinate_bounds j p).1)
      (by simpa only [hlast,map_one] using (coordinate_bounds j p).2)
  choose cell hc using h
  exact ⟨cell,(refinedGridRectangle_mem e he hzero hlast hmesh cell p).mpr hc⟩

theorem refinedGridRectangle_disjoint {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1) :
    Pairwise fun i k : Fin 2 → Fin N => Disjoint (refinedGridRectangle a N e i).val
      (refinedGridRectangle a N e k).val := by
  intro i k hik
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hik
  apply Set.disjoint_left.mpr
  intro p hp hq
  have hi := (refinedGridRectangle_mem e he hzero hlast hmesh i p).mp hp j
  have hk := (refinedGridRectangle_mem e he hzero hlast hmesh k p).mp hq j
  rcases lt_or_gt_of_ne hj with hh | hh
  · have hle := he.monotone (show (i j).succ≤(k j).castSucc from by change (i j).val+1≤(k j).val; exact hh)
    linarith
  · have hle := he.monotone (show (k j).succ≤(i j).castSucc from by change (k j).val+1≤(i j).val; exact hh)
    linarith

theorem refinedGridRectangle_resolved {a N : ℕ} (r : CutRing) (e : Fin (N+1) → CutRing) :
    ∃ n : ℕ, ∃ q : Fin 2 → ℤ, ∀ cell : Fin 2 → Fin N,
      ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
        (coordinateWindowPrimitives n q) i).val) (refinedGridRectangle a N e cell).val := by
  obtain ⟨n,q,hq⟩ := finite_coordinate_windows_container (fun _ : Fin (N+1) => 1)
    (fun i _ => endpointLabel (e i))
  have hl (i : Fin (N+1)) (j : Fin 2) : q j≤endpointLabel (e i) ∧ endpointLabel (e i)<q j+n := by
    have hh := hq i j
    constructor <;> omega
  refine ⟨n,q,fun cell x y hh => ?_⟩
  exact and_congr
    (coordinateInterval_window n q 0 _ _ (hl _ 0) (hl _ 0) x y hh)
    (coordinateInterval_window n q 1 _ _ (hl _ 1) (hl _ 1) x y hh)

end RefinementPartition

end SimpleAmenable
end
end

end OAI
