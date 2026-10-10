import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.WindowRectangles
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FiniteArrangementGerms
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FiniteRefiningGrid

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section RefinedEndpointDecisions

theorem finite_grid_endpoint_sides {N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (i : Fin N) (c : CutRing) (hc : cutFraction c ∈ Set.range e) (k : ℤ) :
    ordinary c-(k:ℝ)≤ordinary (e i.castSucc) ∨ ordinary (e i.succ)≤ordinary c-(k:ℝ) := by
  by_contra hh
  push Not at hh
  have hlo : 0≤ordinary (e i.castSucc) := by
    have h := he.monotone (Fin.zero_le i.castSucc)
    simpa only [hzero,map_zero] using h
  have hup : ordinary (e i.succ)≤1 := by
    have h := he.monotone (Fin.le_last i.succ)
    simpa only [hlast,map_one] using h
  have hf : ⌊ordinary c⌋=k := Int.floor_eq_iff.mpr ⟨by linarith,by linarith⟩
  have hfrac : ordinary (cutFraction c)=ordinary c-(k:ℝ) := by rw [ordinary_cutFraction,Int.fract,hf]
  exact finite_grid_no_between he i hc (by rw [hfrac]; exact ⟨hh.1,hh.2⟩)

theorem finite_grid_endpoint_decision {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (i : Fin N) (c : CutRing) (hc : cutFraction c ∈ Set.range e) (k : ℤ)
    (j : Fin 2) (x y : GenericSquare a)
    (hx : ordinary (e i.castSucc)≤coordinate j x ∧ coordinate j x<ordinary (e i.succ))
    (hy : ordinary (e i.castSucc)≤coordinate j y ∧ coordinate j y<ordinary (e i.succ)) :
    coordinate j x+(k:ℝ)<ordinary c ↔ coordinate j y+(k:ℝ)<ordinary c := by
  rcases finite_grid_endpoint_sides e he hzero hlast i c hc k with hh | hh
  · have h₁ : ¬coordinate j x+(k:ℝ)<ordinary c := by linarith [hx.1]
    have h₂ : ¬coordinate j y+(k:ℝ)<ordinary c := by linarith [hy.1]
    exact iff_of_false h₁ h₂
  · exact iff_of_true (by linarith [hx.2]) (by linarith [hy.2])

theorem refinedGridRectangle_interval_constant {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (j : Fin 2) (u v : CutRing)
    (hu : cutFraction u ∈ Set.range e) (hv : cutFraction v ∈ Set.range e)
    (huv : ordinary u≤ordinary v) (hlen : ordinary v-ordinary u<1)
    (x y : GenericSquare a)
    (hx : x ∈ (refinedGridRectangle a N e cell).val)
    (hy : y ∈ (refinedGridRectangle a N e cell).val) :
    x ∈ (coordinateInterval a j u v).val ↔ y ∈ (coordinateInterval a j u v).val := by
  have hx' := (refinedGridRectangle_mem e he hzero hlast hmesh cell x).mp hx j
  have hy' := (refinedGridRectangle_mem e he hzero hlast hmesh cell y).mp hy j
  change x ∈ coordinateBetween a j u v ↔ y ∈ coordinateBetween a j u v
  rw [mem_coordinateBetween_iff j u v huv hlen,mem_coordinateBetween_iff j u v huv hlen]
  apply exists_congr
  intro k
  have h₁ := finite_grid_endpoint_decision e he hzero hlast (cell j) u hu k j x y hx' hy'
  have h₂ := finite_grid_endpoint_decision e he hzero hlast (cell j) v hv k j x y hx' hy'
  rw [← not_lt,← not_lt (a := coordinate j y+(k:ℝ))]
  exact and_congr (not_congr h₁) h₂

end RefinedEndpointDecisions

section ClosedRefinementContainment

theorem finite_grid_interval_lift {N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (i : Fin N) (u v : CutRing)
    (hu : cutFraction u ∈ Set.range e) (hv : cutFraction v ∈ Set.range e)
    (x : ℝ) (hx : ordinary (e i.castSucc)≤x ∧ x<ordinary (e i.succ))
    (k : ℤ) (hk : ordinary u≤x+(k:ℝ) ∧ x+(k:ℝ)<ordinary v) :
    ordinary u≤ordinary (e i.castSucc)+(k:ℝ) ∧ ordinary (e i.succ)+(k:ℝ)≤ordinary v := by
  constructor
  · rcases finite_grid_endpoint_sides e he hzero hlast i u hu k with hh | hh
    · linarith
    · linarith [hx.2,hk.1]
  · rcases finite_grid_endpoint_sides e he hzero hlast i v hv k with hh | hh
    · linarith [hx.1,hk.2]
    · linarith

theorem refinedGridRectangle_nonempty {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) : (refinedGridRectangle a N e cell).val.Nonempty := by
  let O : Set (ℝ × ℝ) := (Set.Ioo (ordinary (e (cell 0).castSucc)) (ordinary (e (cell 0).succ))) ×ˢ
    (Set.Ioo (ordinary (e (cell 1).castSucc)) (ordinary (e (cell 1).succ)))
  have hO : IsOpen O := isOpen_Ioo.prod isOpen_Ioo
  have hne : O.Nonempty := Set.Nonempty.prod
    (Set.nonempty_Ioo.mpr (he (Fin.castSucc_lt_succ (i := cell 0))))
    (Set.nonempty_Ioo.mpr (he (Fin.castSucc_lt_succ (i := cell 1))))
  obtain ⟨p,hp,hg⟩ := (avoidsCuts_dense a).inter_open_nonempty O hO hne
  have hbounds (j : Fin 2) : 0≤ordinary (e (cell j).castSucc) ∧ ordinary (e (cell j).succ)≤1 := by
    constructor
    · have hh := he.monotone (Fin.zero_le (cell j).castSucc); simpa only [hzero,map_zero] using hh
    · have hh := he.monotone (Fin.le_last (cell j).succ); simpa only [hlast,map_one] using hh
  have hsq : p.1 ∈ Set.Ico (0:ℝ) 1 ∧ p.2 ∈ Set.Ico (0:ℝ) 1 :=
    ⟨⟨(hbounds 0).1.trans hp.1.1.le,hp.1.2.trans_le (hbounds 0).2⟩,
     ⟨(hbounds 1).1.trans hp.2.1.le,hp.2.2.trans_le (hbounds 1).2⟩⟩
  let x : GenericSquare a := ⟨p,hsq.1,hsq.2,hg⟩
  refine ⟨x,(refinedGridRectangle_mem e he hzero hlast hmesh cell x).mpr ?_⟩
  intro j
  fin_cases j
  · exact ⟨hp.1.1.le,hp.1.2⟩
  · exact ⟨hp.2.1.le,hp.2.2⟩

theorem refinedGridRectangle_closed_lift {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (u v : Fin 2 → CutRing)
    (hu : ∀ j, cutFraction (u j) ∈ Set.range e) (hv : ∀ j, cutFraction (v j) ∈ Set.range e)
    (huv : ∀ j, ordinary (u j)≤ordinary (v j))
    (hlen : ∀ j, ordinary (v j)-ordinary (u j)<1)
    (x : GenericSquare a) (hx : x ∈ (refinedGridRectangle a N e cell).val)
    (hR : x ∈ (coordinateRectangle a u v).val) :
    ∃ k : Fin 2 → ℤ, ∀ j,
      ordinary (u j)≤ordinary (e (cell j).castSucc)+(k j:ℝ) ∧
      ordinary (e (cell j).succ)+(k j:ℝ)≤ordinary (v j) := by
  have hp (j : Fin 2) : x ∈ coordinateBetween a j (u j) (v j) := by
    fin_cases j
    · exact hR.1
    · exact hR.2
  have hh (j : Fin 2) := (mem_coordinateBetween_iff j (u j) (v j) (huv j) (hlen j) x).mp (hp j)
  choose k hk using hh
  exact ⟨k,fun j => finite_grid_interval_lift e he hzero hlast (cell j) (u j) (v j)
    (hu j) (hv j) (coordinate j x)
    ((refinedGridRectangle_mem e he hzero hlast hmesh cell x).mp hx j) (k j) (hk j)⟩

end ClosedRefinementContainment

section CommonTranslatedGrid

theorem refinedGridRectangle_translated_window {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (v : CutRing × CutRing)
    (hcuts : ∀ j : Fin 2, ∀ i : Fin (n+1),
      cutFraction (windowCut n (q j) i+pointCoordinate v j) ∈ Set.range e) :
    ∃ old : Fin 2 → Fin n, ∃ k : Fin 2 → ℤ, ∀ j,
      ordinary (windowCut n (q j) (old j).castSucc+pointCoordinate v j)≤
        ordinary (e (cell j).castSucc)+(k j:ℝ) ∧
      ordinary (e (cell j).succ)+(k j:ℝ)≤
        ordinary (windowCut n (q j) (old j).succ+pointCoordinate v j) := by
  obtain ⟨x,hx⟩ := refinedGridRectangle_nonempty (a := a) e he hzero hlast hmesh cell
  obtain ⟨old,ho⟩ := windowRectangle_cover n hn q (translate a (-v) x)
  have hR : x ∈ (spatialTranslate v (windowRectangle a n q old)).val := ho
  rw [windowRectangle,spatialTranslate_coordinateRectangle] at hR
  have hpos : (200:ℝ)<n := by exact_mod_cast (by omega : 200<n)
  have hlen (j) : ordinary (windowCut n (q j) (old j).succ+pointCoordinate v j)-
      ordinary (windowCut n (q j) (old j).castSucc+pointCoordinate v j)<1 := by
    simp only [map_add,add_sub_add_right_eq_sub]
    exact (windowCut_mesh n (q j) (old j)).trans_lt ((div_lt_one (by linarith)).mpr hpos)
  have hle (j) : ordinary (windowCut n (q j) (old j).castSucc+pointCoordinate v j)≤
      ordinary (windowCut n (q j) (old j).succ+pointCoordinate v j) := by
    simp only [map_add,add_le_add_iff_right]
    exact (windowCut_strictMono n (q j) (Fin.castSucc_lt_succ (i := old j))).le
  exact ⟨old,refinedGridRectangle_closed_lift e he hzero hlast hmesh cell _ _
    (fun j => hcuts j _) (fun j => hcuts j _) hle hlen x hx (by simpa only [pointCoordinate] using hR)⟩

theorem common_translated_grid {ι : Type*} [Fintype ι]
    (S : Finset CutRing) (n : ℕ) (hn : 201≤n)
    (size : ι → ℕ) (_hs : ∀ i, 201 ≤ size i) (q : ι → Fin 2 → ℤ) (v : ι → CutRing × CutRing) :
    ∃ N : ℕ, 0<N ∧ ∃ e : Fin (N+1) → CutRing,
      StrictMono (fun i => ordinary (e i)) ∧ e 0=0 ∧ e (Fin.last N)=1 ∧
      (∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)≤200/(n:ℝ)) ∧
      (∀ c ∈ S, cutFraction c ∈ Set.range e) ∧
      (∀ i, ∀ j : Fin 2, ∀ k : Fin (size i+1),
        cutFraction (windowCut (size i) (q i j) k+pointCoordinate (v i) j) ∈ Set.range e) ∧
      (∀ i : Fin N, ∃ k : Fin n,
        ordinary (windowCut n 0 k.castSucc)≤ordinary (e i.castSucc) ∧
        ordinary (e i.succ)≤ordinary (windowCut n 0 k.succ)) := by
  classical
  let U : Finset CutRing := S ∪ Finset.univ.biUnion (fun i : ι =>
    Finset.univ.biUnion (fun j : Fin 2 => (Finset.univ : Finset (Fin (size i+1))).image
      (fun k => windowCut (size i) (q i j) k+pointCoordinate (v i) j)))
  obtain ⟨N,hN,e,he,hzero,hlast,hcuts,hfine⟩ := finite_refining_grid U n (by omega)
  have href := finite_grid_refines_window (by omega : 0<n) e he hzero hlast hfine
  refine ⟨N,hN,e,he,hzero,hlast,?_,?_,?_,href⟩
  · intro i
    obtain ⟨k,hk₁,hk₂⟩ := href i
    have hm := windowCut_mesh n 0 k
    linarith
  · intro c hc
    exact hcuts c (Finset.mem_union_left _ hc)
  · intro i j k
    apply hcuts
    simp only [U,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,Finset.mem_image,true_and]
    exact Or.inr ⟨i,j,k,rfl⟩

end CommonTranslatedGrid

end SimpleAmenable
end
end

end OAI
