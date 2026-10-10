import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CompactCommonRefinement

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section RefinementNeighborhoods

theorem refinedGridRectangle_subset_translated_window {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (v : CutRing × CutRing)
    (hcuts : ∀ j : Fin 2, ∀ i : Fin (n+1),
      cutFraction (windowCut n (q j) i+pointCoordinate v j) ∈ Set.range e) :
    ∃ old : Fin 2 → Fin n,
      refinedGridRectangle a N e cell ≤ spatialTranslate v (windowRectangle a n q old) := by
  obtain ⟨old,k,hk⟩ := refinedGridRectangle_translated_window (a := a) e he hzero hlast hmesh cell n hn q v hcuts
  refine ⟨old,?_⟩
  intro p hp
  have hpm := (refinedGridRectangle_mem e he hzero hlast hmesh cell p).mp hp
  rw [windowRectangle,spatialTranslate_coordinateRectangle]
  have h (j : Fin 2) : p ∈ coordinateBetween a j
      (windowCut n (q j) (old j).castSucc+pointCoordinate v j)
      (windowCut n (q j) (old j).succ+pointCoordinate v j) := by
    have hle : ordinary (windowCut n (q j) (old j).castSucc+pointCoordinate v j)≤
        ordinary (windowCut n (q j) (old j).succ+pointCoordinate v j) := by
      simp only [map_add,add_le_add_iff_right]
      exact (windowCut_strictMono n (q j) (Fin.castSucc_lt_succ (i := old j))).le
    have hlen : ordinary (windowCut n (q j) (old j).succ+pointCoordinate v j)-
        ordinary (windowCut n (q j) (old j).castSucc+pointCoordinate v j)<1 := by
      simp only [map_add,add_sub_add_right_eq_sub]
      have hn' : (200:ℝ)<n := by exact_mod_cast (by omega : 200<n)
      exact (windowCut_mesh n (q j) (old j)).trans_lt ((div_lt_one (by linarith)).mpr hn')
    apply (mem_coordinateBetween_iff j _ _ hle hlen p).mpr
    refine ⟨k j,?_,?_⟩
    · linarith [(hpm j).1,(hk j).1]
    · linarith [(hpm j).2,(hk j).2]
  exact ⟨h 0,h 1⟩

theorem closedRefinedBox_endpoint_near {N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (cell : Fin 2 → Fin N)
    (z : ℝ × ℝ) (δ : ℝ) (h : closedRefinedBox N e cell ⊆ Metric.ball z δ) :
    ∀ k, |ordinary (e (cell k).castSucc)-realCoordinate z k|<δ ∧
      |ordinary (e (cell k).succ)-realCoordinate z k|<δ := by
  have hl : (ordinary (e (cell 0).castSucc),ordinary (e (cell 1).castSucc)) ∈ closedRefinedBox N e cell := by
    intro k
    fin_cases k <;> exact ⟨le_rfl,(he (Fin.castSucc_lt_succ (i := cell _))).le⟩
  have hu : (ordinary (e (cell 0).succ),ordinary (e (cell 1).succ)) ∈ closedRefinedBox N e cell := by
    intro k
    fin_cases k <;> exact ⟨(he (Fin.castSucc_lt_succ (i := cell _))).le,le_rfl⟩
  have hL := h hl
  have hU := h hu
  rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff] at hL hU
  intro k
  fin_cases k
  · exact ⟨hL.1,hU.1⟩
  · exact ⟨hL.2,hU.2⟩

end RefinementNeighborhoods

end SimpleAmenable
end
end

end OAI
