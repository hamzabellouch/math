import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CompactFineGrid
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.RefinedEndpointDecisions

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CompactCommonRefinement

def closedRefinedBox (N : ℕ) (e : Fin (N+1) → CutRing) (cell : Fin 2 → Fin N) : Set (ℝ × ℝ) :=
  {p | ∀ j, ordinary (e (cell j).castSucc)≤realCoordinate p j ∧
    realCoordinate p j≤ordinary (e (cell j).succ)}

theorem compact_common_refining_grid {ι κ : Type*} [Fintype ι]
    (S : Finset CutRing) (size : ι → ℕ) (hs : ∀ i, 201 ≤ size i)
    (q : ι → Fin 2 → ℤ) (v : ι → CutRing × CutRing)
    (O : κ → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hcover : Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ⊆ ⋃ i, O i)
    (ε : κ → ℝ) (hε : ∀ i, 0<ε i) :
    ∃ N : ℕ, 0<N ∧ ∃ e : Fin (N+1) → CutRing,
      StrictMono (fun i => ordinary (e i)) ∧ e 0=0 ∧ e (Fin.last N)=1 ∧
      (∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1) ∧
      (∀ c ∈ S, cutFraction c ∈ Set.range e) ∧
      (∀ i, ∀ j : Fin 2, ∀ k : Fin (size i+1),
        cutFraction (windowCut (size i) (q i j) k+pointCoordinate (v i) j) ∈ Set.range e) ∧
      (∀ cell : Fin 2 → Fin N, ∃ k, closedRefinedBox N e cell ⊆ O k ∧
        ∀ j, ordinary (e (cell j).succ)-ordinary (e (cell j).castSucc)<ε k) := by
  obtain ⟨n,hn,hfine⟩ := compact_local_bounds_fine_grid O hO hcover ε hε
  obtain ⟨N,hN,e,he,hzero,hlast,hmesh,hS,hcuts,href⟩ := common_translated_grid S n hn size hs q v
  have hnpos : (200:ℝ)<n := by exact_mod_cast (by omega : 200<n)
  refine ⟨N,hN,e,he,hzero,hlast,fun i => (hmesh i).trans_lt
    ((div_lt_one (by linarith)).mpr hnpos),hS,hcuts,?_⟩
  intro cell
  have hh (j : Fin 2) := href (cell j)
  choose old hold using hh
  obtain ⟨k,hδ,hk⟩ := hfine n le_rfl old
  refine ⟨k,fun p hp => hk (fun j => ⟨(hold j).1.trans (hp j).1,(hp j).2.trans (hold j).2⟩),?_⟩
  intro j
  exact (hmesh (cell j)).trans_lt hδ

end CompactCommonRefinement

end SimpleAmenable
end
end

end OAI
