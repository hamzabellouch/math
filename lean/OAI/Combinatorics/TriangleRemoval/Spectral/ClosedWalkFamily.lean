import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.ClosedWords

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
section TraceBridge
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev closedWalkFamily (r : ℕ) := Σ v : V, {p : G.Walk v v // p.length = r}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in

lemma wordOfWalk_adj {r : ℕ} {a : V} (p : G.Walk a a) (hp : p.length = r)
    (i j : Fin r) (hij : (SimpleGraph.cycleGraph r).Adj i j) :
    G.Adj (p.getVert i.val) (p.getVert j.val) := by
  obtain ⟨x,hx⟩ := i
  obtain ⟨y,hy⟩ := j
  have hne : x ≠ y := by
    intro h
    subst y
    exact hij.ne rfl
  wlog hgt : x > y generalizing x y
  · exact (this y hy x hx hij.symm hne.symm (by omega)).symm
  rcases SimpleGraph.cycleGraph_adj'.mp hij with h | h
  · rw [Fin.sub_val_of_le (show (⟨y, hy⟩ : Fin r) ≤ ⟨x, hx⟩ from hgt.le)] at h
    dsimp only at h
    have heq : x = y+1 := by omega
    subst x
    exact (p.adj_getVert_succ (by omega : y < p.length)).symm
  · rw [Fin.coe_sub_iff_lt.mpr hgt] at h
    dsimp only at h
    have hx' : x = r-1 := by omega
    have hy' : y = 0 := by omega
    subst x; subst y
    have hlast := p.adj_getVert_succ (by omega : r-1 < p.length)
    simpa only [show r-1+1 = p.length by omega, SimpleGraph.Walk.getVert_length,
      SimpleGraph.Walk.getVert_zero] using hlast

noncomputable def wordOfWalk {r : ℕ} (p : closedWalkFamily G r) : closedWords G r :=
  ⟨fun i => p.2.1.getVert i.val, by
    classical
    simp only [closedWords, Finset.mem_filter, Finset.mem_univ, true_and]
    exact wordOfWalk_adj G p.2.1 p.2.2⟩

omit [DecidableEq V] in
lemma wordOfWalk_injective {r : ℕ} (hr : 0 < r) :
    Function.Injective (wordOfWalk (G := G) (r := r)) := by
  intro p q hpq
  obtain ⟨a,p,hp⟩ := p
  obtain ⟨b,q,hq⟩ := q
  have hword : (fun i : Fin r => p.getVert i.val) = (fun i : Fin r => q.getVert i.val) :=
    Subtype.ext_iff.mp hpq
  have hab : a = b := by simpa using congrFun hword ⟨0,hr⟩
  subst b
  apply congrArg (Sigma.mk a)
  apply Subtype.ext
  apply SimpleGraph.Walk.ext_getVert_le_length (hp.trans hq.symm)
  intro k hk
  by_cases hkr : k < r
  · exact congrFun hword ⟨k,hkr⟩
  · have heq : k = r := by omega
    subst k
    simpa only [hp, hq] using p.getVert_length.trans q.getVert_length.symm

noncomputable def walkOfWord (n : ℕ) (f : closedWords G (n+3)) :
    closedWalkFamily G (n+3) := by
  let h : SimpleGraph.cycleGraph (n+3) →g G := ⟨f.val, by
    have hf := f.property
    simpa only [closedWords, Finset.mem_filter, Finset.mem_univ, true_and] using hf⟩
  exact ⟨f.val 0, (SimpleGraph.cycleGraph.cycle n).map h, by
    change ((SimpleGraph.cycleGraph.cycle n).map h).length = n+3
    rw [SimpleGraph.Walk.length_map, SimpleGraph.cycleGraph.length_cycle]⟩

omit [DecidableEq V] in
lemma walkOfWord_injective (n : ℕ) : Function.Injective (walkOfWord G n) := by
  intro f g hfg
  apply Subtype.ext
  funext i
  let k := (SimpleGraph.cycleGraph.cycle n).support.idxOf i
  have hk := (SimpleGraph.cycleGraph.cycle n).getVert_support_idxOf
    (canonical_cycle_spanning n i)
  have hget := congrArg (fun w : closedWalkFamily G (n+3) => w.2.1.getVert k) hfg
  simpa [walkOfWord, SimpleGraph.Walk.getVert_map, k, hk] using hget

theorem trace_adjMatrix_eq_closedWords (n : ℕ) :
    Matrix.trace (G.adjMatrix ℕ ^ (n+3)) = (closedWords G (n+3)).card := by
  have hcard : Fintype.card (closedWalkFamily G (n+3)) =
      Fintype.card (closedWords G (n+3)) := le_antisymm
    (Fintype.card_le_of_injective _ (wordOfWalk_injective G (by omega)))
    (Fintype.card_le_of_injective _ (walkOfWord_injective G n))
  rw [Fintype.card_coe] at hcard
  rw [← hcard, Fintype.card_sigma]
  simp only [Matrix.trace, Matrix.diag_apply, SimpleGraph.adjMatrix_pow_apply_eq_card_walk, Nat.cast_id]
  apply Finset.sum_congr rfl
  intro i hi
  exact Fintype.card_congr (Equiv.refl _)

lemma closedWords_card_eq (r : ℕ) :
    (closedWords G r).card = (graphEmbeddings (SimpleGraph.cycleGraph r) G).card +
      (nonsimpleWords G r).card := by
  classical
  have hfun : ((closedWords G r).filter Function.Injective) =
      (graphEmbeddings (SimpleGraph.cycleGraph r) G).image (fun (τ : Fin r ↪ V) => (τ : Fin r → V)) := by
    ext f
    simp only [Finset.mem_filter, closedWords, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hf, hi⟩
      exact ⟨⟨f,hi⟩, (mem_graphEmbeddings _).mpr hf, rfl⟩
    · rintro ⟨τ,hτ,rfl⟩
      exact ⟨(mem_graphEmbeddings τ).mp hτ, τ.injective⟩
  have hc := Finset.card_filter_add_card_filter_not (s := closedWords G r) Function.Injective
  rw [hfun, Finset.card_image_of_injective _ (fun _ _ h => Function.Embedding.ext (congrFun h))] at hc
  exact hc.symm

theorem link_trace_count_bound (n : ℕ) (Δ C : ℕ) (hΔ0 : 1 ≤ Δ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ)
    (hcyc : ∀ b, 3 ≤ b → b < n+3 →
      (graphEmbeddings (SimpleGraph.cycleGraph b) G).card ≤ C * Δ ^ b) :
    Matrix.trace (G.adjMatrix ℕ ^ (n+3)) -
        (graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card ≤
      (n+3) ^ (n+4) * (Fintype.card V * Δ ^ ((n+3)/2) + C * Δ ^ (n+2)) := by
  rw [trace_adjMatrix_eq_closedWords, closedWords_card_eq, Nat.add_sub_cancel_left]
  exact nonsimpleWords_card_le G n Δ C hΔ0 hΔ hcyc

end TraceBridge
end SharpTerminalLeave

end
end

end OAI
