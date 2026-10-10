import OAI.Combinatorics.Ramsey.CycleClique.Construction.Definitions
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace OAI

/-!
# Outside paths and separated neighbourhood balls

This is manuscript Lemma `path:separation`. The boundary graph deletes
edges with both ends in `X`, so shortening a walk cannot introduce a
direct edge between its two endpoints in `X`.
-/

namespace CycleClique.Construction
variable {V : Type*}

/-- Delete precisely the edges with both ends in the excluded vertex set. -/
def boundaryGraph (G : SimpleGraph V) (X : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (x ∉ X ∨ y ∉ X)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩

/-- A positive-parameter outside path: exactly `d` internal vertices,
all outside `X`. The boundary graph excludes the parameter-zero edge. -/
def PositiveOutsidePath (G : SimpleGraph V) (X : Set V) (x y : V) (d : ℕ) : Prop :=
  ∃ p : (boundaryGraph G X).Walk x y,
    p.IsPath ∧ p.length = d + 1 ∧
    ∀ v ∈ p.support, v ∈ X → v = x ∨ v = y

/-- The ball reached by at most `r` edges after the first outside neighbour
of `x`, with all subsequent vertices outside `X`. -/
def OutsideBall (G : SimpleGraph V) (X : Set V) (x : V) (r : ℕ) : Set V :=
  {v | v ∉ X ∧ ∃ p : (boundaryGraph G X).Walk x v,
    p.length ≤ r + 1 ∧ ∀ w ∈ p.support, w ∈ X → w = x}

theorem OutsideBall.mono {G : SimpleGraph V} {X : Set V} {x : V} {r s : ℕ}
    (hrs : r ≤ s) : OutsideBall G X x r ⊆ OutsideBall G X x s := by
  rintro v ⟨hv, p, hp, hsupp⟩
  exact ⟨hv, p, by omega, hsupp⟩

theorem outsideBall_zero {G : SimpleGraph V} {X : Set V} {x v : V}
    (hx : x ∈ X) : v ∈ OutsideBall G X x 0 ↔ G.Adj x v ∧ v ∉ X := by
  constructor
  · rintro ⟨hv, p, hp, _⟩
    have hlen : p.length = 1 := by
      have hn : p.length ≠ 0 := fun h => hv (p.eq_of_length_eq_zero h ▸ hx)
      omega
    exact ⟨(p.adj_of_length_eq_one hlen).1, hv⟩
  · rintro ⟨h, hv⟩
    refine ⟨hv, (show (boundaryGraph G X).Adj x v from ⟨h, Or.inr hv⟩).toWalk, ?_, ?_⟩
    · simp
    · intro w hw hwX
      change w ∈ [x, v] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rfl
      · exact False.elim (hv hwX)

private theorem outside_path_of_walk [DecidableEq V] {G : SimpleGraph V} {X : Set V}
    {x y : V} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (p : (boundaryGraph G X).Walk x y)
    (hsupp : ∀ v ∈ p.support, v ∈ X → v = x ∨ v = y) :
    ∃ d, 1 ≤ d ∧ d + 1 ≤ p.length ∧ PositiveOutsidePath G X x y d := by
  have hzero : p.bypass.length ≠ 0 := fun h => hxy (p.bypass.eq_of_length_eq_zero h)
  have hone : p.bypass.length ≠ 1 := by
    intro h
    have hadj := p.bypass.adj_of_length_eq_one h
    rcases hadj.2 with h | h
    · exact h hx
    · exact h hy
  have htwo : 2 ≤ p.bypass.length := by omega
  refine ⟨p.bypass.length - 1, by omega, ?_, p.bypass, p.bypass_isPath, by omega, ?_⟩
  · have := p.length_bypass_le_length
    omega
  · intro v hv hvX
    exact hsupp v (p.support_bypass_subset_support hv) hvX

/-- Forbidding the specified positive outside paths separates two balls
both as vertex sets and by the absence of edges between them. -/
theorem outside_balls_separated {G : SimpleGraph V} {X : Set V} {x y : V}
    (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) {r s : ℕ}
    (hforbid : ∀ d, 1 ≤ d → d ≤ r + s + 2 → ¬ PositiveOutsidePath G X x y d) :
    Disjoint (OutsideBall G X x r) (OutsideBall G X y s) ∧
    ∀ u ∈ OutsideBall G X x r, ∀ v ∈ OutsideBall G X y s, ¬ G.Adj u v := by
  classical
  constructor
  · apply Set.disjoint_left.mpr
    rintro z ⟨_, p, hp, hps⟩ ⟨_, q, hq, hqs⟩
    let w := p.append q.reverse
    have hsupp : ∀ v ∈ w.support, v ∈ X → v = x ∨ v = y := by
      intro v hv hvX
      rcases (SimpleGraph.Walk.mem_support_append_iff p q.reverse).mp hv with hv | hv
      · exact Or.inl (hps v hv hvX)
      · exact Or.inr (hqs v (by simpa using hv) hvX)
    obtain ⟨d, hd, hlen, hpath⟩ := outside_path_of_walk hx hy hxy w hsupp
    have hw : w.length ≤ r + s + 2 := by
      simpa [w, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] using
        (show p.length + q.length ≤ r + s + 2 by omega)
    exact hforbid d hd (by omega) hpath
  · rintro u ⟨hu, p, hp, hps⟩ v ⟨hv, q, hq, hqs⟩ hadj
    have hedge : (boundaryGraph G X).Adj u v := ⟨hadj, Or.inl hu⟩
    let w := (p.concat hedge).append q.reverse
    have hsupp : ∀ z ∈ w.support, z ∈ X → z = x ∨ z = y := by
      intro z hz hzX
      rcases (SimpleGraph.Walk.mem_support_append_iff (p.concat hedge) q.reverse).mp hz with hz | hz
      · have hz' : z ∈ p.support ∨ z = v := by simpa using hz
        rcases hz' with hz' | rfl
        · exact Or.inl (hps z hz' hzX)
        · exact False.elim (hv hzX)
      · exact Or.inr (hqs z (by simpa using hz) hzX)
    obtain ⟨d, hd, hlen, hpath⟩ := outside_path_of_walk hx hy hxy w hsupp
    have hw : w.length ≤ r + s + 3 := by
      simpa [w, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_concat,
        SimpleGraph.Walk.length_reverse] using
        (show p.length + 1 + q.length ≤ r + s + 3 by omega)
    exact hforbid d hd (by omega) hpath

/-- The singleton/ball case of the same separation principle. -/
theorem singleton_outside_ball_separated {G : SimpleGraph V} {X : Set V} {x y : V}
    (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) {r : ℕ}
    (hforbid : ∀ d, 1 ≤ d → d ≤ r + 1 → ¬ PositiveOutsidePath G X x y d) :
    ∀ v ∈ OutsideBall G X x r, ¬ G.Adj v y := by
  classical
  rintro v ⟨hv, p, hp, hps⟩ hadj
  have hedge : (boundaryGraph G X).Adj v y := ⟨hadj, Or.inl hv⟩
  let w := p.concat hedge
  have hsupp : ∀ z ∈ w.support, z ∈ X → z = x ∨ z = y := by
    intro z hz hzX
    have hz' : z ∈ p.support ∨ z = y := by simpa [w] using hz
    rcases hz' with hz' | rfl
    · exact Or.inl (hps z hz' hzX)
    · exact Or.inr rfl
  obtain ⟨d, hd, hlen, hpath⟩ := outside_path_of_walk hx hy hxy w hsupp
  have hw : w.length ≤ r + 2 := by simpa [w] using (show p.length + 1 ≤ r + 2 by omega)
  exact hforbid d hd (by omega) hpath

end CycleClique.Construction

end OAI
