import OAI.Combinatorics.Ramsey.CycleClique.Construction.BallSeparation
import OAI.Combinatorics.Ramsey.CycleClique.Construction.WalkCycle

namespace OAI

/-! Required-path constraints and inheritance, including the parameter-zero
edge case, from manuscript Lemmas `finite:required-path-rule` and
`finite:inheritance`. -/

namespace CycleClique.Construction
variable {V : Type*} {G : SimpleGraph V}

/-- A simple outside path with `d` internal vertices. Parameter zero is
the joining edge; positive parameters agree with the boundary-graph version. -/
def OutsidePath (G : SimpleGraph V) (X : Set V) (x y : V) (d : ℕ) : Prop :=
  ∃ p : G.Walk x y, p.IsPath ∧ p.length = d + 1 ∧
    ∀ v ∈ p.support, v ∈ X → v = x ∨ v = y

theorem outsidePath_zero {X : Set V} {x y : V} :
    OutsidePath G X x y 0 ↔ G.Adj x y := by
  constructor
  · rintro ⟨p, _, hp, _⟩
    exact p.adj_of_length_eq_one hp
  · intro h
    refine ⟨h.toWalk, h.isPath_toWalk, rfl, ?_⟩
    intro v hv _
    simpa using hv

theorem outsidePath_one_of_common_neighbor {X : Set V} {x y u : V}
    (hxy : x ≠ y) (hxu : G.Adj x u) (huy : G.Adj u y) (hu : u ∉ X) :
    OutsidePath G X x y 1 := by
  have hchain : [x, u, y].IsChain G.Adj := by simpa using And.intro hxu huy
  let p : G.Walk x y := SimpleGraph.Walk.ofSupport [x, u, y] (by simp) hchain
  have hsupp : p.support = [x, u, y] := SimpleGraph.Walk.support_ofSupport (by simp) hchain
  have hlen : p.length = 2 := SimpleGraph.Walk.length_ofSupport (by simp) hchain
  refine ⟨p, ?_, ?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.mk'
    rw [hsupp]
    simp [hxy, hxu.ne, huy.ne]
  · exact hlen
  · intro v hv hvX
    simp only [hsupp, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact False.elim (hu hvX)
    · exact Or.inr rfl

def boundaryHom (G : SimpleGraph V) (X : Set V) : boundaryGraph G X →g G where
  toFun := id
  map_rel' := fun h => h.1

theorem PositiveOutsidePath.toOutside {X : Set V} {x y : V} {d : ℕ}
    (h : PositiveOutsidePath G X x y d) : OutsidePath G X x y d := by
  obtain ⟨p, hp, hlen, hsupp⟩ := h
  let f := boundaryHom G X
  refine ⟨p.map f, hp.map Function.injective_id, ?_, ?_⟩
  · exact (SimpleGraph.Walk.length_map f p).trans hlen
  · intro v hv hvX
    have hv' : v ∈ p.support := by simpa [f, boundaryHom] using hv
    exact hsupp v hv' hvX

theorem OutsidePath.of_enlargement {X X' : Set V} {x y : V} {d : ℕ}
    (hXX' : X ⊆ X') (h : OutsidePath G X' x y d) : OutsidePath G X x y d := by
  obtain ⟨p, hp, hlen, hsupp⟩ := h
  exact ⟨p, hp, hlen, fun v hv hvX => hsupp v hv (hXX' hvX)⟩

theorem OutsidePath.reverse {X : Set V} {x y : V} {d : ℕ}
    (h : OutsidePath G X x y d) : OutsidePath G X y x d := by
  obtain ⟨p, hp, hlen, hsupp⟩ := h
  refine ⟨p.reverse, hp.reverse, by simpa using hlen, ?_⟩
  intro v hv hvX
  exact (hsupp v (by simpa using hv) hvX).symm

theorem outsidePath_forbidden_enlargement {X X' : Set V} {x y : V} {d : ℕ}
    (hXX' : X ⊆ X') (h : ¬ OutsidePath G X x y d) : ¬ OutsidePath G X' x y d :=
  fun hp => h (hp.of_enlargement hXX')

/-- Extract the actual internal vertex list. Its vertices avoid `X`,
and its length is exactly the outside parameter. -/
theorem OutsidePath.interior {X : Set V} {x y : V} {d : ℕ}
    (h : OutsidePath G X x y d) :
    ∃ J : List V, J.Nodup ∧ J.length = d ∧ (∀ z ∈ J, z ∉ X) ∧
      (x :: (J ++ [y])).IsChain G.Adj := by
  obtain ⟨p, hp, hlen, hsupp⟩ := h
  cases p with
  | nil => simp at hlen
  | cons hxy p =>
    let J := p.support.dropLast
    have hsuffix : J ++ [y] = p.support := by
      simpa only [J, p.getLast_support] using
        List.dropLast_concat_getLast p.support_ne_nil
    have hnd : (x :: (J ++ [y])).Nodup := by
      rw [hsuffix]
      exact hp.support_nodup
    have hJ : J.Nodup := (List.nodup_append'.mp (List.nodup_cons.mp hnd).2).1
    have hJlen : J.length = d := by
      simp only [SimpleGraph.Walk.length_cons] at hlen
      simp only [J, List.length_dropLast, SimpleGraph.Walk.length_support]
      omega
    refine ⟨J, hJ, hJlen, ?_, ?_⟩
    · intro z hz hzX
      have hzsupport : z ∈ (SimpleGraph.Walk.cons hxy p).support := by
        simp only [SimpleGraph.Walk.support_cons, ← hsuffix]
        exact List.mem_cons.mpr (Or.inr (List.mem_append_left _ hz))
      rcases hsupp z hzsupport hzX with rfl | rfl
      · exact (List.nodup_cons.mp hnd).1 (List.mem_append_left _ hz)
      · exact List.disjoint_left.mp
          (List.nodup_append'.mp (List.nodup_cons.mp hnd).2).2.2 hz (by simp)
    · rw [hsuffix]
      exact (SimpleGraph.Walk.cons hxy p).isChain_adj_support

private theorem start_not_mem_support_tail {x y : V} {p : G.Walk x y}
    (hp : p.IsPath) : x ∉ p.support.tail := by
  have hnd := hp.support_nodup
  rw [← p.cons_tail_support] at hnd
  exact (List.nodup_cons.mp hnd).1

/-- A required path lies in `X`, while the internal vertices of the
outside path avoid `X`; joining the two gives the exact cycle length. -/
theorem hasCycle_of_required_outside_path {X : Set V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (hpX : ∀ v ∈ p.support, v ∈ X)
    {d : ℕ} (houtside : OutsidePath G X x y d)
    (hlen : 2 ≤ p.length ∨ 1 ≤ d) : HasCycle G (p.length + (d + 1)) := by
  obtain ⟨q, hq, hqlen, hqX⟩ := houtside
  have hqr : q.reverse.IsPath := hq.reverse
  have hdis : p.support.tail.Disjoint q.reverse.support.tail := by
    apply List.disjoint_left.mpr
    intro v hvp hvq
    have hvp' : v ∈ p.support := List.mem_of_mem_tail hvp
    have hvq' : v ∈ q.support := by
      simpa using (List.mem_of_mem_tail hvq : v ∈ q.reverse.support)
    rcases hqX v hvq' (hpX v hvp') with rfl | rfl
    · exact start_not_mem_support_tail hp hvp
    · exact start_not_mem_support_tail hqr hvq
  have hc := hp.isCycle_append hqr hdis (by
    rcases hlen with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by simpa [hqlen] using (show 1 < d + 1 by omega)))
  have hcycle := hasCycle_of_isCycle hc
  simpa [hqlen] using hcycle

/-- Every simple required path of length `ℓ≤k` excludes exactly the
outside parameter `k-ℓ`. This also covers a required path of length `k`
and a hypothetical joining edge. -/
theorem required_path_forbids {X : Set V} {x y : V} {k : ℕ}
    (hk : 3 ≤ k) (hcycle : ¬ HasCycle G (k + 1))
    (p : G.Walk x y) (hp : p.IsPath) (hpX : ∀ v ∈ p.support, v ∈ X)
    (hpos : 1 ≤ p.length) (hbound : p.length ≤ k) :
    ¬ OutsidePath G X x y (k - p.length) := by
  intro h
  have hc := hasCycle_of_required_outside_path p hp hpX h
    (show 2 ≤ p.length ∨ 1 ≤ k - p.length by omega)
  exact hcycle (by convert hc using 1; omega)

end CycleClique.Construction

end OAI
