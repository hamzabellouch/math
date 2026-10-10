import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiniteBallBounds

namespace OAI

/-! Semantic rules for the finite checker's forbidden-parameter matrices:
inheritance, required-path closure and the two extension parameters. -/

namespace CycleClique.Construction
variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

theorem ForbiddenMatrix.Sound.of_subset {M N : ForbiddenMatrix n}
    {X : Finset V} {f : Fin n → V} (hM : M.Sound G X f)
    (hNM : ∀ i j, N i j ⊆ M i j) : N.Sound G X f := by
  intro i j d hd
  exact hM i j d (hNM i j hd)

theorem ForbiddenMatrix.Sound.enlarge_ground {M : ForbiddenMatrix n}
    {X Y : Finset V} {f : Fin n → V} (hM : M.Sound G X f) (hXY : X ⊆ Y) :
    M.Sound G Y f := by
  intro i j d hd
  exact outsidePath_forbidden_enlargement hXY (hM i j d hd)

theorem ForbiddenMatrix.Sound.union {M N : ForbiddenMatrix n}
    {X : Finset V} {f : Fin n → V} (hM : M.Sound G X f) (hN : N.Sound G X f) :
    ForbiddenMatrix.Sound (fun i j => M i j ∪ N i j) G X f := by
  intro i j d hd
  rcases Finset.mem_union.mp hd with hd | hd
  · exact hM i j d hd
  · exact hN i j d hd

theorem ForbiddenMatrix.Sound.reverse {M : ForbiddenMatrix n}
    {X : Finset V} {f : Fin n → V} (hM : M.Sound G X f) :
    ForbiddenMatrix.Sound (fun i j => M j i) G X f := by
  intro i j d hd hp
  exact hM j i d hd hp.reverse

theorem ForbiddenMatrix.Sound.no_required_edge {M : ForbiddenMatrix n}
    {X : Finset V} {f : Fin n → V} (hM : M.Sound G X f)
    {i j : Fin n} (hzero : 0 ∈ M i j) (hij : G.Adj (f i) (f j)) : False :=
  hM i j 0 hzero (outsidePath_zero.mpr hij)

theorem required_indexed_path_forbids {H : SimpleGraph (Fin n)}
    (f : H →g G) (hf : Function.Injective f) {X : Finset V}
    (hfX : ∀ i, f i ∈ X) {i j : Fin n} {k : ℕ}
    (hk : 3 ≤ k) (hcycle : ¬ HasCycle G (k + 1))
    (p : H.Walk i j) (hp : p.IsPath) (hpos : 1 ≤ p.length) (hbound : p.length ≤ k) :
    ¬ OutsidePath G (X : Set V) (f i) (f j) (k - p.length) := by
  have hmapX : ∀ v ∈ (p.map f).support, v ∈ (X : Set V) := by
    intro v hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    exact hfX a
  have hh := required_path_forbids hk hcycle (p.map f) (hp.map hf) hmapX
    (by simpa only [SimpleGraph.Walk.length_map] using hpos)
    (by simpa only [SimpleGraph.Walk.length_map] using hbound)
  simpa only [SimpleGraph.Walk.length_map] using hh

theorem outsidePath_one_iff_common_neighbor {X : Set V} {x y : V} (hxy : x ≠ y) :
    OutsidePath G X x y 1 ↔ ∃ u, u ∉ X ∧ G.Adj x u ∧ G.Adj u y := by
  constructor
  · intro hp
    obtain ⟨J, _, hlen, hout, hchain⟩ := hp.interior
    obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hlen
    refine ⟨u, hout u (by simp), ?_⟩
    simpa using hchain
  · rintro ⟨u, hu, hxu, huy⟩
    exact outsidePath_one_of_common_neighbor hxy hxu huy hu

end CycleClique.Construction

end OAI
