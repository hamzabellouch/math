import OAI.Combinatorics.Ramsey.CycleClique.Construction.EndpointAttachment

namespace OAI

/-! Rotating from a second attachment extends the prefix exclusion to every endpoint. -/

namespace CycleClique.Construction
theorem spanningPath_first_tail_last {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath G x W f) (t : Fin r)
    (hfinal : ∀ i : Fin (r + 1), f i ∈ pathEnds G x W r ↔ t.val < i.val)
    (hclique : G.IsClique (pathEnds G x W r : Set V))
    {w : V} (hw : w ∈ pathEnds G x W r) (hne : w ≠ f t.succ)
    (hadj : G.Adj (f t.castSucc) w) :
    ∃ g : Fin (r + 1) → V, IsSpanningPath G x W g ∧
      g (Fin.last r) = f t.succ ∧
      ∀ j : Fin (r + 1), j.val ≤ t.val → g j = f j := by
  have hwW : w ∈ (W : Set V) := pathEnds_subset G x W r hw
  rw [← hf.2.2.2] at hwW
  obtain ⟨i, hiw⟩ := hwW
  have hitail : t.val < i.val := (hfinal i).mp (hiw ▸ hw)
  have hi : t.val + 1 < i.val := by
    have hneq : i ≠ t.succ := fun h => hne (hiw.symm.trans (congrArg f h))
    have hval : i.val ≠ t.val + 1 := fun h => hneq (Fin.ext h)
    omega
  obtain ⟨g, hg, hglast, hgfix⟩ := spanningPath_swap_tail hf t hfinal hclique i hi
  have hrot := rotate_path g hg.1 hg.2.1 t (by
    rw [hglast, hiw, hgfix t.castSucc (by simp)]
    exact hadj.symm)
  refine ⟨g ∘ rotationIndex t, ⟨hrot.1, hrot.2.1,
    hrot.2.2.1.trans hg.2.2.1, hrot.2.2.2.2.trans hg.2.2.2⟩,
    hrot.2.2.2.1.trans (hgfix t.succ (by simp)), ?_⟩
  intro j hj
  have hidx : rotationIndex t j = j := by
    apply Fin.ext
    dsimp [rotationIndex]
    split_ifs
    omega
  change g (rotationIndex t j) = f j
  rw [hidx]
  exact hgfix j (by omega)

theorem endpoint_attachment_of_prefix_preserved {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x w : V} {W : Finset V} {r : ℕ}
    {f g : Fin (r + 1) → V} (hf : IsSpanningPath G x W f) (t : Fin r)
    (hfinal : ∀ i : Fin (r + 1), f i ∈ pathEnds G x W r ↔ t.val < i.val)
    (hg : IsSpanningPath G x W g) (hglast : g (Fin.last r) = w)
    (hfix : ∀ j : Fin (r + 1), j.val ≤ t.val → g j = f j)
    (hneighbors : ∀ v, G.Adj w v → v ∈ W) :
    ∀ v, G.Adj w v → v ∈ pathEnds G x W r ∨ v = f t.castSucc := by
  intro v hwv
  by_cases hv : v ∈ pathEnds G x W r
  · exact Or.inl hv
  · right
    have hvW : v ∈ (W : Set V) := hneighbors v hwv
    rw [← hf.2.2.2] at hvW
    obtain ⟨j, hjv⟩ := hvW
    have hjbefore : j.val ≤ t.val := by
      by_contra hn
      exact hv (hjv ▸ (hfinal j).mpr (by omega))
    by_cases heq : j.val = t.val
    · have hj : j = t.castSucc := Fin.ext heq
      exact hjv.symm.trans (congrArg f hj)
    · let p : Fin r := ⟨j.val, by have := t.isLt; omega⟩
      have hgp : g p.castSucc = v := (hfix p.castSucc (by dsimp [p]; omega)).trans
        ((congrArg f (Fin.ext rfl)).trans hjv)
      have hrot := successor_mem_pathEnds hg p (by rw [hglast, hgp]; exact hwv)
      rw [hfix p.succ (by dsimp [p]; omega)] at hrot
      have hbound := (hfinal p.succ).mp hrot
      dsimp [p] at hbound
      omega

/-- Every endpoint has no neighbour outside the endpoint clique other
than the one attachment vertex. -/
theorem full_endpoint_attachment {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath G x W f) (t : Fin r)
    (hfinal : ∀ i : Fin (r + 1), f i ∈ pathEnds G x W r ↔ t.val < i.val)
    (hclique : G.IsClique (pathEnds G x W r : Set V))
    (hneighbors : ∀ e ∈ pathEnds G x W r, ∀ v, G.Adj e v → v ∈ W)
    (hsecond : ∃ w ∈ pathEnds G x W r,
      w ≠ f t.succ ∧ G.Adj (f t.castSucc) w) :
    ∀ w ∈ pathEnds G x W r, ∀ v, G.Adj w v →
      v ∈ pathEnds G x W r ∨ v = f t.castSucc := by
  intro w hw
  by_cases heq : w = f t.succ
  · subst w
    obtain ⟨w₁, hw₁, hne, hadj⟩ := hsecond
    obtain ⟨g, hg, hlast, hfix⟩ := spanningPath_first_tail_last hf t hfinal hclique hw₁ hne hadj
    exact endpoint_attachment_of_prefix_preserved hf t hfinal hg hlast hfix
      (hneighbors _ hw)
  · exact partial_endpoint_attachment hf t hfinal hclique hneighbors w hw heq

end CycleClique.Construction

end OAI
