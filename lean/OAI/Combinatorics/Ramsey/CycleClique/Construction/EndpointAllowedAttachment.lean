import OAI.Combinatorics.Ramsey.CycleClique.Construction.EndpointFullAttachment

namespace OAI

/-! Attachment conclusions restricted to neighbours in the longest path's vertex set. -/

namespace CycleClique.Construction
theorem endpoint_attachment_vertex_of_prefix_preserved {V : Type*} [Fintype V]
    {H : SimpleGraph V} {x w v : V} {W : Finset V} {r : ℕ}
    {f g : Fin (r + 1) → V} (hf : IsSpanningPath H x W f) (t : Fin r)
    (hfinal : ∀ i : Fin (r + 1), f i ∈ pathEnds H x W r ↔ t.val < i.val)
    (hg : IsSpanningPath H x W g) (hglast : g (Fin.last r) = w)
    (hfix : ∀ j : Fin (r + 1), j.val ≤ t.val → g j = f j)
    (hvW : v ∈ W) (hwv : H.Adj w v) :
    v ∈ pathEnds H x W r ∨ v = f t.castSucc := by
  by_cases hv : v ∈ pathEnds H x W r
  · exact Or.inl hv
  · right
    have hvW' : v ∈ (W : Set V) := hvW
    rw [← hf.2.2.2] at hvW'
    obtain ⟨j, hjv⟩ := hvW'
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

theorem partial_endpoint_attachment_in_W {V : Type*} [Fintype V]
    {H : SimpleGraph V} {x w v : V} {W : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath H x W f) (t : Fin r)
    (hfinal : ∀ i : Fin (r + 1), f i ∈ pathEnds H x W r ↔ t.val < i.val)
    (hclique : H.IsClique (pathEnds H x W r : Set V))
    (hw : w ∈ pathEnds H x W r) (hne : w ≠ f t.succ)
    (hvW : v ∈ W) (hwv : H.Adj w v) :
    v ∈ pathEnds H x W r ∨ v = f t.castSucc := by
  have hwW : w ∈ (W : Set V) := pathEnds_subset H x W r hw
  rw [← hf.2.2.2] at hwW
  obtain ⟨i, hiw⟩ := hwW
  have hitail : t.val < i.val := (hfinal i).mp (hiw ▸ hw)
  have hi : t.val + 1 < i.val := by
    have hneq : i ≠ t.succ := fun h => hne (hiw.symm.trans (congrArg f h))
    have hval : i.val ≠ t.val + 1 := fun h => hneq (Fin.ext h)
    omega
  obtain ⟨g, hg, hlast, hfix⟩ := spanningPath_swap_tail hf t hfinal hclique i hi
  apply endpoint_attachment_vertex_of_prefix_preserved hf t hfinal hg (hlast.trans hiw)
    (fun j hj => hfix j (by omega)) hvW hwv

theorem full_endpoint_attachment_in_W {V : Type*} [Fintype V]
    {H : SimpleGraph V} {x w v : V} {W : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath H x W f) (t : Fin r)
    (hfinal : ∀ i : Fin (r + 1), f i ∈ pathEnds H x W r ↔ t.val < i.val)
    (hclique : H.IsClique (pathEnds H x W r : Set V))
    (hsecond : ∃ w ∈ pathEnds H x W r,
      w ≠ f t.succ ∧ H.Adj (f t.castSucc) w)
    (hw : w ∈ pathEnds H x W r) (hvW : v ∈ W) (hwv : H.Adj w v) :
    v ∈ pathEnds H x W r ∨ v = f t.castSucc := by
  by_cases heq : w = f t.succ
  · subst w
    obtain ⟨w₁, hw₁, hne, hadj⟩ := hsecond
    obtain ⟨g, hg, hlast, hfix⟩ := spanningPath_first_tail_last hf t hfinal hclique hw₁ hne hadj
    exact endpoint_attachment_vertex_of_prefix_preserved hf t hfinal hg hlast hfix hvW hwv
  · exact partial_endpoint_attachment_in_W hf t hfinal hclique hw heq hvW hwv

end CycleClique.Construction

end OAI
