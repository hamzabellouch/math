import OAI.Combinatorics.Ramsey.CycleClique.Construction.LongestPaths

namespace OAI

/-! The endpoint clique is a final segment, and its tail can be reordered. -/

namespace CycleClique.Construction
/-- A nonempty successor-closed subset of a finite interval, excluding
zero, starts immediately after a well-defined boundary index. -/
theorem successor_closed_final_segment {r : ℕ} (P : Fin (r + 1) → Prop)
    (hzero : ¬ P 0) (hlast : P (Fin.last r))
    (hnext : ∀ i : Fin r, P i.castSucc → P i.succ) :
    ∃ t : Fin r, ∀ i : Fin (r + 1), P i ↔ t.val < i.val := by
  classical
  let A : Finset (Fin (r + 1)) := Finset.univ.filter P
  have hA : A.Nonempty := ⟨Fin.last r, by simpa [A] using hlast⟩
  let a := A.min' hA
  have ha : P a := (Finset.mem_filter.mp (A.min'_mem hA)).2
  have hapos : 1 ≤ a.val := by
    by_contra hn
    have heq : a = 0 := by
      apply Fin.ext
      simpa only [Fin.val_zero] using (show a.val = 0 by omega)
    exact hzero (heq ▸ ha)
  have hmin : ∀ i, P i → a.val ≤ i.val := by
    intro i hi
    exact Finset.min'_le A i (by simpa [A] using hi)
  have hup : ∀ j, ∀ hj : j < r + 1, a.val ≤ j → P ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero => intro hj hle; omega
    | succ j ih =>
      intro hj hle
      by_cases heq : a.val = j + 1
      · have heq' : a = ⟨j + 1, hj⟩ := Fin.ext heq
        exact heq' ▸ ha
      · have hjr : j < r := by omega
        have hprev := ih (by omega) (by omega)
        exact hnext ⟨j, hjr⟩ hprev
  refine ⟨⟨a.val - 1, by have := a.isLt; omega⟩, ?_⟩
  intro i
  constructor
  · intro hi
    have := hmin i hi
    dsimp
    omega
  · intro hi
    apply hup i.val i.isLt
    dsimp at hi
    omega

theorem pathEnds_final_segment {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W : Finset V} {r : ℕ}
    (hr : 1 ≤ r) {f : Fin (r + 1) → V} (hf : IsSpanningPath G x W f)
    (hclique : G.IsClique (pathEnds G x W r : Set V)) :
    ∃ t : Fin r, ∀ i : Fin (r + 1), f i ∈ pathEnds G x W r ↔ t.val < i.val := by
  apply successor_closed_final_segment (fun i => f i ∈ pathEnds G x W r)
  · rw [hf.2.2.1]
    exact start_not_pathEnds hr
  · exact mem_pathEnds.mpr ⟨f, hf, rfl⟩
  · intro i hi
    exact pathEnds_successor_closed hf hclique hi

/-- Permuting the clique tail while fixing its first vertex preserves
the path and all of its prefix. -/
theorem spanningPath_permute_tail {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W E : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath G x W f)
    (t : Fin r) (hfinal : ∀ i : Fin (r + 1), f i ∈ E ↔ t.val < i.val)
    (hclique : G.IsClique (E : Set V)) (σ : Equiv.Perm (Fin (r + 1)))
    (hfix : ∀ i : Fin (r + 1), i.val ≤ t.val + 1 → σ i = i) :
    IsSpanningPath G x W (f ∘ σ) := by
  have htail : ∀ i : Fin (r + 1), t.val < i.val → t.val < (σ i).val := by
    intro i hi
    by_contra hn
    have hs : σ (σ i) = σ i := hfix (σ i) (by omega)
    have heq : i = σ i := σ.injective hs.symm
    have hv := congrArg Fin.val heq
    omega
  refine ⟨hf.1.comp σ.injective, ?_, ?_, ?_⟩
  · intro i
    change G.Adj (f (σ i.castSucc)) (f (σ i.succ))
    by_cases hbefore : i.val ≤ t.val
    · rw [hfix i.castSucc (by change i.val ≤ t.val + 1; omega),
        hfix i.succ (by change i.val + 1 ≤ t.val + 1; omega)]
      exact hf.2.1 i
    · apply hclique ((hfinal _).mpr (htail _ (by simpa using (by omega : t.val < i.val))))
        ((hfinal _).mpr (htail _ (by simp; omega)))
      intro heq
      have hidx := σ.injective (hf.1 heq)
      have hv := congrArg Fin.val hidx
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega
  · change f (σ 0) = x
    rw [hfix 0 (by simp)]
    exact hf.2.2.1
  · ext v
    constructor
    · rintro ⟨i, rfl⟩
      rw [← hf.2.2.2]
      exact ⟨σ i, rfl⟩
    · intro hv
      rw [← hf.2.2.2] at hv
      obtain ⟨i, rfl⟩ := hv
      exact ⟨σ.symm i, by simp⟩

/-- Any tail vertex other than the first can be made last while the
prefix and the first tail vertex stay fixed. -/
theorem spanningPath_swap_tail {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W E : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath G x W f)
    (t : Fin r) (hfinal : ∀ i : Fin (r + 1), f i ∈ E ↔ t.val < i.val)
    (hclique : G.IsClique (E : Set V)) (i : Fin (r + 1))
    (hi : t.val + 1 < i.val) :
    ∃ g : Fin (r + 1) → V, IsSpanningPath G x W g ∧
      g (Fin.last r) = f i ∧
      ∀ j : Fin (r + 1), j.val ≤ t.val + 1 → g j = f j := by
  classical
  let σ := Equiv.swap i (Fin.last r)
  have hfix : ∀ j : Fin (r + 1), j.val ≤ t.val + 1 → σ j = j := by
    intro j hj
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      have := congrArg Fin.val h
      omega
    · intro h
      have := congrArg Fin.val h
      simp only [Fin.val_last] at this
      have := i.isLt
      omega
  exact ⟨f ∘ σ, spanningPath_permute_tail hf t hfinal hclique σ hfix,
    by simp [σ], fun j hj => congrArg f (hfix j hj)⟩

/-- Every endpoint except the first vertex of the fixed clique tail
has no neighbour in the preceding prefix except its attachment vertex. -/
theorem partial_endpoint_attachment {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath G x W f)
    (t : Fin r)
    (hfinal : ∀ i : Fin (r + 1), f i ∈ pathEnds G x W r ↔ t.val < i.val)
    (hclique : G.IsClique (pathEnds G x W r : Set V))
    (hneighbors : ∀ e ∈ pathEnds G x W r, ∀ v, G.Adj e v → v ∈ W) :
    ∀ w ∈ pathEnds G x W r, w ≠ f t.succ →
      ∀ v, G.Adj w v → v ∈ pathEnds G x W r ∨ v = f t.castSucc := by
  intro w hw hwfirst v hwv
  have hwW : w ∈ (W : Set V) := pathEnds_subset G x W r hw
  rw [← hf.2.2.2] at hwW
  obtain ⟨i, hiw⟩ := hwW
  have hitail : t.val < i.val := (hfinal i).mp (hiw ▸ hw)
  have hi : t.val + 1 < i.val := by
    have hneq : i ≠ t.succ := fun h => hwfirst (hiw.symm.trans (congrArg f h))
    have hval : i.val ≠ t.val + 1 := fun h => hneq (Fin.ext h)
    omega
  obtain ⟨g, hg, hglast, hgfix⟩ := spanningPath_swap_tail hf t hfinal hclique i hi
  by_cases hv : v ∈ pathEnds G x W r
  · exact Or.inl hv
  · right
    have hvW : v ∈ (W : Set V) := hneighbors w hw v hwv
    rw [← hf.2.2.2] at hvW
    obtain ⟨j, hjv⟩ := hvW
    have hjbefore : j.val ≤ t.val := by
      by_contra hn
      exact hv (hjv ▸ (hfinal j).mpr (by omega))
    by_cases heq : j.val = t.val
    · have hj : j = t.castSucc := Fin.ext heq
      exact hjv.symm.trans (congrArg f hj)
    · let p : Fin r := ⟨j.val, by have := t.isLt; omega⟩
      have hgp : g p.castSucc = v := (hgfix p.castSucc (by dsimp [p]; omega)).trans
        ((congrArg f (Fin.ext rfl)).trans hjv)
      have hrot := successor_mem_pathEnds hg p (by rw [hglast, hiw, hgp]; exact hwv)
      rw [hgfix p.succ (by dsimp [p]; omega)] at hrot
      have hbound := (hfinal p.succ).mp hrot
      dsimp [p] at hbound
      omega

end CycleClique.Construction

end OAI
