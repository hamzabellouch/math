import OAI.Combinatorics.Ramsey.CycleClique.Construction.GlobalLongest

namespace OAI

/-! The external-ear consequence of connectivity after each vertex deletion. -/

namespace CycleClique.Construction
theorem ce_external_ear {V : Type*} {H : SimpleGraph V}
    (hconn : H.Connected) (hdel : ∀ a : V, (H.induce {v | v ≠ a}).Connected)
    (S : Finset V) (hS : 2 ≤ S.card) (x : V) (hx : x ∉ S) :
    ∃ l, 2 ≤ l ∧ ∃ g : Fin (l + 1) → V, IsIndexedPath H g ∧
      g 0 ∈ S ∧ g (Fin.last l) ∈ S ∧
      ∀ i : Fin (l + 1), 0 < i.val → i.val < l → g i ∉ S := by
  classical
  let X := H.induce {v | v ∉ S}
  let x' : {v | v ∉ S} := ⟨x, hx⟩
  let W : Set V := {v | ∃ hv : v ∉ S, X.Reachable x' ⟨v, hv⟩}
  have hxW : x ∈ W := ⟨hx, .rfl⟩
  have hWout : ∀ v ∈ W, v ∉ S := fun _ ⟨hv, _⟩ => hv
  have hboundary : ∀ u ∈ W, ∀ v ∉ W, H.Adj u v → v ∈ S := by
    intro u hu v hv huv
    by_contra hvs
    obtain ⟨huS, huR⟩ := hu
    apply hv
    refine ⟨hvs, huR.trans ?_⟩
    exact (show X.Adj ⟨u, huS⟩ ⟨v, hvs⟩ from huv).reachable
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hyW : y ∉ W := fun h => hWout y h hy
  obtain ⟨u, hu, a, haW, hua⟩ := connected_edge_leaving hconn hxW hyW
  have ha : a ∈ S := hboundary u hu a haW hua
  have hxne : x ≠ a := fun h => hx (h ▸ ha)
  have hbex : ∃ b ∈ S, b ≠ a := by
    by_contra! hb
    have hsmall : S.card ≤ 1 := Finset.card_le_one.mpr (fun v hv w hw =>
      (hb v hv).trans (hb w hw).symm)
    omega
  obtain ⟨b, hb, hba⟩ := hbex
  let D := H.induce {v | v ≠ a}
  let W' : Set {v | v ≠ a} := {v | v.val ∈ W}
  have hxb : (⟨x, hxne⟩ : {v | v ≠ a}) ∈ W' := hxW
  have hbb : (⟨b, hba⟩ : {v | v ≠ a}) ∉ W' := fun h => hWout b h hb
  obtain ⟨u', hu', b', hb'W, hu'b'⟩ :=
    connected_edge_leaving (hdel a) hxb hbb
  have hb' : b'.val ∈ S := hboundary u'.val hu' b'.val hb'W hu'b'
  obtain ⟨huS, huR⟩ := hu
  obtain ⟨hu'S, hu'R⟩ := hu'
  obtain ⟨p, hp⟩ := (huR.symm.trans hu'R).exists_isPath
  let f : Fin (p.length + 1) → V := fun i => (p.getVert i.val).val
  have hf : IsIndexedPath H f := by
    refine ⟨?_, ?_⟩
    · intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn (by change i.val ≤ p.length; omega)
        (by change j.val ≤ p.length; omega) (Subtype.ext hij)
    · intro i
      exact p.adj_getVert_succ i.isLt
  have hfout : ∀ i, f i ∉ S := fun i => (p.getVert i.val).property
  have hf0 : f 0 = u := by simp [f]
  have hfl : f (Fin.last p.length) = u'.val := by simp [f]
  have hb'f : b'.val ∉ Set.range f := by
    rintro ⟨i, hi⟩
    exact hfout i (hi ▸ hb')
  have hsnoc : IsIndexedPath H (Fin.snoc f b'.val) :=
    indexedPath_snoc hf hb'f (by rw [hfl]; exact hu'b')
  have hasnoc : a ∉ Set.range (Fin.snoc f b'.val) := by
    rintro ⟨i, hi⟩
    have hn : ∀ k : Fin (p.length + 2), (Fin.snoc f b'.val : Fin (p.length + 2) → V) k ≠ a := by
      intro k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simpa only [Fin.snoc_last] using (show b'.val ≠ a from b'.property)
      · rw [Fin.snoc_castSucc]
        exact fun h => hfout j (h ▸ ha)
    exact hn i hi
  have hstart : H.Adj a ((Fin.snoc f b'.val : Fin (p.length + 2) → V) 0) := by
    have hz : (0 : Fin (p.length + 2)) = (0 : Fin (p.length + 1)).castSucc := rfl
    rw [hz, Fin.snoc_castSucc, hf0]
    exact hua.symm
  refine ⟨p.length + 2, by omega, Fin.cons a (Fin.snoc f b'.val),
    indexedPath_cons hsnoc hasnoc hstart, ?_, ?_, ?_⟩
  · simpa only [Fin.cons_zero] using ha
  · change (Fin.cons a (Fin.snoc f b'.val) : Fin (p.length + 3) → V)
      (Fin.last (p.length + 1)).succ ∈ S
    simpa only [Fin.cons_succ, Fin.snoc_last] using hb'
  · intro i hi hil
    let j : Fin (p.length + 1) := ⟨i.val - 1, by omega⟩
    have hij : j.castSucc.succ = i := by apply Fin.ext; dsimp [j]; omega
    rw [← hij, Fin.cons_succ, Fin.snoc_castSucc]
    exact hfout j

end CycleClique.Construction

end OAI
