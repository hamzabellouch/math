import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListFinalDegree

namespace OAI

/-! Coarse-cell labels for the actual ordered fork output. Both members of a
fresh mediator pair stay in their actual active center's cell. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped Classical

def CellAligned {β : Type*} (s : State) (cell : ℕ → β) : Prop :=
  ∀ (i : Fin s.2.2.2.length) (j : Fin (groupAt s.2.2.2 i.val).length),
    cell (portAt (groupAt s.2.2.2 i.val) j.val).1=cell i.val

def nextCell {β : Type*} (s : State) (cell : ℕ → β) (v : ℕ) : β :=
  if v<s.1 then cell v else
    cell (((catalog s.2.2.2).drop ((v-s.1)/2)).headD (0,((0,0),(0,0)))).1

theorem nextCell_old {β : Type*} (s : State) (cell : ℕ → β)
    (v : ℕ) (hv : v<s.1) : nextCell s cell v=cell v := by
  simp only [nextCell,hv,ite_true]

theorem nextCell_fresh {β : Type*} (s : State) (h : ValidPorts s.1 s.2.2.2)
    (cell : ℕ → β) (e : Fin (pairCount s.2.2.2)) (b : Fin 2) :
    nextCell s cell (s.1+2*e.val+b.val)=cell (actualSite h e 0).val := by
  have hn : ¬s.1+2*e.val+b.val<s.1 := by omega
  have hd : (s.1+2*e.val+b.val-s.1)/2=e.val := by have := b.isLt; omega
  simp only [nextCell,hn,ite_false,hd,catalog_actualSite h e]

theorem cellAligned_actualSite {β : Type*} (s : State) (h : ValidPorts s.1 s.2.2.2)
    (cell : ℕ → β) (ha : CellAligned s cell) (e : Fin (pairCount s.2.2.2)) (a : Fin 3) :
    cell (actualSite h e a).val=cell (actualSite h e 0).val := by
  fin_cases a
  · rfl
  · exact ha (localPair s.2.2.2 e).1 (localFirst s.2.2.2 e)
  · exact ha (localPair s.2.2.2 e).1 (localSecond s.2.2.2 e)

theorem next_cellAligned {β : Type*} (N : ℚ) (s : State) (h : ValidPorts s.1 s.2.2.2)
    (cell : ℕ → β) (ha : CellAligned s cell) : CellAligned (next N s) (nextCell s cell) := by
  intro i j
  have hj₀ := j.isLt
  generalize hkj : j.val=k at hj₀ ⊢
  clear hkj j
  have hi : i.val<s.2.2.2.length := by simpa only [next_centers] using i.isLt
  have hn : i.val<s.1 := lt_of_lt_of_le hi h.centers
  rw [nextCell_old s cell i.val hn]
  have hg : groupAt (next N s).2.2.2 i.val=nextGroup s.1 (scale N s) s.2.2.2 i.val :=
    next_groupAt _ _ _ _ hi
  have hj : k<(groupAt s.2.2.2 i.val).length/2+(groupAt s.2.2.2 i.val).length%2 := by
    have hj := hj₀
    rw [hg,nextGroup_length] at hj
    exact hj
  rw [hg]
  by_cases hf : k<(groupAt s.2.2.2 i.val).length/2
  · rw [nextGroup_portAt_fresh _ _ _ _ _ hf]
    let p : LocalPair s.2.2.2 := ⟨⟨i.val,hi⟩,⟨k,hf⟩⟩
    let e := pairEquiv s.2.2.2 p
    have he : e.val=pairStart s.2.2.2 i.val+k := pairEquiv_val _ p
    have hh := nextCell_fresh s h cell e 0
    simp only [Fin.val_zero,Nat.add_zero,he] at hh
    rw [hh]
    change cell (localPair s.2.2.2 e).1.val=cell i.val
    have hl : localPair s.2.2.2 e=p := (pairEquiv s.2.2.2).symm_apply_apply p
    rw [hl]
  · rw [nextGroup_portAt_retained _ _ _ _ _ (by omega)]
    let t := 2*((groupAt s.2.2.2 i.val).length/2)+(k-(groupAt s.2.2.2 i.val).length/2)
    have ht : t<(groupAt s.2.2.2 i.val).length := retained_index_lt _ _ hj (by omega)
    rw [nextCell_old s cell _ (h.bounded ⟨i.val,hi⟩ ⟨t,ht⟩)]
    exact ha ⟨i.val,hi⟩ ⟨t,ht⟩

end ContinuumCoulomb.QuantumForkList

end

end OAI
