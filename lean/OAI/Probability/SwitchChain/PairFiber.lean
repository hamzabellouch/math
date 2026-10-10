import OAI.Probability.SwitchChain.Definitions

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber

variable {V : Type*} [sectionFintypeV : Fintype V]

def Outside (i j w : V) : Prop := w ≠ i ∧ w ≠ j

def edgeBit (G : SimpleGraph V) (u v : V) : Nat := by
  classical
  exact if G.Adj u v then 1 else 0

def key (i j : V) (G : SimpleGraph V) :
    (V → V → Prop) × Prop × (V → Nat) :=
  (fun u v => Outside i j u ∧ Outside i j v ∧ G.Adj u v,
   G.Adj i j, fun w => edgeBit G i w + edgeBit G j w)

def singletonSet (G : SimpleGraph V) (i j : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => Outside i j w ∧ Xor (G.Adj i w) (G.Adj j w))

def leftSet (G : SimpleGraph V) (i j : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => Outside i j w ∧ G.Adj i w ∧ ¬ G.Adj j w)

def commonSet (G : SimpleGraph V) (i j : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => Outside i j w ∧ G.Adj i w ∧ G.Adj j w)

@[simp] theorem mem_singletonSet (G : SimpleGraph V) (i j w : V) :
    w ∈ singletonSet G i j ↔ Outside i j w ∧ Xor (G.Adj i w) (G.Adj j w) := by
  classical
  simp [singletonSet]

@[simp] theorem mem_leftSet (G : SimpleGraph V) (i j w : V) :
    w ∈ leftSet G i j ↔ Outside i j w ∧ G.Adj i w ∧ ¬ G.Adj j w := by
  classical
  simp [leftSet]

@[simp] theorem mem_commonSet (G : SimpleGraph V) (i j w : V) :
    w ∈ commonSet G i j ↔ Outside i j w ∧ G.Adj i w ∧ G.Adj j w := by
  classical
  simp [commonSet]

theorem leftSet_subset_singletonSet (G : SimpleGraph V) (i j : V) :
    leftSet G i j ⊆ singletonSet G i j := by
  intro w hw
  rcases (mem_leftSet G i j w).mp hw with ⟨ho, hi, hj⟩
  exact (mem_singletonSet G i j w).mpr ⟨ho, Or.inl ⟨hi, hj⟩⟩

include sectionFintypeV in
theorem key_count {i j : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H) (w : V) :
    edgeBit G i w + edgeBit G j w = edgeBit H i w + edgeBit H j w := by
  have retainedsectionFintypeV := sectionFintypeV
  exact
  congrFun (congrArg (fun k => k.2.2) h) w

include sectionFintypeV in
theorem key_internal {i j : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H) : G.Adj i j ↔ H.Adj i j := by
  have retainedsectionFintypeV := sectionFintypeV
  exact
  Iff.of_eq (congrArg (fun k => k.2.1) h)

include sectionFintypeV in
theorem key_outside {i j u v : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H) (hu : Outside i j u) (hv : Outside i j v) :
    G.Adj u v ↔ H.Adj u v := by
  have retainedsectionFintypeV := sectionFintypeV
  have hh := congrFun (congrFun (congrArg Prod.fst h) u) v
  change (Outside i j u ∧ Outside i j v ∧ G.Adj u v) =
    (Outside i j u ∧ Outside i j v ∧ H.Adj u v) at hh
  simpa only [hu, hv, true_and] using Iff.of_eq hh

theorem singletonSet_eq_of_key_eq {i j : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H) : singletonSet G i j = singletonSet H i j := by
  classical
  ext w
  have hc := key_count h w
  by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
    by_cases hi : H.Adj i w <;> by_cases hj : H.Adj j w <;>
    simp_all [edgeBit, Xor]

theorem commonSet_eq_of_key_eq {i j : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H) : commonSet G i j = commonSet H i j := by
  classical
  ext w
  have hc := key_count h w
  by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
    by_cases hi : H.Adj i w <;> by_cases hj : H.Adj j w <;>
    simp_all [edgeBit]

theorem key_left_adj {i j w : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H)
    (hl : leftSet G i j = leftSet H i j) (ho : Outside i j w) :
    G.Adj i w ↔ H.Adj i w := by
  classical
  have hc := key_count h w
  have hm : w ∈ leftSet G i j ↔ w ∈ leftSet H i j := by rw [hl]
  simp only [mem_leftSet] at hm
  by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
    by_cases hi : H.Adj i w <;> by_cases hj : H.Adj j w <;>
    simp_all [edgeBit]

theorem key_right_adj {i j w : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H)
    (hl : leftSet G i j = leftSet H i j) (ho : Outside i j w) :
    G.Adj j w ↔ H.Adj j w := by
  classical
  have hc := key_count h w
  have hm := key_left_adj h hl ho
  by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
    by_cases hi : H.Adj i w <;> by_cases hj : H.Adj j w <;>
    simp_all [edgeBit]

theorem graph_eq_of_key_leftSet_eq {i j : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H)
    (hl : leftSet G i j = leftSet H i j) : G = H := by
  classical
  ext u v
  by_cases ui : u = i
  · subst u
    by_cases vi : v = i
    · subst v; simp
    by_cases vj : v = j
    · subst v; exact key_internal h
    exact key_left_adj h hl ⟨vi, vj⟩
  by_cases uj : u = j
  · subst u
    by_cases vi : v = i
    · subst v; simpa only [G.adj_comm, H.adj_comm] using key_internal h
    by_cases vj : v = j
    · subst v; simp
    exact key_right_adj h hl ⟨vi, vj⟩
  by_cases vi : v = i
  · subst v
    simpa only [G.adj_comm, H.adj_comm] using key_left_adj h hl (show Outside i j u from ⟨ui, uj⟩)
  by_cases vj : v = j
  · subst v
    simpa only [G.adj_comm, H.adj_comm] using key_right_adj h hl (show Outside i j u from ⟨ui, uj⟩)
  exact key_outside h ⟨ui, uj⟩ ⟨vi, vj⟩

include sectionFintypeV in
theorem key_swap (G : SimpleGraph V) (i j : V) : key i j G = key j i G := by
  have retainedsectionFintypeV := sectionFintypeV
  apply Prod.ext
  · funext u v
    apply propext
    dsimp [key, Outside]
    tauto
  · apply Prod.ext
    · exact propext (G.adj_comm i j)
    · funext w
      exact Nat.add_comm _ _

def assemble (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (A B : Finset V)
    (hA : ∀ w ∈ A, Outside i j w)
    (hB : ∀ w ∈ B, Outside i j w) : SimpleGraph V where
  Adj u v :=
    (Outside i j u ∧ Outside i j v ∧ G.Adj u v) ∨
    (((u = i ∧ v = j) ∨ (u = j ∧ v = i)) ∧ G.Adj i j) ∨
    (u = i ∧ v ∈ A) ∨ (v = i ∧ u ∈ A) ∨
    (u = j ∧ v ∈ B) ∨ (v = j ∧ u ∈ B)
  symm := by
    constructor
    intro u v h
    rcases h with h | h | h | h | h | h
    · exact Or.inl ⟨h.2.1, h.1, G.symm.symm u v h.2.2⟩
    · exact Or.inr (Or.inl ⟨by tauto, h.2⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, h.2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩))))
  loopless := by
    constructor
    intro v h
    rcases h with h | h | h | h | h | h
    · exact G.irrefl h.2.2
    · rcases h.1 with ⟨hi, hj⟩ | ⟨hj, hi⟩ <;> exact hij (hi.symm.trans hj)
    · exact (hA v h.2).1 h.1
    · exact (hA v h.2).1 h.1
    · exact (hB v h.2).2 h.1
    · exact (hB v h.2).2 h.1

include sectionFintypeV in
theorem assemble_adj_left (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (A B : Finset V) (hA : ∀ w ∈ A, Outside i j w)
    (hB : ∀ w ∈ B, Outside i j w) {w : V} (hw : Outside i j w) :
    (assemble G i j hij A B hA hB).Adj i w ↔ w ∈ A := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [assemble, Outside, hij, hw.1, hw.2]

include sectionFintypeV in
theorem assemble_adj_right (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (A B : Finset V) (hA : ∀ w ∈ A, Outside i j w)
    (hB : ∀ w ∈ B, Outside i j w) {w : V} (hw : Outside i j w) :
    (assemble G i j hij A B hA hB).Adj j w ↔ w ∈ B := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [assemble, Outside, Ne.symm hij, hw.1, hw.2]

include sectionFintypeV in
theorem assemble_adj_internal (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (A B : Finset V) (hA : ∀ w ∈ A, Outside i j w)
    (hB : ∀ w ∈ B, Outside i j w) :
    (assemble G i j hij A B hA hB).Adj i j ↔ G.Adj i j := by
  have retainedsectionFintypeV := sectionFintypeV
  have hja : j ∉ A := fun h => (hA j h).2 rfl
  have hib : i ∉ B := fun h => (hB i h).1 rfl
  simp [assemble, Outside, hij, Ne.symm hij, hja, hib]

include sectionFintypeV in
theorem assemble_adj_outside (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (A B : Finset V) (hA : ∀ w ∈ A, Outside i j w)
    (hB : ∀ w ∈ B, Outside i j w) {u v : V}
    (hu : Outside i j u) (hv : Outside i j v) :
    (assemble G i j hij A B hA hB).Adj u v ↔ G.Adj u v := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [assemble, hu, hv, hu.1, hu.2, hv.1, hv.2]

def trade (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j) : SimpleGraph V := by
  classical
  refine assemble G i j hij (commonSet G i j ∪ T)
    (commonSet G i j ∪ (singletonSet G i j \ T)) ?_ ?_
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact ((mem_commonSet G i j w).mp hw).1
    · exact ((mem_singletonSet G i j w).mp (hT hw)).1
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact ((mem_commonSet G i j w).mp hw).1
    · exact ((mem_singletonSet G i j w).mp (Finset.mem_sdiff.mp hw).1).1

theorem trade_adj_left (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j)
    {w : V} (hw : Outside i j w) :
    (trade G i j hij T hT).Adj i w ↔ (G.Adj i w ∧ G.Adj j w) ∨ w ∈ T := by
  classical
  unfold trade
  rw [assemble_adj_left _ _ _ _ _ _ _ _ hw]
  simp [hw]

theorem trade_adj_right (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j)
    {w : V} (hw : Outside i j w) :
    (trade G i j hij T hT).Adj j w ↔
      (G.Adj i w ∧ G.Adj j w) ∨ (Xor (G.Adj i w) (G.Adj j w) ∧ w ∉ T) := by
  classical
  unfold trade
  rw [assemble_adj_right _ _ _ _ _ _ _ _ hw]
  simp [hw]

theorem trade_adj_internal (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j) :
    (trade G i j hij T hT).Adj i j ↔ G.Adj i j := by
  unfold trade
  exact assemble_adj_internal _ _ _ _ _ _ _ _

theorem trade_adj_outside (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j)
    {u v : V} (hu : Outside i j u) (hv : Outside i j v) :
    (trade G i j hij T hT).Adj u v ↔ G.Adj u v := by
  unfold trade
  exact assemble_adj_outside _ _ _ _ _ _ _ _ hu hv

include sectionFintypeV in
theorem key_eq_of {i j : V} {G H : SimpleGraph V}
    (ho : ∀ u v, Outside i j u → Outside i j v → (G.Adj u v ↔ H.Adj u v))
    (hi : G.Adj i j ↔ H.Adj i j)
    (hc : ∀ w, edgeBit G i w + edgeBit G j w = edgeBit H i w + edgeBit H j w) :
    key i j G = key i j H := by
  have retainedsectionFintypeV := sectionFintypeV
  apply Prod.ext
  · funext u v
    apply propext
    change (Outside i j u ∧ Outside i j v ∧ G.Adj u v) ↔
      (Outside i j u ∧ Outside i j v ∧ H.Adj u v)
    constructor
    · intro h; exact ⟨h.1, h.2.1, (ho u v h.1 h.2.1).mp h.2.2⟩
    · intro h; exact ⟨h.1, h.2.1, (ho u v h.1 h.2.1).mpr h.2.2⟩
  · exact Prod.ext (propext hi) (funext hc)

theorem key_trade (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j) :
    key i j (trade G i j hij T hT) = key i j G := by
  classical
  apply key_eq_of
  · intro u v hu hv
    exact trade_adj_outside G i j hij T hT hu hv
  · exact trade_adj_internal G i j hij T hT
  · intro w
    by_cases wi : w = i
    · subst w
      have hi := trade_adj_internal G i j hij T hT
      simp only [edgeBit, SimpleGraph.irrefl, ↓reduceIte, zero_add]
      rw [(trade G i j hij T hT).adj_comm, G.adj_comm, hi]
    by_cases wj : w = j
    · subst w
      have hi := trade_adj_internal G i j hij T hT
      simp [edgeBit, hi]
    have ho : Outside i j w := ⟨wi, wj⟩
    have hl := trade_adj_left G i j hij T hT ho
    have hr := trade_adj_right G i j hij T hT ho
    have ht : w ∈ T → Xor (G.Adj i w) (G.Adj j w) :=
      fun hw => ((mem_singletonSet G i j w).mp (hT hw)).2
    simp only [edgeBit, hl, hr]
    by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
      by_cases wt : w ∈ T <;> simp_all [Xor]

theorem leftSet_trade (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j) :
    leftSet (trade G i j hij T hT) i j = T := by
  classical
  ext w
  by_cases ho : Outside i j w
  · have hl := trade_adj_left G i j hij T hT ho
    have hr := trade_adj_right G i j hij T hT ho
    have ht : w ∈ T → Xor (G.Adj i w) (G.Adj j w) :=
      fun hw => ((mem_singletonSet G i j w).mp (hT hw)).2
    simp only [mem_leftSet, ho, true_and, hl, hr]
    by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
      by_cases wt : w ∈ T <;> simp_all [Xor]
  · have ht : w ∉ T := fun hw => ho ((mem_singletonSet G i j w).mp (hT hw)).1
    simp [ho, ht]

end Problem315.PairFiber

end

end OAI
