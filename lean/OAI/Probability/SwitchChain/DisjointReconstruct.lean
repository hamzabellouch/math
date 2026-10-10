import OAI.Probability.SwitchChain.DisjointEncoding

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointEncoding

variable {V : Type*}

def blockEquiv (e : Fin 4 ↪ V) : Fin 4 ⊕ {w : V // Outside e w} ≃ V :=
  Equiv.ofBijective (Sum.elim e Subtype.val) (by
    constructor
    · rintro (a | u) (b | v) h
      · exact congrArg Sum.inl (e.injective h)
      · exact False.elim (v.property a h.symm)
      · exact False.elim (u.property b h)
      · exact congrArg Sum.inr (Subtype.ext h)
    · intro v
      by_cases h : ∃ a, v = e a
      · obtain ⟨a, ha⟩ := h
        exact ⟨Sum.inl a, ha.symm⟩
      · exact ⟨Sum.inr ⟨v, by simpa [Outside] using h⟩, rfl⟩)

@[simp] theorem blockEquiv_inl (e : Fin 4 ↪ V) (a : Fin 4) :
    blockEquiv e (Sum.inl a) = e a := rfl

@[simp] theorem blockEquiv_inr (e : Fin 4 ↪ V) (w : {w : V // Outside e w}) :
    blockEquiv e (Sum.inr w) = w.val := rfl

@[simp] theorem blockEquiv_symm_endpoint (e : Fin 4 ↪ V) (a : Fin 4) :
    (blockEquiv e).symm (e a) = Sum.inl a :=
  (blockEquiv e).symm_apply_apply (Sum.inl a)

@[simp] theorem blockEquiv_symm_outside (e : Fin 4 ↪ V) (w : {w : V // Outside e w}) :
    (blockEquiv e).symm w.val = Sum.inr w :=
  (blockEquiv e).symm_apply_apply (Sum.inr w)

def glueGraph {α β : Type*} (I : SimpleGraph α) (B : α → β → Prop)
    (O : SimpleGraph β) : SimpleGraph (α ⊕ β) where
  Adj u v := match u, v with
    | Sum.inl a, Sum.inl b => I.Adj a b
    | Sum.inl a, Sum.inr w => B a w
    | Sum.inr w, Sum.inl a => B a w
    | Sum.inr u, Sum.inr v => O.Adj u v
  symm := by
    constructor
    rintro (a | u) (b | v) h
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    constructor
    rintro (a | w) h
    · exact I.irrefl h
    · exact O.irrefl h

def reconstruct (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) : SimpleGraph V :=
  (glueGraph I B O).comap (blockEquiv e).symm

@[simp] theorem reconstruct_block_block (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (a b : Fin 4) :
    (reconstruct e I B O).Adj (e a) (e b) ↔ I.Adj a b := by
  simp [reconstruct, SimpleGraph.comap_adj, glueGraph]

@[simp] theorem reconstruct_block_outside (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (a : Fin 4) (w : {w : V // Outside e w}) :
    (reconstruct e I B O).Adj (e a) w.val ↔ B a w := by
  simp [reconstruct, SimpleGraph.comap_adj, glueGraph]

@[simp] theorem reconstruct_outside_block (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (a : Fin 4) (w : {w : V // Outside e w}) :
    (reconstruct e I B O).Adj w.val (e a) ↔ B a w := by
  simp [reconstruct, SimpleGraph.comap_adj, glueGraph]

@[simp] theorem reconstruct_outside_outside (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (u v : {w : V // Outside e w}) :
    (reconstruct e I B O).Adj u.val v.val ↔ O.Adj u v := by
  simp [reconstruct, SimpleGraph.comap_adj, glueGraph]

theorem reconstruct_graph (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    reconstruct e (G.comap e) (fun a w => G.Adj (e a) w.val)
      (G.comap (fun w : {w : V // Outside e w} => w.val)) = G := by
  ext u v
  obtain ⟨u, rfl⟩ := (blockEquiv e).surjective u
  obtain ⟨v, rfl⟩ := (blockEquiv e).surjective v
  cases u <;> cases v <;> simp [SimpleGraph.adj_comm]

def BoundaryMatches (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (B : Fin 4 → {w : V // Outside e w} → Prop) : Prop :=
  ∀ w, ((if B 0 w then 1 else 0) + (if B 1 w then 1 else 0) =
      edgeBit G (e 0) w.val + edgeBit G (e 1) w.val) ∧
    ((if B 2 w then 1 else 0) + (if B 3 w then 1 else 0) =
      edgeBit G (e 2) w.val + edgeBit G (e 3) w.val)

theorem sameCell_reconstruct (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (hleft : I.Adj 0 1 ↔ G.Adj (e 0) (e 1))
    (hright : I.Adj 2 3 ↔ G.Adj (e 2) (e 3))
    (hB : BoundaryMatches e G B) :
    SameCell e G (reconstruct e I B (G.comap Subtype.val)) := by
  constructor
  · intro u v hu hv
    simpa using (reconstruct_outside_outside e I B (G.comap Subtype.val)
      ⟨u, hu⟩ ⟨v, hv⟩).symm
  · simpa using hleft.symm
  · simpa using hright.symm
  · intro w hw
    simp only [edgeBit]
    rw [reconstruct_block_outside e I B (G.comap Subtype.val) 0 ⟨w, hw⟩,
      reconstruct_block_outside e I B (G.comap Subtype.val) 1 ⟨w, hw⟩]
    exact (hB ⟨w, hw⟩).1.symm
  · intro w hw
    simp only [edgeBit]
    rw [reconstruct_block_outside e I B (G.comap Subtype.val) 2 ⟨w, hw⟩,
      reconstruct_block_outside e I B (G.comap Subtype.val) 3 ⟨w, hw⟩]
    exact (hB ⟨w, hw⟩).2.symm

variable [Fintype V]

theorem degree_eq_sum_bits (G : SimpleGraph V) (v : V) :
    G.degree v = ∑ w, if G.Adj v w then (1 : Nat) else 0 := by
  simpa using G.degree_eq_sum_if_adj (R := Nat) v

theorem degree_reconstruct_block (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (a : Fin 4) :
    (reconstruct e I B O).degree (e a) =
      I.degree a + (Finset.univ.filter (fun w => B a w)).card := by
  rw [degree_eq_sum_bits (reconstruct e I B O) _,
    ← (blockEquiv e).sum_comp
      (fun v => if (reconstruct e I B O).Adj (e a) v then (1 : Nat) else 0),
    Fintype.sum_sum_type]
  simp only [blockEquiv_inl, blockEquiv_inr, reconstruct_block_block,
    reconstruct_block_outside, degree_eq_sum_bits, Finset.card_filter]

theorem degree_reconstruct_outside (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (w : {w : V // Outside e w}) :
    (reconstruct e I B O).degree w.val =
      (Finset.univ.filter (fun a => B a w)).card + O.degree w := by
  rw [degree_eq_sum_bits (reconstruct e I B O) _,
    ← (blockEquiv e).sum_comp
      (fun v => if (reconstruct e I B O).Adj w.val v then (1 : Nat) else 0),
    Fintype.sum_sum_type]
  simp only [blockEquiv_inl, blockEquiv_inr, reconstruct_outside_block,
    reconstruct_outside_outside, degree_eq_sum_bits, Finset.card_filter]

theorem degree_outside_preserved (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (hB : BoundaryMatches e G B) (w : {w : V // Outside e w}) :
    (reconstruct e I B (G.comap Subtype.val)).degree w.val = G.degree w.val := by
  have hcolumn : (Finset.univ.filter (fun a => B a w)).card =
      (Finset.univ.filter (fun a : Fin 4 => G.Adj (e a) w.val)).card := by
    simp only [Finset.card_filter, Fin.sum_univ_four]
    have h1 := (hB w).1
    have h2 := (hB w).2
    simp only [edgeBit] at h1 h2
    omega
  have hG := degree_reconstruct_outside e (G.comap e)
    (fun a w => G.Adj (e a) w.val) (G.comap Subtype.val) w
  rw [reconstruct_graph] at hG
  rw [degree_reconstruct_outside, hcolumn]
  exact hG.symm

theorem degree_preserved_of_block (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (hB : BoundaryMatches e G B)
    (hblock : ∀ a, I.degree a + (Finset.univ.filter (fun w => B a w)).card =
      G.degree (e a)) :
    ∀ v, (reconstruct e I B (G.comap Subtype.val)).degree v = G.degree v := by
  intro v
  obtain ⟨v, rfl⟩ := (blockEquiv e).surjective v
  cases v with
  | inl a =>
    change (reconstruct e I B (G.comap Subtype.val)).degree (e a) = G.degree (e a)
    rw [degree_reconstruct_block]
    exact hblock a
  | inr w => exact degree_outside_preserved e G I B hB w

end Problem315.DisjointEncoding

end

end OAI
