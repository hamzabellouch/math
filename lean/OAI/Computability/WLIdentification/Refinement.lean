import OAI.Computability.WLIdentification.Model

namespace OAI

namespace WLIdentification

/-- Equality of finite color histograms admits a color-preserving bijection. -/
theorem exists_colorEquiv {α β γ : Type} [Fintype α] [Fintype β]
    (f : α → γ) (g : β → γ)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ e : α ≃ β, ∀ a, f a = g (e a) := by
  classical
  have hc (c : γ) : Fintype.card {a // f a = c} = Fintype.card {b // g b = c} := by
    have hh := congrArg (Multiset.count c) h
    simpa only [Multiset.count_map, Fintype.card_subtype, ← Finset.filter_val,
      Finset.card_def, eq_comm] using hh
  let E (c : γ) : {a // f a = c} ≃ {b // g b = c} :=
    Classical.choice (Fintype.card_eq.mp (hc c))
  let e : α ≃ β := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight E).trans (Equiv.sigmaFiberEquiv g))
  refine ⟨e, ?_⟩
  intro a
  exact (E (f a) ⟨a, rfl⟩).property.symm

/-- A round witness is a bijection on the entire tuple table. -/
theorem tupleRound_bijection {G H : Graph} {k s : ℕ}
    (h : tupleHistogram G k s = tupleHistogram H k s) :
    ∃ e : (Fin k → Fin G.order) ≃ (Fin k → Fin H.order),
      ∀ v, tupleColor G k s v = tupleColor H k s (e v) :=
  exists_colorEquiv _ _ h

def degree (G : Graph) (v : Fin G.order) : ℕ :=
  (Finset.univ.filter (fun w => G.edge v w = true)).card

/-- Degree is already recoverable from a joint-update round, with two distinct slots. -/
def degreeOfColor {k : ℕ} (i j : Fin k) (c : TupleColor k 1) : ℕ :=
  (c.2.map (fun vector => (vector j).2 i j)).count true

@[simp]
theorem degreeOfColor_tuple {G : Graph} {k : ℕ} (i j : Fin k) (hij : i ≠ j)
    (v : Fin k → Fin G.order) :
    degreeOfColor i j (tupleColor G k 1 v) = degree G (v i) := by
  classical
  unfold degreeOfColor
  dsimp only [tupleColor, TupleColor]
  rw [Multiset.map_map]
  simp only [Function.comp_def, Function.update_of_ne hij, Function.update_self]
  rw [Multiset.count_map]
  change (Multiset.filter (fun z => true = G.edge (v i) z) Finset.univ.val).card = _
  rw [show Multiset.filter (fun z => true = G.edge (v i) z) Finset.univ.val =
      Multiset.filter (fun z => G.edge (v i) z = true) Finset.univ.val from
    Multiset.filter_congr (fun _ _ => eq_comm)]
  rfl

/-- Equal one-round tuple colors preserve adjacency, equality and the degrees of its slots. -/
theorem round_one_local {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    {v : Fin k → Fin G.order} {w : Fin k → Fin H.order}
    (h : tupleColor G k 1 v = tupleColor H k 1 w) :
    (∀ i j, v i = v j ↔ w i = w j) ∧
    (∀ i j, G.edge (v i) (v j) = H.edge (w i) (w j)) ∧
    (∀ i, degree G (v i) = degree H (w i)) := by
  have h0 : tupleColor G k 0 v = tupleColor H k 0 w := congrArg Prod.fst h
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have he := congrFun (congrFun (congrArg Prod.fst h0) i) j
    exact decide_eq_decide.mp he
  · intro i j
    exact congrFun (congrFun (congrArg Prod.snd h0) i) j
  · intro i
    have hj : ∃ j : Fin k, i ≠ j := by
      let a : Fin k := ⟨0, by omega⟩
      let b : Fin k := ⟨1, by omega⟩
      by_cases hia : i = a
      · refine ⟨b, ?_⟩
        subst i
        intro he
        have := congrArg Fin.val he
        simp [a, b] at this
      · exact ⟨a, hia⟩
    obtain ⟨j, hij⟩ := hj
    have he := congrArg (degreeOfColor i j) h
    simpa only [degreeOfColor_tuple i j hij] using he

def diagonalEquiv {k : ℕ} (i : Fin k) (α : Type) :
    α ≃ {v : Fin k → α // ∀ j, v j = v i} where
  toFun x := ⟨fun _ => x, fun _ => rfl⟩
  invFun v := v.val i
  left_inv _ := rfl
  right_inv v := by
    apply Subtype.ext
    funext j
    exact (v.property j).symm

/-- Matching diagonal tuples yields exactly a degree-preserving vertex bijection. -/
theorem round_one_degreeBijection {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    (h : tupleHistogram G k 1 = tupleHistogram H k 1) :
    ∃ e : Fin G.order ≃ Fin H.order, ∀ v, degree G v = degree H (e v) := by
  obtain ⟨E, hE⟩ := tupleRound_bijection h
  let i : Fin k := ⟨0, by omega⟩
  have hdiag (v : Fin k → Fin G.order) :
      (∀ j, v j = v i) ↔ ∀ j, E v j = E v i := by
    apply forall_congr'
    intro j
    exact (round_one_local hk (hE v)).1 j i
  let e := (diagonalEquiv i (Fin G.order)).trans
    ((E.subtypeEquiv hdiag).trans (diagonalEquiv i (Fin H.order)).symm)
  refine ⟨e, ?_⟩
  intro v
  exact (round_one_local hk (hE (fun _ => v))).2.2 i

/-- The needed local reconstruction information follows from the literal r-WL definition. -/
theorem equivalent_degreeBijection {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    (h : Equivalent k G H) :
    ∃ e : Fin G.order ≃ Fin H.order, ∀ v, degree G v = degree H (e v) := by
  have hne : k ≠ 1 := by omega
  rw [Equivalent, ite_eq_right hne] at h
  exact round_one_degreeBijection hk (h 1)

/-- Any at most k distinguished vertices have a simultaneous degree-and-incidence match.
This is enough to recover a whole bounded-size incidence piece, not just one valuation. -/
theorem equivalent_local_match {G H : Graph} {k m : ℕ} (hk : 2 ≤ k)
    (h : Equivalent k G H) (hm : m ≤ k) (hm0 : 0 < m) (v : Fin m → Fin G.order) :
    ∃ w : Fin m → Fin H.order,
      (∀ i j, v i = v j ↔ w i = w j) ∧
      (∀ i j, G.edge (v i) (v j) = H.edge (w i) (w j)) ∧
      (∀ i, degree G (v i) = degree H (w i)) := by
  have hne : k ≠ 1 := by omega
  rw [Equivalent, ite_eq_right hne] at h
  obtain ⟨E, hE⟩ := tupleRound_bijection (h 1)
  let v' : Fin k → Fin G.order := fun j =>
    if hj : j.val < m then v ⟨j.val, hj⟩ else v ⟨0, hm0⟩
  have hv (i : Fin m) : v' (Fin.castLE hm i) = v i := by simp [v', i.isLt]
  let w : Fin m → Fin H.order := fun i => E v' (Fin.castLE hm i)
  refine ⟨w, ?_, ?_, ?_⟩
  · intro i j
    simpa only [hv] using (round_one_local hk (hE v')).1 (Fin.castLE hm i) (Fin.castLE hm j)
  · intro i j
    simpa only [hv] using (round_one_local hk (hE v')).2.1 (Fin.castLE hm i) (Fin.castLE hm j)
  · intro i
    simpa only [hv] using (round_one_local hk (hE v')).2.2 (Fin.castLE hm i)

/-- A second joint round gives a single vertex bijection preserving adjacency to
any distinguished slot and the degrees of all possible next vertices. -/
theorem round_two_neighborBijection {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    {v : Fin k → Fin G.order} {w : Fin k → Fin H.order}
    (h : tupleColor G k 2 v = tupleColor H k 2 w) (i : Fin k) :
    ∃ e : Fin G.order ≃ Fin H.order, ∀ z,
      G.edge (v i) z = H.edge (w i) (e z) ∧ degree G z = degree H (e z) := by
  have hj : ∃ j : Fin k, i ≠ j := by
    let a : Fin k := ⟨0, by omega⟩
    let b : Fin k := ⟨1, by omega⟩
    by_cases hia : i = a
    · refine ⟨b, ?_⟩
      subst i
      intro he
      have := congrArg Fin.val he
      simp [a, b] at this
    · exact ⟨a, hia⟩
  obtain ⟨j, hij⟩ := hj
  have hh := congrArg Prod.snd h
  change Finset.univ.val.map (fun z => fun j => tupleColor G k 1 (Function.update v j z)) =
    Finset.univ.val.map (fun z => fun j => tupleColor H k 1 (Function.update w j z)) at hh
  obtain ⟨e, he⟩ := exists_colorEquiv _ _ hh
  refine ⟨e, ?_⟩
  intro z
  have hz := round_one_local hk (v := Function.update v j z)
    (w := Function.update w j (e z)) (congrFun (he z) j)
  simpa only [Function.update_of_ne hij, Function.update_self] using
    And.intro (hz.2.1 i j) (hz.2.2 j)

def degreeNeighbors (G : Graph) (v : Fin G.order) (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun w => G.edge v w = true ∧ degree G w = d)).card

theorem round_two_degreeNeighbors {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    {v : Fin k → Fin G.order} {w : Fin k → Fin H.order}
    (h : tupleColor G k 2 v = tupleColor H k 2 w) (i : Fin k) (d : ℕ) :
    degreeNeighbors G (v i) d = degreeNeighbors H (w i) d := by
  obtain ⟨e, he⟩ := round_two_neighborBijection hk h i
  apply Finset.card_equiv e
  intro z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, (he z).1, (he z).2]

theorem equivalent_symm {G H : Graph} {k : ℕ} (h : Equivalent k G H) :
    Equivalent k H G := by
  unfold Equivalent at *
  split_ifs at * <;> exact fun s => (h s).symm

/-- In particular private-leaf counts, rather than just total degrees, are
preserved by a simultaneous local match in every equivalent mate. -/
theorem equivalent_local_neighborhood_match {G H : Graph} {k m : ℕ} (hk : 2 ≤ k)
    (h : Equivalent k G H) (hm : m ≤ k) (hm0 : 0 < m) (v : Fin m → Fin G.order) :
    ∃ w : Fin m → Fin H.order,
      (∀ i j, v i = v j ↔ w i = w j) ∧
      (∀ i j, G.edge (v i) (v j) = H.edge (w i) (w j)) ∧
      (∀ i, degree G (v i) = degree H (w i)) ∧
      (∀ i d, degreeNeighbors G (v i) d = degreeNeighbors H (w i) d) := by
  have hne : k ≠ 1 := by omega
  rw [Equivalent, ite_eq_right hne] at h
  obtain ⟨E, hE⟩ := tupleRound_bijection (h 2)
  let v' : Fin k → Fin G.order := fun j =>
    if hj : j.val < m then v ⟨j.val, hj⟩ else v ⟨0, hm0⟩
  have hv (i : Fin m) : v' (Fin.castLE hm i) = v i := by simp [v', i.isLt]
  let w : Fin m → Fin H.order := fun i => E v' (Fin.castLE hm i)
  have h1 : tupleColor G k 1 v' = tupleColor H k 1 (E v') :=
    congrArg Prod.fst (hE v')
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa only [hv] using (round_one_local hk h1).1 (Fin.castLE hm i) (Fin.castLE hm j)
  · intro i j
    simpa only [hv] using (round_one_local hk h1).2.1 (Fin.castLE hm i) (Fin.castLE hm j)
  · intro i
    simpa only [hv] using (round_one_local hk h1).2.2 (Fin.castLE hm i)
  · intro i d
    simpa only [hv] using round_two_degreeNeighbors hk (hE v') (Fin.castLE hm i) d

end WLIdentification

end OAI
