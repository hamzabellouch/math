import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

namespace Problem367

theorem reflTransGen_erase_of_unique_neighbor
    {α : Type*} [DecidableEq α] {D : Finset α} {R : α → α → Prop}
    {v p a b : α}
    (hsymm : ∀ {x y}, R x y → R y x)
    (hp : p ∈ D) (hpv : p ≠ v)
    (hleaf : ∀ x ∈ D, R v x → x = p)
    (ha : a ∈ D.erase v) (hb : b ∈ D.erase v)
    (hab : Relation.ReflTransGen (fun x y => x ∈ D ∧ y ∈ D ∧ R x y) a b) :
    Relation.ReflTransGen
      (fun x y => x ∈ D.erase v ∧ y ∈ D.erase v ∧ R x y) a b := by
  let f : α → α := fun x => if x = v then p else x
  have hf : ∀ x ∈ D, f x ∈ D.erase v := by
    intro x hx
    by_cases hxv : x = v
    · simp [f, hxv, hpv, hp]
    · simp [f, hxv, hx]
  have hstep : ∀ x y, x ∈ D ∧ y ∈ D ∧ R x y →
      Relation.ReflTransGen
        (fun x y => x ∈ D.erase v ∧ y ∈ D.erase v ∧ R x y) (f x) (f y) := by
    intro x y hxy
    by_cases hxv : x = v
    · have hyp : y = p := hleaf y hxy.2.1 (hxv ▸ hxy.2.2)
      subst x
      subst y
      simp only [f, ite_eq_left rfl, ite_eq_right hpv]
      exact Relation.ReflTransGen.refl
    · by_cases hyv : y = v
      · have hxp : x = p := hleaf x hxy.1 (hsymm (hyv ▸ hxy.2.2))
        subst y
        subst x
        simp only [f, ite_eq_left rfl, ite_eq_right hpv]
        exact Relation.ReflTransGen.refl
      · apply Relation.ReflTransGen.single
        exact ⟨hf x hxy.1, hf y hxy.2.1, by simpa [f, hxv, hyv] using hxy.2.2⟩
  have h := Relation.ReflTransGen.lift' f hstep a b hab
  simpa [Function.onFun, f, (Finset.mem_erase.mp ha).1, (Finset.mem_erase.mp hb).1] using h

theorem reflTransGen_connected_erase_of_leaf
    {α : Type*} [DecidableEq α] {D : Finset α} {R : α → α → Prop} {v : α}
    (hsymm : ∀ {x y}, R x y → R y x)
    (hirrefl : ∀ x, ¬ R x x)
    (hconn : ∀ a ∈ D, ∀ b ∈ D,
      Relation.ReflTransGen (fun x y => x ∈ D ∧ y ∈ D ∧ R x y) a b)
    (hv : v ∈ D) (hn : (D.erase v).Nonempty)
    (hleaf : ∀ x ∈ D, ∀ y ∈ D, R v x → R v y → x = y) :
    ∀ a ∈ D.erase v, ∀ b ∈ D.erase v,
      Relation.ReflTransGen
        (fun x y => x ∈ D.erase v ∧ y ∈ D.erase v ∧ R x y) a b := by
  obtain ⟨q, hq⟩ := hn
  obtain h | ⟨p, hvp, _⟩ := (hconn v hv q (Finset.mem_erase.mp hq).2).cases_head
  · exact False.elim ((Finset.mem_erase.mp hq).1 h.symm)
  · have hpv : p ≠ v := by
      intro h
      subst p
      exact hirrefl v hvp.2.2
    intro a ha b hb
    exact reflTransGen_erase_of_unique_neighbor hsymm hvp.2.1 hpv
      (fun x hx hxv => hleaf x hx p hvp.2.1 hxv hvp.2.2) ha hb
      (hconn a (Finset.mem_erase.mp ha).2 b (Finset.mem_erase.mp hb).2)

theorem connectedFinset_erase_of_leaf
    {d : ℕ} {D : Finset (TreeVertex d)} {v : TreeVertex d}
    (hD : ConnectedFinset D) (hv : v ∈ D) (hn : (D.erase v).Nonempty)
    (hleaf : ∀ x ∈ D, ∀ y ∈ D, treeAdj v x → treeAdj v y → x = y) :
    ConnectedFinset (D.erase v) := by
  refine ⟨hn, reflTransGen_connected_erase_of_leaf ?_ ?_ hD.2 hv hn hleaf⟩
  · intro x y h
    exact h.elim Or.inr Or.inl
  · intro x h
    rcases h with ⟨c, h⟩ | ⟨c, h⟩ <;>
      have := congrArg List.length h <;> simp at this

theorem treeAdj_unique_neighbor_of_max_length
    {d : ℕ} {D : Finset (TreeVertex d)} {v : TreeVertex d}
    (hmax : ∀ x ∈ D, x.1.length ≤ v.1.length) :
    ∀ x ∈ D, ∀ y ∈ D, treeAdj v x → treeAdj v y → x = y := by
  have hlower : ∀ x ∈ D, treeAdj v x → ∃ c : Fin d, v.1 = x.1 ++ [c] := by
    intro x hx hadj
    rcases hadj with ⟨c, hc⟩ | h
    · have hlen := congrArg List.length hc
      have hbound := hmax x hx
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    · exact h
  intro x hx y hy hvx hvy
  obtain ⟨c, hc⟩ := hlower x hx hvx
  obtain ⟨e, he⟩ := hlower y hy hvy
  apply Subtype.ext
  have h := congrArg List.dropLast (hc.symm.trans he)
  simpa using h

theorem connectedFinset_erase_of_max_length
    {d : ℕ} {D : Finset (TreeVertex d)} {v : TreeVertex d}
    (hD : ConnectedFinset D) (hv : v ∈ D) (hn : (D.erase v).Nonempty)
    (hmax : ∀ x ∈ D, x.1.length ≤ v.1.length) :
    ConnectedFinset (D.erase v) :=
  connectedFinset_erase_of_leaf hD hv hn (treeAdj_unique_neighbor_of_max_length hmax)

theorem inducedEdges_eq_insert_erase_of_max_length
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (hv : v ∈ D) (hp : p ∈ D) (hpv : treeAdj p v)
    (hplen : p.1.length < v.1.length)
    (hmax : ∀ x ∈ D, x.1.length ≤ v.1.length) :
    inducedEdges D = insert (p, v) (inducedEdges (D.erase v)) := by
  classical
  ext e
  rcases e with ⟨x, y⟩
  simp only [inducedEdges, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_insert, Prod.mk.injEq, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hx, hy⟩, hxy, hlen⟩
    have hxv : x ≠ v := by
      intro h
      subst x
      have := hmax y hy
      omega
    by_cases hyv : y = v
    · left
      refine ⟨?_, hyv⟩
      apply treeAdj_unique_neighbor_of_max_length hmax x hx p hp
      · exact (hyv ▸ hxy).elim Or.inr Or.inl
      · exact hpv.elim Or.inr Or.inl
    · exact Or.inr ⟨⟨⟨hxv, hx⟩, ⟨hyv, hy⟩⟩, hxy, hlen⟩
  · rintro (⟨rfl, rfl⟩ | ⟨⟨⟨_, hx⟩, ⟨_, hy⟩⟩, hxy, hlen⟩)
    · exact ⟨⟨hp, hv⟩, hpv, hplen⟩
    · exact ⟨⟨hx, hy⟩, hxy, hlen⟩

theorem inducedEdges_eq_insert_erase_of_unique_lower_neighbor
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (hv : v ∈ D) (hp : p ∈ D) (hpv : treeAdj p v)
    (hplen : p.1.length < v.1.length)
    (hleaf : ∀ x ∈ D, treeAdj v x → x = p) :
    inducedEdges D = insert (p, v) (inducedEdges (D.erase v)) := by
  classical
  ext e
  rcases e with ⟨x, y⟩
  simp only [inducedEdges, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_insert, Prod.mk.injEq, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hx, hy⟩, hxy, hlen⟩
    have hxv : x ≠ v := by
      intro h
      subst x
      have hyp := hleaf y hy hxy
      subst y
      omega
    by_cases hyv : y = v
    · exact Or.inl ⟨hleaf x hx ((hyv ▸ hxy).elim Or.inr Or.inl), hyv⟩
    · exact Or.inr ⟨⟨⟨hxv, hx⟩, ⟨hyv, hy⟩⟩, hxy, hlen⟩
  · rintro (⟨rfl, rfl⟩ | ⟨⟨⟨_, hx⟩, ⟨_, hy⟩⟩, hxy, hlen⟩)
    · exact ⟨⟨hp, hv⟩, hpv, hplen⟩
    · exact ⟨⟨hx, hy⟩, hxy, hlen⟩

end Problem367

end

end OAI
