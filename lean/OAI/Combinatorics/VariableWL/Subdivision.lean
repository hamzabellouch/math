import OAI.Combinatorics.VariableWL.Refinement

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.Subdivision

variable {P : Type uVariable1} {E : Type uVariable2} {n : ℕ}

abbrev Vertex (P : Type uVariable3) (E : Type uVariable4) (n : ℕ) := P ⊕ (E × Fin n)
abbrev Link (E : Type uVariable5) (n : ℕ) := E × Fin (n+1)

def left (src : E → P) (l : Link E n) : Vertex P E n :=
  if h : l.2.val = 0 then .inl (src l.1)
  else .inr (l.1, ⟨l.2.val - 1, by omega⟩)

def right (dst : E → P) (l : Link E n) : Vertex P E n :=
  if h : l.2.val = n then .inl (dst l.1)
  else .inr (l.1, ⟨l.2.val, by omega⟩)

theorem endpoints_ne (hn : 0 < n) (src dst : E → P) (l : Link E n) :
    left src l ≠ right dst l := by
  unfold left right
  split_ifs with h₀ h₁ h₁
  · omega
  · simp
  · simp
  · intro h
    have hh := congrArg (fun x : Vertex P E n =>
      match x with | .inl _ => 0 | .inr x => x.2.val) h
    simp only at hh
    omega

theorem exists_unused_cut [DecidableEq E] (S : Finset (Link E n))
    (hS : S.card < n+1) : ∃ cut : E → Fin (n+1), ∀ e, (e, cut e) ∉ S := by
  classical
  have hx (e : E) : ∃ i : Fin (n+1), (e,i) ∉ S := by
    by_contra h
    have hall : ∀ i : Fin (n+1), (e,i) ∈ S := by simpa using h
    have hsub : Finset.univ.image (fun i : Fin (n+1) => (e,i)) ⊆ S := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hall i
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (fun _ _ h => Prod.mk.inj h |>.2),
      Finset.card_univ, Fintype.card_fin] at hc
    omega
  exact ⟨fun e => (hx e).choose, fun e => (hx e).choose_spec⟩

def owner (src dst : E → P) (cut : E → Fin (n+1)) : Vertex P E n → P
  | .inl p => p
  | .inr (e,j) => if j.val < (cut e).val then src e else dst e

@[simp] theorem owner_real (src dst : E → P) (cut : E → Fin (n+1)) (p : P) :
    owner src dst cut (.inl p) = p := rfl

theorem owner_link (src dst : E → P) (cut : E → Fin (n+1))
    (l : Link E n) (hcut : l.2 ≠ cut l.1) :
    owner src dst cut (left src l) = owner src dst cut (right dst l) := by
  have hv : l.2.val ≠ (cut l.1).val := fun h => hcut (Fin.ext h)
  unfold left right
  split_ifs with h₀ h₁ h₁
  · omega
  · simp only [owner]
    rw [ite_eq_left (by omega)]
  · simp only [owner]
    rw [ite_eq_right (by omega)]
  · simp only [owner]
    have hi : l.2.val - 1 < (cut l.1).val ↔ l.2.val < (cut l.1).val := by omega
    simp only [hi]

def depth (cut : E → Fin (n+1)) : Vertex P E n → ℕ
  | .inl _ => 0
  | .inr (e,j) => if j.val < (cut e).val then j.val+1 else n-j.val

theorem depth_link (src dst : E → P) (cut : E → Fin (n+1))
    (l : Link E n) (hcut : l.2 ≠ cut l.1) :
    if l.2.val < (cut l.1).val then
      depth cut (right dst l) = depth cut (left src l) + 1
    else depth cut (left src l) = depth cut (right dst l) + 1 := by
  have hv : l.2.val ≠ (cut l.1).val := fun h => hcut (Fin.ext h)
  have hb := l.2.isLt
  have hbc := (cut l.1).isLt
  unfold left right
  split_ifs <;> simp only [depth]
  all_goals (try split_ifs) <;> omega

def supportGraph (hn : 0 < n) (src dst : E → P) (S : Set (Link E n)) :
    SimpleGraph (Vertex P E n) where
  Adj v w := ∃ l ∈ S,
    (v = left src l ∧ w = right dst l) ∨ (v = right dst l ∧ w = left src l)
  symm := ⟨by
    rintro v w ⟨l, hl, h⟩
    exact ⟨l, hl, h.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm)⟩⟩
  loopless := ⟨by
    rintro v ⟨l, _, h⟩
    exact endpoints_ne hn src dst l (h.elim (fun h => h.1.symm.trans h.2)
      (fun h => h.2.symm.trans h.1))⟩

theorem owner_adj (hn : 0 < n) (src dst : E → P) (S : Set (Link E n))
    (cut : E → Fin (n+1)) (hc : ∀ l ∈ S, l.2 ≠ cut l.1)
    {v w : Vertex P E n} (h : (supportGraph hn src dst S).Adj v w) :
    owner src dst cut v = owner src dst cut w := by
  obtain ⟨l, hl, h⟩ := h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact owner_link src dst cut l (hc l hl)
  · exact (owner_link src dst cut l (hc l hl)).symm

theorem owner_walk (hn : 0 < n) (src dst : E → P) (S : Set (Link E n))
    (cut : E → Fin (n+1)) (hc : ∀ l ∈ S, l.2 ≠ cut l.1)
    {v w : Vertex P E n} (p : (supportGraph hn src dst S).Walk v w) :
    owner src dst cut v = owner src dst cut w := by
  induction p with
  | nil => rfl
  | cons h p ih => exact (owner_adj hn src dst S cut hc h).trans ih

theorem at_most_one_real [DecidableEq E] (hn : 0 < n) (src dst : E → P)
    (S : Finset (Link E n)) (hS : S.card < n+1) {p q : P}
    (h : (supportGraph hn src dst S).Reachable (.inl p) (.inl q)) : p = q := by
  obtain ⟨cut, hc⟩ := exists_unused_cut S hS
  apply owner_walk hn src dst S cut (fun l hl h => ?_) h.some
  change l ∈ S at hl
  exact hc l.1 (by simpa only [← h, Prod.eta] using hl)

end VariableWL.Subdivision

namespace VariableWL.Subdivision
variable {P : Type uVariable6} {E : Type uVariable7} {n : ℕ}

def parent (src dst : E → P) (cut : E → Fin (n+1)) : Vertex P E n → Vertex P E n
  | .inl p => .inl p
  | .inr (e,j) =>
    if j.val < (cut e).val then
      if h : j.val = 0 then .inl (src e)
      else .inr (e, ⟨j.val-1, by omega⟩)
    else
      if h : j.val+1 = n then .inl (dst e)
      else .inr (e, ⟨j.val+1, by omega⟩)

theorem parent_link (src dst : E → P) (cut : E → Fin (n+1))
    (l : Link E n) (hcut : l.2 ≠ cut l.1) :
    if l.2.val < (cut l.1).val then
      parent src dst cut (right dst l) = left src l
    else parent src dst cut (left src l) = right dst l := by
  have hv : l.2.val ≠ (cut l.1).val := fun h => hcut (Fin.ext h)
  have hb := l.2.isLt
  have hbc := (cut l.1).isLt
  unfold left right
  split_ifs <;> simp only [parent]
  all_goals try split_ifs
  all_goals first | omega | rfl | (congr 2; apply Fin.ext; simp only; omega)

theorem acyclic_of_unique_lower {V : Type uVariable8} (G : SimpleGraph V) (rank : V → ℕ)
    (hne : ∀ u v, G.Adj u v → rank u ≠ rank v)
    (hunique : ∀ u v w, G.Adj u v → G.Adj u w →
      rank v < rank u → rank w < rank u → v = w) : G.IsAcyclic := by
  classical
  intro v p hp
  obtain ⟨u, hu, hmax⟩ := (p.support.toFinset).exists_max_image rank
    ⟨v, List.mem_toFinset.mpr p.start_mem_support⟩
  have hup : u ∈ p.support := List.mem_toFinset.mp hu
  let q := p.rotate u hup
  have hq : q.IsCycle := hp.rotate hup
  have hs : G.Adj u q.snd := by
    simpa only [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.snd] using
      q.adj_getVert_succ (i := 0) (by have := hq.three_le_length; omega)
  have ht : G.Adj u q.penultimate := by
    have := q.adj_getVert_succ (i := q.length-1) (by have := hq.three_le_length; omega)
    rw [Nat.sub_add_cancel (by have := hq.three_le_length; omega),
      SimpleGraph.Walk.getVert_length] at this
    exact this.symm
  have hm (x : V) (hx : x ∈ q.support) : rank x ≤ rank u := by
    apply hmax x
    exact List.mem_toFinset.mpr ((p.mem_support_rotate_iff u hup).mp hx)
  have hms := hm q.snd (q.getVert_mem_support 1)
  have hmt := hm q.penultimate (q.getVert_mem_support (q.length-1))
  exact hq.snd_ne_penultimate (hunique u q.snd q.penultimate hs ht
    (lt_of_le_of_ne hms (hne _ _ hs).symm) (lt_of_le_of_ne hmt (hne _ _ ht).symm))

theorem chosen_support_acyclic (hn : 0 < n) (src dst : E → P)
    (S : Set (Link E n)) (cut : E → Fin (n+1))
    (hc : ∀ l ∈ S, l.2 ≠ cut l.1) : (supportGraph hn src dst S).IsAcyclic := by
  have hedge {u v} (h : (supportGraph hn src dst S).Adj u v) :
      (depth cut u + 1 = depth cut v ∧ parent src dst cut v = u) ∨
      (depth cut v + 1 = depth cut u ∧ parent src dst cut u = v) := by
    obtain ⟨l, hl, h⟩ := h
    have hd := depth_link src dst cut l (hc l hl)
    have hp := parent_link src dst cut l (hc l hl)
    split_ifs at hd hp with hi
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨hd.symm, hp⟩
      · exact Or.inr ⟨hd.symm, hp⟩
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨hd.symm, hp⟩
      · exact Or.inl ⟨hd.symm, hp⟩
  apply acyclic_of_unique_lower _ (depth cut)
  · intro u v h
    rcases hedge h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  · intro u v w hv hw hdv hdw
    rcases hedge hv with ⟨h, _⟩ | ⟨_, h⟩
    · omega
    rcases hedge hw with ⟨h', _⟩ | ⟨_, h'⟩
    · omega
    exact h.symm.trans h'

theorem small_support_acyclic [DecidableEq E] (hn : 0 < n) (src dst : E → P)
    (S : Finset (Link E n)) (hS : S.card < n+1) :
    (supportGraph hn src dst S).IsAcyclic := by
  obtain ⟨cut, hc⟩ := exists_unused_cut S hS
  exact chosen_support_acyclic hn src dst S cut (fun l hl h => hc l.1
    (by change l ∈ S at hl; simpa only [← h, Prod.eta] using hl))

theorem internal_adj_wire (hn : 0 < n) (src dst : E → P) (S : Set (Link E n))
    {e f : E} {i j : Fin n}
    (h : (supportGraph hn src dst S).Adj (.inr (e,i)) (.inr (f,j))) : e = f := by
  obtain ⟨l, _, h⟩ := h
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  all_goals
    simp only [left, right] at h₁ h₂
    split_ifs at h₁ h₂
    all_goals simp_all

end VariableWL.Subdivision

namespace VariableWL.Markers
open scoped CharTwo
variable {V : Type uVariable9} {G : SimpleGraph V}

theorem walkSum_congr {ω ω' : V → V → Bit}
    (h : ∀ u v, G.Adj u v → ω u v = ω' u v) {u v : V} (p : G.Walk u v) :
    walkSum ω p = walkSum ω' p := by
  induction p with
  | nil => rfl
  | cons h' p ih => rw [walkSum_cons, walkSum_cons, h _ _ h', ih]

@[simp] theorem walkSum_zero {u v : V} (p : G.Walk u v) :
    walkSum (fun _ _ => 0) p = 0 := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [walkSum, ih]

theorem walkSum_add (ω ω' : V → V → Bit) {u v : V} (p : G.Walk u v) :
    walkSum (fun x y => ω x y + ω' x y) p = walkSum ω p + walkSum ω' p := by
  induction p with
  | nil => simp [walkSum]
  | cons _ _ ih => simp only [walkSum_cons, ih]; ring

theorem walkSum_mul (ω : V → V → Bit) (c : Bit) {u v : V} (p : G.Walk u v) :
    walkSum (fun x y => ω x y * c) p = walkSum ω p * c := by
  induction p with
  | nil => simp [walkSum]
  | cons _ _ ih => simp only [walkSum_cons, ih]; ring

end VariableWL.Markers

end OAI
