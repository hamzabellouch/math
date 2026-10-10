import OAI.Combinatorics.ListHadwiger.Reduction

namespace OAI

namespace ReedSeymour
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V}

lemma loops_even_of_cycles_even
    (h : ∀ (v : V) (p : G.Walk v v), p.IsCycle → Even p.length) :
    ∀ (v : V) (p : G.Walk v v), Even p.length := by
  suffices ∀ n (v : V) (p : G.Walk v v), p.length = n → Even p.length by
    intro v p
    exact this p.length v p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v p hn
    cases p with
    | nil => simp
    | @cons _ a b hab q =>
      by_cases hp : q.IsPath
      · by_cases hl : 3 ≤ (q.cons hab).length
        · exact h _ _ (Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨by simpa using hp, hl⟩)
        · have hpos : 0 < q.length := by
            by_contra hnot
            have hh : q.Nil := by simpa using (show q.length = 0 by omega)
            exact hab.ne hh.eq.symm
          have hh : (q.cons hab).length = 2 := by simp only [Walk.length_cons] at *; omega
          simp [hh]
      · rw [Walk.isPath_iff_isSubwalk_imp_nil] at hp
        push Not at hp
        obtain ⟨x, c, ⟨a, b, hq⟩, hc⟩ := hp
        have hcpos : 0 < c.length := by
          by_contra hh
          apply hc
          simpa using (show c.length = 0 by omega)
        have heq : n = a.length + c.length + b.length + 1 := by
          rw [hq, Walk.length_cons, Walk.length_append, Walk.length_append] at hn
          omega
        have ec := ih c.length (by omega) x c rfl
        have er := ih ((b.append (a.cons hab)).length) (by
          simp only [Walk.length_append, Walk.length_cons]; omega) x
          (b.append (a.cons hab)) rfl
        rw [hq]
        simp only [Walk.length_cons, Walk.length_append] at er ⊢
        rw [Nat.even_iff] at ec er ⊢
        omega

lemma two_colorable_of_cycles_even
    (h : ∀ (v : V) (p : G.Walk v v), p.IsCycle → Even p.length) :
    G.Colorable 2 :=
  SimpleGraph.two_colorable_iff_forall_loop_even.mpr (loops_even_of_cycles_even h)

def Shortest {a b : V} (p : G.Walk a b) : Prop :=
  ∀ q : G.Walk a b, p.length ≤ q.length

lemma exists_shortest {a b : V} (h : G.Reachable a b) :
    ∃ p : G.Walk a b, Shortest p := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  refine ⟨p, fun q => ?_⟩
  rw [hp]
  exact SimpleGraph.dist_le q

lemma Shortest.separated {a b : V} {p : G.Walk a b} (hp : Shortest p)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) (hij : i < j) :
    p.getVert i ≠ p.getVert j := by
  intro he
  let q := (p.take i).append ((p.drop j).copy he.symm rfl)
  have hh := hp q
  simp only [q, Walk.length_append, Walk.length_copy, Walk.take_length,
    Walk.drop_length, Nat.min_eq_left hi] at hh
  omega

lemma Shortest.adj_indices {a b : V} {p : G.Walk a b} (hp : Shortest p)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (he : G.Adj (p.getVert i) (p.getVert j)) : i + 1 = j ∨ j + 1 = i := by
  have hf : ∀ {i j : ℕ}, i ≤ p.length → j ≤ p.length → i < j →
      G.Adj (p.getVert i) (p.getVert j) → i + 1 = j := by
    intro i j hi hj hij he
    have hh := hp ((p.take i).append (he.toWalk.append (p.drop j)))
    simp only [Walk.length_append, Walk.take_length, Walk.drop_length,
      Adj.length_toWalk, Nat.min_eq_left hi] at hh
    omega
  rcases lt_trichotomy i j with hij | hij | hij
  · exact Or.inl (hf hi hj hij he)
  · exact (he.ne (congrArg p.getVert hij)).elim
  · exact Or.inr (hf hj hi hij he.symm)

def ReachOn (G : SimpleGraph V) (S : Set V) (a b : V) : Prop :=
  ∃ p : G.Walk a b, ∀ x ∈ p.support, x ∈ S

lemma ReachOn.left {S : Set V} {a b : V} (h : ReachOn G S a b) : a ∈ S :=
  h.choose_spec a h.choose.start_mem_support
lemma ReachOn.right {S : Set V} {a b : V} (h : ReachOn G S a b) : b ∈ S :=
  h.choose_spec b h.choose.end_mem_support
lemma ReachOn.refl {S : Set V} {a : V} (h : a ∈ S) : ReachOn G S a a :=
  ⟨.nil, by simpa using h⟩
lemma ReachOn.symm {S : Set V} {a b : V} (h : ReachOn G S a b) : ReachOn G S b a := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by simpa using hp⟩
lemma ReachOn.trans {S : Set V} {a b c : V} (h : ReachOn G S a b)
    (h' : ReachOn G S b c) : ReachOn G S a c := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := h'
  exact ⟨p.append q, fun x hx => (Walk.mem_support_append_iff p q).mp hx |>.elim
    (hp x) (hq x)⟩
lemma ReachOn.mono {S T : Set V} {a b : V} (h : ReachOn G S a b) (hst : S ⊆ T) :
    ReachOn G T a b := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun x hx => hst (hp x hx)⟩
lemma ReachOn.adj {S : Set V} {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (hab : G.Adj a b) : ReachOn G S a b :=
  ⟨hab.toWalk, by simpa using (show a ∈ S ∧ b ∈ S from ⟨ha,hb⟩)⟩

lemma connected_iff_reachOn {S : Set V} :
    (G.induce S).Connected ↔ S.Nonempty ∧ ∀ a ∈ S, ∀ b ∈ S, ReachOn G S a b := by
  constructor
  · intro h
    refine ⟨by obtain ⟨a, ha⟩ := Classical.choice h.nonempty; exact ⟨a,ha⟩, ?_⟩
    intro a ha b hb
    obtain ⟨p⟩ := h ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨p.map (SimpleGraph.Embedding.induce S).toHom, ?_⟩
    intro x hx
    have hh : x ∈ p.support.map (SimpleGraph.Embedding.induce S).toHom :=
      (Walk.support_map ..) ▸ hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hh
    exact y.property
  · rintro ⟨hne, h⟩
    refine { preconnected := ?_, nonempty := hne.to_subtype }
    intro a b
    obtain ⟨p, hp⟩ := h a a.property b b.property
    exact ⟨p.induce S hp⟩

lemma connected_reachOn {S : Set V} (h : (G.induce S).Connected)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) : ReachOn G S a b :=
  (connected_iff_reachOn.mp h).2 a ha b hb

def component (G : SimpleGraph V) (S : Set V) (a : V) : Set V :=
  {b | ReachOn G S a b}

lemma component_subset (S : Set V) (a : V) : component G S a ⊆ S :=
  fun _ hb => hb.right

lemma component_connected {S : Set V} {a : V} (ha : a ∈ S) :
    (G.induce (component G S a)).Connected := by
  refine connected_iff_reachOn.mpr ⟨⟨a, ReachOn.refl ha⟩, ?_⟩
  intro x hx y hy
  obtain ⟨p, hp⟩ := hx.symm.trans hy
  refine ⟨p, fun z hz => ?_⟩
  classical
  have hreach : ReachOn G S x z := ⟨p.takeUntil z hz, fun t ht =>
    hp t (p.support_takeUntil_subset_support hz ht)⟩
  exact hx.trans hreach

lemma cycle_delete_connected_root {a : V} {p : G.Walk a a} (hp : p.IsCycle) :
    (G.induce ({v | v ∈ p.support} \ {a})).Connected := by
  cases p with
  | nil => exact (Walk.not_isCycle_nil hp).elim
  | @cons _ b c hab q =>
    have hq : q.IsPath := (Walk.cons_isCycle_iff q hab).mp hp |>.1
    have hn : ¬q.Nil := Walk.not_nil_of_isCycle_cons hp
    have hd := hq.support_nodup
    rw [← q.support_dropLast_concat hn, List.nodup_append] at hd
    have ha : a ∉ q.dropLast.support := by simpa using hd.2.2 a
    have he : ({v | v ∈ (q.cons hab).support} \ {a} : Set V) =
        {v | v ∈ q.dropLast.support} := by
      ext v
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
        Walk.support_cons, List.mem_cons, ← q.support_dropLast_concat hn,
        List.mem_append]
      have hh : v ∈ q.dropLast.support → v ≠ a := by rintro hv rfl; exact ha hv
      tauto
    rw [he]
    exact q.dropLast.connected_induce_support

lemma cycle_delete_connected {a v : V} {p : G.Walk a a} (hp : p.IsCycle)
    (hv : v ∈ p.support) : (G.induce ({x | x ∈ p.support} \ {v})).Connected := by
  classical
  have he : {x | x ∈ (p.rotate v hv).support} = {x | x ∈ p.support} := by
    ext x
    exact Walk.mem_support_rotate_iff p v hv
  have hh := cycle_delete_connected_root (hp.rotate hv)
  rwa [he] at hh

structure BetweenMin (G : SimpleGraph V) (A B : Set V) (a b : V) (p : G.Walk a b) : Prop where
  source : a ∈ A
  target : b ∈ B
  minimal : ∀ x ∈ A, ∀ y ∈ B, ∀ q : G.Walk x y, p.length ≤ q.length

lemma exists_betweenMin (hG : G.Connected) {A B : Set V} (hA : A.Nonempty)
    (hB : B.Nonempty) : ∃ (a b : V) (p : G.Walk a b), BetweenMin G A B a b p := by
  have hex : ∃ n : ℕ, ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b, p.length = n := by
    obtain ⟨a,ha⟩ := hA
    obtain ⟨b,hb⟩ := hB
    obtain ⟨p⟩ := hG a b
    exact ⟨p.length,a,ha,b,hb,p,rfl⟩
  classical
  obtain ⟨a,ha,b,hb,p,hp⟩ := Nat.find_spec hex
  refine ⟨a,b,p,ha,hb,?_⟩
  intro x hx y hy q
  rw [hp]
  exact Nat.find_min' hex ⟨x,hx,y,hy,q,rfl⟩

lemma BetweenMin.shortest {A B : Set V} {a b : V} {p : G.Walk a b}
    (h : BetweenMin G A B a b p) : Shortest p :=
  h.minimal a h.source b h.target

lemma BetweenMin.source_only {A B : Set V} {a b x : V} {p : G.Walk a b}
    (h : BetweenMin G A B a b p) (hx : x ∈ p.support) (hxA : x ∈ A) : x = a := by
  obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  have hh := h.minimal _ hxA b h.target (p.drop i)
  simp only [Walk.drop_length] at hh
  have : i = 0 := by omega
  simp [this]

lemma BetweenMin.target_only {A B : Set V} {a b x : V} {p : G.Walk a b}
    (h : BetweenMin G A B a b p) (hx : x ∈ p.support) (hxB : x ∈ B) : x = b := by
  obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  have hh := h.minimal a h.source _ hxB (p.take i)
  simp only [Walk.take_length, Nat.min_eq_left hi] at hh
  have : i = p.length := by omega
  simp [this]

lemma Shortest.isPath {a b : V} {p : G.Walk a b} (hp : Shortest p) : p.IsPath := by
  obtain ⟨q, hq⟩ := p.reachable.exists_walk_length_eq_dist
  apply p.isPath_of_length_eq_dist
  exact le_antisymm (hq ▸ hp q) (SimpleGraph.dist_le p)

structure MinimalConnector {ι : Type*} (G : SimpleGraph V) (N : ι → Set V) : Prop where
  connected : G.Connected
  interfaces : ∀ i, (N i).Nonempty
  minimal : ∀ S : Set V, (G.induce S).Connected → S ≠ Set.univ →
    ∃ i, Disjoint S (N i)

def Gate (G : SimpleGraph V) (N C : Set V) (v : V) : Prop :=
  ∀ a ∈ N, ∀ b ∈ C, ¬ReachOn G {x | x ≠ v} a b

lemma MinimalConnector.cycle_gate {ι : Type*} {N : ι → Set V}
    (h : MinimalConnector G N) {a v : V} {p : G.Walk a a}
    (hp : p.IsCycle) (hv : v ∈ p.support) :
    ∃ i, Gate G (N i) {x | x ∈ p.support} v := by
  have hc := cycle_delete_connected hp hv
  obtain ⟨b, hb⟩ := (connected_iff_reachOn.mp hc).1
  let D := component G {x | x ≠ v} b
  have hdconn : (G.induce D).Connected := component_connected (by simpa using hb.2)
  have hdproper : D ≠ Set.univ := by
    intro he
    have hh : v ∈ D := he ▸ Set.mem_univ v
    exact (component_subset _ _ hh) rfl
  obtain ⟨i, hi⟩ := h.minimal D hdconn hdproper
  refine ⟨i, ?_⟩
  intro x hx y hy hr
  have hy' : y ∈ ({x | x ∈ p.support} \ {v} : Set V) := ⟨hy, hr.right⟩
  have hby : ReachOn G {x | x ≠ v} b y :=
    (connected_reachOn hc hb hy').mono (fun _ hz => hz.2)
  exact Set.disjoint_left.mp hi (hby.trans hr.symm) hx

lemma Gate.mem_support {N C : Set V} {v a b : V} (h : Gate G N C v)
    (ha : a ∈ N) (hb : b ∈ C) (p : G.Walk a b) : v ∈ p.support := by
  by_contra hn
  exact h a ha b hb ⟨p, fun x hx he => hn (he ▸ hx)⟩

structure Tail {ι : Type*} (G : SimpleGraph V) (N : ι → Set V) (C : Set V) (v : V) where
  index : ι
  start : V
  path : G.Walk start v
  minimum : BetweenMin G (N index) C start v path
  gate : Gate G (N index) C v

lemma exists_tail {ι : Type*} {N : ι → Set V} (h : MinimalConnector G N)
    {C : Set V} (hC : C.Nonempty) {v : V} (hv : v ∈ C)
    (hg : ∃ i, Gate G (N i) C v) :
    Nonempty (Tail G N C v) := by
  obtain ⟨i,hi⟩ := hg
  obtain ⟨a,b,p,hp⟩ := exists_betweenMin h.connected (h.interfaces i) hC
  have he : v = b := hp.target_only (hi.mem_support hp.source hp.target p) hv
  subst b
  exact ⟨⟨i,a,p,hp,hi⟩⟩

lemma Tail.avoid {ι : Type*} {N : ι → Set V} {C : Set V} {v w : V}
    (t : Tail G N C v) (hw : w ∈ C) (hwv : w ≠ v) : w ∉ t.path.support :=
  fun h => hwv (t.minimum.target_only h hw)

lemma Tail.index_ne {ι : Type*} {N : ι → Set V} {C : Set V} {v w : V}
    (t : Tail G N C v) (s : Tail G N C w) (hv : v ∈ C) (hw : w ∈ C)
    (hvw : v ≠ w) : t.index ≠ s.index := by
  intro he
  have hh := s.gate.mem_support (he ▸ t.minimum.source) hv t.path
  exact t.avoid hw hvw.symm hh

lemma Tail.disjoint {ι : Type*} {N : ι → Set V} {C : Set V} {v w : V}
    (t : Tail G N C v) (s : Tail G N C w) (hv : v ∈ C)
    (hvw : v ≠ w) : Disjoint ({x | x ∈ t.path.support} : Set V)
      {x | x ∈ s.path.support} := by
  classical
  refine Set.disjoint_left.mpr ?_
  intro x hx hy
  have hxv : x ≠ v := by rintro rfl; exact s.avoid hv hvw hy
  have hp := Walk.endpoint_notMem_support_takeUntil t.minimum.shortest.isPath hx (Ne.symm hxv)
  have hs := s.avoid hv hvw
  have hh := t.gate.mem_support t.minimum.source s.minimum.target
    ((t.path.takeUntil x hx).append (s.path.dropUntil x hy))
  rcases (Walk.mem_support_append_iff ..).mp hh with hh | hh
  · exact hp hh
  · exact hs (s.path.support_dropUntil_subset_support hy hh)

lemma Tail.cross_edges {ι : Type*} {N : ι → Set V} {C : Set V} {v w x y : V}
    (t : Tail G N C v) (s : Tail G N C w) (hv : v ∈ C) (hw : w ∈ C)
    (hvw : v ≠ w) (hx : x ∈ t.path.support) (hy : y ∈ s.path.support)
    (hxy : G.Adj x y) : x = v ∧ y = w := by
  classical
  have hf : ∀ {v w x y : V} (t : Tail G N C v) (s : Tail G N C w),
      v ∈ C → v ≠ w → x ∈ t.path.support → y ∈ s.path.support →
      G.Adj x y → x = v := by
    intro v w x y t s hv hvw hx hy hxy
    by_contra hxv
    have hp := Walk.endpoint_notMem_support_takeUntil t.minimum.shortest.isPath hx (Ne.symm hxv)
    have hs := s.avoid hv hvw
    have hh := t.gate.mem_support t.minimum.source s.minimum.target
      ((t.path.takeUntil x hx).append ((s.path.dropUntil y hy).cons hxy))
    rcases (Walk.mem_support_append_iff ..).mp hh with hh | hh
    · exact hp hh
    · simp only [Walk.support_cons, List.mem_cons] at hh
      exact hh.elim (fun he => hxv he.symm)
        (fun hh => hs (s.path.support_dropUntil_subset_support hy hh))
  exact ⟨hf t s hv hvw hx hy hxy, hf s t hw hvw.symm hy hx hxy.symm⟩

lemma Tail.interface_avoid {ι : Type*} {N : ι → Set V} {C : Set V} {v w x : V}
    (t : Tail G N C v) (s : Tail G N C w) (hv : v ∈ C) (hvw : v ≠ w)
    (hx : x ∈ s.path.support) : x ∉ N t.index := by
  classical
  intro hn
  have hh := t.gate.mem_support hn s.minimum.target (s.path.dropUntil x hx)
  exact s.avoid hv hvw (s.path.support_dropUntil_subset_support hx hh)

structure SplitConnector {ι : Type*} (G : SimpleGraph V) (N : ι → Set V) where
  left : ι
  right : ι
  distinct : left ≠ right
  carrier : Set V
  connected : (G.induce carrier).Connected
  color : V → Fin 2
  proper : ∀ x ∈ carrier, ∀ y ∈ carrier, G.Adj x y → color x ≠ color y
  meets_left : (carrier ∩ N left).Nonempty
  meets_right : (carrier ∩ N right).Nonempty
  left_color : ∀ x ∈ carrier, x ∈ N left → color x = 0
  right_color : ∀ x ∈ carrier, x ∈ N right → color x = 1

def parity (n : ℕ) : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by decide)⟩

lemma parity_adj (n : ℕ) : parity n ≠ parity (n+1) := by
  intro he
  have hh := congrArg Fin.val he
  simp only [parity] at hh
  omega

lemma parity_add_one {n m : ℕ} (h : parity n = parity m) :
    parity (n+1) = parity (m+1) := by
  apply Fin.ext
  have hh := congrArg Fin.val h
  simp only [parity] at *
  omega

lemma Shortest.idxOf_getVert [DecidableEq V] {a b : V} {p : G.Walk a b}
    (hp : Shortest p) {n : ℕ} (hn : n ≤ p.length) : p.support.idxOf (p.getVert n) = n := by
  rw [p.getVert_eq_support_getElem hn]
  exact hp.isPath.support_nodup.idxOf_getElem n _

lemma Shortest.idxOf_endpoint [DecidableEq V] {a b : V} {p : G.Walk a b}
    (hp : Shortest p) : p.support.idxOf b = p.length := by
  simpa using hp.idxOf_getVert (le_refl p.length)

lemma Shortest.idxOf_start [DecidableEq V] {a b : V} {p : G.Walk a b}
    (hp : Shortest p) : p.support.idxOf a = 0 := by
  simpa using hp.idxOf_getVert (Nat.zero_le p.length)

lemma Shortest.parity_proper [DecidableEq V] {a b x y : V} {p : G.Walk a b}
    (hp : Shortest p) (hx : x ∈ p.support) (hy : y ∈ p.support) (hxy : G.Adj x y)
    (offset : ℕ) : parity (p.support.idxOf x + offset) ≠
      parity (p.support.idxOf y + offset) := by
  have hix : p.support.idxOf x ≤ p.length := by
    have := List.idxOf_lt_length_iff.mpr hx
    simpa only [Walk.length_support, Nat.lt_succ_iff] using this
  have hiy : p.support.idxOf y ≤ p.length := by
    have := List.idxOf_lt_length_iff.mpr hy
    simpa only [Walk.length_support, Nat.lt_succ_iff] using this
  have hh := hp.adj_indices hix hiy (by
    rw [p.getVert_support_idxOf hx, p.getVert_support_idxOf hy]; exact hxy)
  intro he
  have he' := congrArg Fin.val he
  simp only [parity] at he'
  rcases hh with hh | hh <;> omega

lemma connected_union_of_adj {A B : Set V} (hA : (G.induce A).Connected)
    (hB : (G.induce B).Connected) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (hab : G.Adj a b) : (G.induce (A ∪ B)).Connected := by
  have hr : ∀ x ∈ A ∪ B, ReachOn G (A ∪ B) a x := by
    intro x hx
    rcases hx with hx | hx
    · exact (connected_reachOn hA ha hx).mono Set.subset_union_left
    · exact (ReachOn.adj (G := G) (S := A ∪ B) (Or.inl ha) (Or.inr hb) hab).trans
        ((connected_reachOn hB hb hx).mono Set.subset_union_right)
  exact connected_iff_reachOn.mpr ⟨⟨a,Or.inl ha⟩, fun x hx y hy => (hr x hx).symm.trans (hr y hy)⟩

lemma tails_split {ι : Type*} {N : ι → Set V} {C : Set V} {v w : V}
    (t : Tail G N C v) (s : Tail G N C w) (hv : v ∈ C) (hw : w ∈ C)
    (hvw : G.Adj v w) (he : parity t.path.length = parity s.path.length) :
    Nonempty (SplitConnector G N) := by
  classical
  let A : Set V := {x | x ∈ t.path.support}
  let B : Set V := {x | x ∈ s.path.support}
  have hd : Disjoint A B := t.disjoint s hv hvw.ne
  let c : V → Fin 2 := fun x => if x ∈ A then parity (t.path.support.idxOf x)
    else parity (s.path.support.idxOf x + 1)
  have hcA : ∀ x ∈ A, c x = parity (t.path.support.idxOf x) :=
    fun x hx => ite_eq_left hx
  have hcB : ∀ x ∈ B, c x = parity (s.path.support.idxOf x + 1) :=
    fun x hx => ite_eq_right (fun hh => Set.disjoint_left.mp hd hh hx)
  refine ⟨{
    left := t.index, right := s.index,
    distinct := t.index_ne s hv hw hvw.ne, carrier := A ∪ B,
    connected := connected_union_of_adj t.path.connected_induce_support
      s.path.connected_induce_support t.path.end_mem_support s.path.end_mem_support hvw,
    color := c, proper := ?_, meets_left := ?_, meets_right := ?_,
    left_color := ?_, right_color := ?_ }⟩
  · intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hcA x hx, hcA y hy]
      simpa using t.minimum.shortest.parity_proper hx hy hxy 0
    · obtain ⟨hxv,hyw⟩ := t.cross_edges s hv hw hvw.ne hx hy hxy
      subst x; subst y
      rw [hcA v hx, hcB w hy, t.minimum.shortest.idxOf_endpoint,
        s.minimum.shortest.idxOf_endpoint, he]
      exact parity_adj _
    · obtain ⟨hxw,hyv⟩ := s.cross_edges t hw hv hvw.ne.symm hx hy hxy
      subst x; subst y
      rw [hcB w hx, hcA v hy, t.minimum.shortest.idxOf_endpoint,
        s.minimum.shortest.idxOf_endpoint, he]
      exact (parity_adj _).symm
    · rw [hcB x hx, hcB y hy]
      exact s.minimum.shortest.parity_proper hx hy hxy 1
  · exact ⟨t.start,Or.inl t.path.start_mem_support,t.minimum.source⟩
  · exact ⟨s.start,Or.inr s.path.start_mem_support,s.minimum.source⟩
  · intro x hx hn
    rcases hx with hx | hx
    · have hh := t.minimum.source_only hx hn
      subst x
      rw [hcA t.start hx, t.minimum.shortest.idxOf_start]
      rfl
    · exact (t.interface_avoid s hv hvw.ne hx hn).elim
  · intro x hx hn
    rcases hx with hx | hx
    · exact (s.interface_avoid t hw hvw.ne.symm hx hn).elim
    · have hh := s.minimum.source_only hx hn
      subst x
      rw [hcB s.start hx, s.minimum.shortest.idxOf_start]
      rfl

lemma MinimalConnector.two_colorable_or_split {ι : Type*} {N : ι → Set V}
    (h : MinimalConnector G N) : G.Colorable 2 ∨ Nonempty (SplitConnector G N) := by
  classical
  by_cases hs : Nonempty (SplitConnector G N)
  · exact Or.inr hs
  left
  apply two_colorable_of_cycles_even
  intro a p hp
  let C : Set V := {x | x ∈ p.support}
  have hC : C.Nonempty := ⟨a,p.start_mem_support⟩
  have ht : ∀ v : C, Nonempty (Tail G N C v) := fun v =>
    exists_tail h hC v.property (h.cycle_gate hp v.property)
  let tails : (v : C) → Tail G N C v := fun v => Classical.choice (ht v)
  have hc : (G.induce C).Colorable 2 := ⟨Coloring.mk
    (fun v => parity (tails v).path.length) (fun {v w} hvw he =>
      hs (tails_split (tails v) (tails w) v.property w.property hvw he))⟩
  have hh := SimpleGraph.two_colorable_iff_forall_loop_even.mp hc
    ⟨a,p.start_mem_support⟩ (p.induce C (fun _ hx => hx))
  have hl := Walk.length_map (p := p.induce C (fun _ hx => hx))
    (f := (Embedding.induce C).toHom)
  rw [Walk.map_induce] at hl
  exact hl.symm ▸ hh

noncomputable def extendColor (U : Set V) (c : U → Fin 2) (x : V) : Fin 2 := by
  classical
  exact if hx : x ∈ U then c ⟨x,hx⟩ else 0

lemma extendColor_apply {U : Set V} (c : U → Fin 2) {x : V} (hx : x ∈ U) :
    extendColor U c x = c ⟨x,hx⟩ := by simp [extendColor, hx]

lemma colorable_induce_iff_total {S : Set V} : (G.induce S).Colorable 2 ↔
    ∃ c : V → Fin 2, ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → c x ≠ c y := by
  constructor
  · rintro ⟨c⟩
    refine ⟨extendColor S c, fun x hx y hy hxy => ?_⟩
    simpa only [extendColor_apply c hx, extendColor_apply c hy] using
      c.valid (show (G.induce S).Adj ⟨x,hx⟩ ⟨y,hy⟩ from hxy)
  · rintro ⟨c,hc⟩
    exact ⟨Coloring.mk (fun x => c x) (fun {x y} hxy => hc x x.property y y.property hxy)⟩

lemma connected_image_val {U : Set V} {S : Set U}
    (h : ((G.induce U).induce S).Connected) :
    (G.induce (Subtype.val '' S)).Connected := by
  obtain ⟨hne, hc⟩ := connected_iff_reachOn.mp h
  refine connected_iff_reachOn.mpr ⟨hne.image _, ?_⟩
  rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩
  obtain ⟨p,hp⟩ := hc a ha b hb
  refine ⟨p.map (Embedding.induce U).toHom, ?_⟩
  intro x hx
  have hh : x ∈ p.support.map (Embedding.induce U).toHom := (Walk.support_map ..) ▸ hx
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hh
  exact ⟨z,hp z hz,rfl⟩

lemma colorable_image_val {U : Set V} {S : Set U}
    (h : ((G.induce U).induce S).Colorable 2) :
    (G.induce (Subtype.val '' S)).Colorable 2 := by
  obtain ⟨c,hc⟩ := colorable_induce_iff_total.mp h
  apply colorable_induce_iff_total.mpr
  refine ⟨extendColor U c, ?_⟩
  rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩ hxy
  simpa only [extendColor_apply c a.property, extendColor_apply c b.property] using
    hc a ha b hb hxy

noncomputable def SplitConnector.lift {ι : Type*} {U : Set V} {N : ι → Set V}
    (s : SplitConnector (G.induce U) (fun i => {x | x.val ∈ N i})) :
    SplitConnector G N where
  left := s.left
  right := s.right
  distinct := s.distinct
  carrier := Subtype.val '' s.carrier
  connected := connected_image_val s.connected
  color := extendColor U s.color
  proper := by
    rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩ hxy
    simpa only [extendColor_apply s.color a.property, extendColor_apply s.color b.property] using
      s.proper a ha b hb hxy
  meets_left := by
    obtain ⟨a,ha,hn⟩ := s.meets_left
    exact ⟨a,⟨a,ha,rfl⟩,hn⟩
  meets_right := by
    obtain ⟨a,ha,hn⟩ := s.meets_right
    exact ⟨a,⟨a,ha,rfl⟩,hn⟩
  left_color := by
    rintro x ⟨a,ha,rfl⟩ hn
    simpa only [extendColor_apply s.color a.property] using s.left_color a ha hn
  right_color := by
    rintro x ⟨a,ha,rfl⟩ hn
    simpa only [extendColor_apply s.color a.property] using s.right_color a ha hn

lemma SplitConnector.lift_subset {ι : Type*} {U : Set V} {N : ι → Set V}
    (s : SplitConnector (G.induce U) (fun i => {x | x.val ∈ N i})) :
    s.lift.carrier ⊆ U := by
  rintro x ⟨a,ha,rfl⟩
  exact a.property

lemma exists_minimal_transversal [Finite V] {ι : Type*} {N : ι → Set V}
    (hG : G.Connected) (hN : ∀ i, (N i).Nonempty) :
    ∃ U : Set V, (∀ i, (U ∩ N i).Nonempty) ∧
      MinimalConnector (G.induce U) (fun i => {x | x.val ∈ N i}) := by
  classical
  have := hG.nonempty
  let P : Set V → Prop := fun U => (G.induce U).Connected ∧ ∀ i, (U ∩ N i).Nonempty
  have hp : P Set.univ := by
    refine ⟨?_, fun i => by simpa using hN i⟩
    apply connected_iff_reachOn.mpr
    refine ⟨Set.univ_nonempty, fun a _ b _ => ?_⟩
    obtain ⟨p⟩ := hG a b
    exact ⟨p,fun _ _ => trivial⟩
  have hex : ∃ n : ℕ, ∃ U : Set V, P U ∧ U.ncard = n :=
    ⟨(Set.univ : Set V).ncard,Set.univ,hp,rfl⟩
  obtain ⟨U,hU,hu⟩ := Nat.find_spec hex
  have hmin : ∀ T : Set V, P T → U.ncard ≤ T.ncard := by
    intro T hT
    rw [hu]
    exact Nat.find_min' hex ⟨T,hT,rfl⟩
  refine ⟨U,hU.2,⟨hU.1,?_,?_⟩⟩
  · intro i
    obtain ⟨a,ha,hn⟩ := hU.2 i
    exact ⟨⟨a,ha⟩,hn⟩
  · intro S hS hproper
    by_contra hmiss
    push Not at hmiss
    have hmeet : ∀ i, ((Subtype.val '' S) ∩ N i).Nonempty := by
      intro i
      have hh := Set.not_disjoint_iff.mp (hmiss i)
      obtain ⟨a,ha,hn⟩ := hh
      exact ⟨a,⟨a,ha,rfl⟩,hn⟩
    have him : (Subtype.val '' S : Set V) ⊆ U := by
      rintro _ ⟨a,ha,rfl⟩
      exact a.property
    have hstrict : (Subtype.val '' S : Set V) ⊂ U := by
      refine ⟨him, ?_⟩
      intro he
      apply hproper
      apply Set.eq_univ_of_forall
      intro a
      obtain ⟨b,hb,hab⟩ := he a.property
      have : b = a := Subtype.ext hab
      simpa [this] using hb
    have hc : (Subtype.val '' S : Set V).ncard < U.ncard :=
      Set.ncard_lt_ncard hstrict
    have hh := hmin (Subtype.val '' S) ⟨connected_image_val hS,hmeet⟩
    omega

lemma connected_transversal_or_split [Finite V] {ι : Type*} {N : ι → Set V}
    (hG : G.Connected) (hN : ∀ i, (N i).Nonempty) :
    (∃ U : Set V, (G.induce U).Connected ∧ (∀ i, (U ∩ N i).Nonempty) ∧
      (G.induce U).Colorable 2) ∨ Nonempty (SplitConnector G N) := by
  obtain ⟨U,hU,hm⟩ := exists_minimal_transversal hG hN
  rcases hm.two_colorable_or_split with hc | hs
  · exact Or.inl ⟨U,hm.connected,hU,hc⟩
  · exact Or.inr ⟨(Classical.choice hs).lift⟩

lemma connected_transversal_or_split_on [Finite V] {ι : Type*} {N : ι → Set V}
    {X : Set V} (hX : (G.induce X).Connected)
    (hN : ∀ i, (X ∩ N i).Nonempty) :
    (∃ U : Set V, U ⊆ X ∧ (G.induce U).Connected ∧ (∀ i, (U ∩ N i).Nonempty) ∧
      (G.induce U).Colorable 2) ∨
    ∃ s : SplitConnector G N, s.carrier ⊆ X := by
  have hN' : ∀ i, ({x : X | x.val ∈ N i} : Set X).Nonempty := by
    intro i
    obtain ⟨a,ha,hn⟩ := hN i
    exact ⟨⟨a,ha⟩,hn⟩
  rcases connected_transversal_or_split hX hN' with ⟨U,hU,hn,hc⟩ | hs
  · left
    refine ⟨Subtype.val '' U, ?_,connected_image_val hU,?_,colorable_image_val hc⟩
    · rintro _ ⟨a,ha,rfl⟩
      exact a.property
    · intro i
      obtain ⟨a,ha,hn⟩ := hn i
      exact ⟨a,⟨a,ha,rfl⟩,hn⟩
  · let s := Classical.choice hs
    exact Or.inr ⟨s.lift,s.lift_subset⟩

def Touch (G : SimpleGraph V) (A B : Set V) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, G.Adj a b

lemma Touch.symm {A B : Set V} (h : Touch G A B) : Touch G B A := by
  obtain ⟨a,ha,b,hb,hab⟩ := h
  exact ⟨b,hb,a,ha,hab.symm⟩

lemma Touch.mono {A B A' B' : Set V} (h : Touch G A B) (hA : A ⊆ A') (hB : B ⊆ B') :
    Touch G A' B' := by
  obtain ⟨a,ha,b,hb,hab⟩ := h
  exact ⟨a,hA ha,b,hB hb,hab⟩

lemma Touch.left_nonempty {A B : Set V} (h : Touch G A B) : A.Nonempty := by
  obtain ⟨a,ha,_,_,_⟩ := h
  exact ⟨a,ha⟩

lemma Touch.right_nonempty {A B : Set V} (h : Touch G A B) : B.Nonempty := h.symm.left_nonempty

lemma touch_union_left {A B C : Set V} : Touch G (A ∪ B) C ↔ Touch G A C ∨ Touch G B C := by
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    exact ha.elim (fun ha => Or.inl ⟨a,ha,b,hb,hab⟩) (fun ha => Or.inr ⟨a,ha,b,hb,hab⟩)
  · rintro (⟨a,ha,b,hb,hab⟩ | ⟨a,ha,b,hb,hab⟩)
    · exact ⟨a,Or.inl ha,b,hb,hab⟩
    · exact ⟨a,Or.inr ha,b,hb,hab⟩

lemma touch_union_right {A B C : Set V} : Touch G A (B ∪ C) ↔ Touch G A B ∨ Touch G A C := by
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    exact hb.elim (fun hb => Or.inl ⟨a,ha,b,hb,hab⟩) (fun hb => Or.inr ⟨a,ha,b,hb,hab⟩)
  · rintro (⟨a,ha,b,hb,hab⟩ | ⟨a,ha,b,hb,hab⟩)
    · exact ⟨a,ha,b,Or.inl hb,hab⟩
    · exact ⟨a,ha,b,Or.inr hb,hab⟩

lemma connected_union_of_touch {A B : Set V} (hA : (G.induce A).Connected)
    (hB : (G.induce B).Connected) (ht : Touch G A B) : (G.induce (A ∪ B)).Connected := by
  obtain ⟨a,ha,b,hb,hab⟩ := ht
  exact connected_union_of_adj hA hB ha hb hab

def Independent (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬G.Adj a b

lemma independent_empty : Independent G ∅ := by simp [Independent]

lemma Independent.mono {S T : Set V} (h : Independent G T) (hst : S ⊆ T) :
    Independent G S := fun a ha b hb => h a (hst ha) b (hst hb)

lemma independent_union {S T : Set V} (hS : Independent G S) (hT : Independent G T)
    (hnt : ¬Touch G S T) : Independent G (S ∪ T) := by
  intro a ha b hb hab
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hS a ha b hb hab
  · exact hnt ⟨a,ha,b,hb,hab⟩
  · exact hnt ⟨b,hb,a,ha,hab.symm⟩
  · exact hT a ha b hb hab

end ReedSeymour

end OAI
