import OAI.Combinatorics.VariableWL.PortGraph

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.TypedGame
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable1} {W : Type uVariable2} [Fintype V] [Fintype W]

noncomputable abbrev numbered (G : SimpleGraph V) : Graph :=
  ⟨Fintype.card V,G.comap (Fintype.equivFin V).symm⟩

noncomputable def numbering (G : SimpleGraph V) : G ≃g (numbered G).graph where
  toEquiv := Fintype.equivFin V
  map_rel_iff' := by intro x y; change G.Adj _ _ ↔ _; simp

abbrev Position (V : Type uVariable3) (W : Type uVariable4) (q : ℕ) := Fin q → Option (V × W)

noncomputable def encode {q : ℕ} (p : Position V W q) :
    Game.Position (numbered (⊥ : SimpleGraph V)) (numbered (⊥ : SimpleGraph W)) q :=
  fun i => (p i).map (fun z => (Fintype.equivFin V z.1,Fintype.equivFin W z.2))

noncomputable def decode {q : ℕ}
    (p : Game.Position (numbered (⊥ : SimpleGraph V)) (numbered (⊥ : SimpleGraph W)) q) :
    Position V W q :=
  fun i => (p i).map (fun z => ((Fintype.equivFin V).symm z.1,(Fintype.equivFin W).symm z.2))

theorem encode_decode {q : ℕ}
    (p : Game.Position (numbered (⊥ : SimpleGraph V)) (numbered (⊥ : SimpleGraph W)) q) :
    encode (decode p) = p := by
  funext i
  cases h : p i <;> simp [encode,decode,h]

theorem decode_encode {q : ℕ} (p : Position V W q) : decode (encode p) = p := by
  funext i
  cases h : p i <;> simp [encode,decode,h]

def Winning (G : SimpleGraph V) (H : SimpleGraph W) {q : ℕ} (p : Position V W q) : Prop :=
  Game.Winning (G := numbered G) (H := numbered H) (encode p)

theorem Winning.partialIso {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    {p : Position V W q} (hp : Winning G H p) {i j : Fin q} {a c : V} {b d : W}
    (hi : p i = some (a,b)) (hj : p j = some (c,d)) :
    (a=c ↔ b=d) ∧ (G.Adj a c ↔ H.Adj b d) := by
  have hh := Game.Winning.partialIso hp i j (Fintype.equivFin V a,Fintype.equivFin W b)
    (Fintype.equivFin V c,Fintype.equivFin W d) (by simp [encode,hi]) (by simp [encode,hj])
  simpa only [(Fintype.equivFin V).injective.eq_iff,(Fintype.equivFin W).injective.eq_iff,
    SimpleGraph.comap_adj,Equiv.symm_apply_apply] using hh

theorem Winning.discard {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    {p p' : Position V W q} (hp : Winning G H p)
    (hs : ∀ i a, p' i = some a → p i = some a) : Winning G H p' := by
  apply Game.Winning.discard hp
  intro i a ha
  obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp ha
  simp [encode,hs i b hb]

theorem encode_update {q : ℕ} (p : Position V W q) (i : Fin q) (a : V) (b : W) :
    encode (Function.update p i (some (a,b))) =
      Function.update (encode p) i (some (Fintype.equivFin V a,Fintype.equivFin W b)) := by
  classical
  funext j
  by_cases hij : j=i <;> simp [encode,hij]

theorem Winning.move {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    {p : Position V W q} (hp : Winning G H p) (i : Fin q) (hi : p i = none) :
    ∃ e : V ≃ W, ∀ v, Winning G H (Function.update p i (some (v,e v))) := by
  obtain ⟨e,he⟩ := Game.Winning.move hp i (by simp [encode,hi])
  let f := (Fintype.equivFin V).trans (e.trans (Fintype.equivFin W).symm)
  refine ⟨f,fun v => ?_⟩
  change Game.Winning _
  rw [encode_update]
  simpa only [f,Equiv.trans_apply,Equiv.apply_symm_apply] using he (Fintype.equivFin V v)

theorem Winning.degree_eq {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    (hq : 2 ≤ q) {p : Position V W q} (hp : Winning G H p) {i : Fin q} {a : V} {b : W}
    (hi : p i = some (a,b)) : G.degree a = H.degree b := by
  have hh := Game.Winning.degree_eq hq hp (i := i) (a := Fintype.equivFin V a) (b := Fintype.equivFin W b) (by simp only [encode,hi,Option.map_some])
  exact ((numbering G).degree_eq a).symm.trans (hh.trans ((numbering H).degree_eq b))

def keep {q : ℕ} (p : Position V W q) (s : Finset (Fin q)) : Position V W q :=
  fun i => if i ∈ s then p i else none

theorem Winning.keep {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    {p : Position V W q} (hp : Winning G H p) (s : Finset (Fin q)) : Winning G H (keep p s) := by
  apply hp.discard
  intro i a ha
  by_cases hi : i ∈ s
  · simpa [TypedGame.keep,hi] using ha
  · simp [TypedGame.keep,hi] at ha

end VariableWL.TypedGame

namespace VariableWL.Game

def swap {G H : Graph} {q : ℕ} (p : Position G H q) : Position H G q :=
  fun i => (p i).map Prod.swap

theorem swap_swap {G H : Graph} {q : ℕ} (p : Position G H q) : swap (swap p) = p := by
  funext i
  cases h : p i <;> simp [swap,h]

theorem swap_update {G H : Graph} {q : ℕ} (p : Position G H q)
    (i : Fin q) (a : Fin G.order) (b : Fin H.order) :
    swap (Function.update p i (some (a,b))) = Function.update (swap p) i (some (b,a)) := by
  classical
  funext j
  by_cases h : j=i <;> simp [swap,h]

theorem Winning.symm {G H : Graph} {q : ℕ} {p : Position G H q} (hp : Winning p) : Winning (swap p) := by
  classical
  refine ⟨{s | Winning (swap s)},?_,?_,?_,?_⟩
  · simpa only [Set.mem_ofPred_eq,swap_swap] using hp
  · intro s hs i j a b hi hj
    have ha : swap s i = some (a.2,a.1) := by simp [swap,hi,Prod.swap]
    have hb : swap s j = some (b.2,b.1) := by simp [swap,hj,Prod.swap]
    have h := hs.partialIso i j _ _ ha hb
    exact ⟨h.1.symm,h.2.symm⟩
  · intro s hs s' hsub
    apply hs.discard
    intro i a ha
    obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp ha
    simp only [swap,hsub i b hb,Option.map_some,he]
  · intro s hs i hi
    obtain ⟨e,he⟩ := hs.move i (by simp [swap,hi])
    refine ⟨e.symm,fun v => ?_⟩
    change Winning (swap (Function.update s i (some (v,e.symm v))))
    rw [swap_update]
    simpa only [Equiv.apply_symm_apply] using he (e.symm v)
end VariableWL.Game

namespace VariableWL.TypedGame
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable5} {W : Type uVariable6} [Fintype V] [Fintype W]

def swap {q : ℕ} (p : Position V W q) : Position W V q := fun i => (p i).map Prod.swap

theorem Winning.symm {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    {p : Position V W q} (hp : Winning G H p) : Winning H G (swap p) := by
  have he : encode (swap p) = Game.swap (encode p) := by
    funext i
    cases h : p i <;> simp [encode,swap,Game.swap,h]
  change Game.Winning _
  rw [he]
  exact Game.Winning.symm hp

theorem spare {q : ℕ} (hq : 3 ≤ q) (i j : Fin q) : ∃ l : Fin q, l ≠ i ∧ l ≠ j := by
  classical
  have hc : ({i,j} : Finset (Fin q)).card < (Finset.univ : Finset (Fin q)).card := by
    have hl : ({i,j} : Finset (Fin q)).card ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
    simpa only [Finset.card_univ,Fintype.card_fin] using lt_of_le_of_lt hl (by omega : 2 < q)
  obtain ⟨l,_,hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨l,?_⟩
  simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hl

def Triangle (G : SimpleGraph V) (v : V) : Prop :=
  ∃ a b, G.Adj v a ∧ G.Adj a b ∧ G.Adj b v

theorem Winning.triangle_forward {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    (hq : 3 ≤ q) {p : Position V W q} (hp : Winning G H p)
    {i : Fin q} {v : V} {w : W} (hi : p i = some (v,w)) (hv : Triangle G v) : Triangle H w := by
  classical
  obtain ⟨a,b,hva,hab,hbv⟩ := hv
  obtain ⟨j,hji,_⟩ := spare hq i i
  obtain ⟨l,hli,hlj⟩ := spare hq i j
  let p0 := TypedGame.keep p {i}
  have h0 := hp.keep {i}
  obtain ⟨e,he⟩ := h0.move j (by simp [TypedGame.keep,hji])
  let p1 := Function.update p0 j (some (a,e a))
  have h1 : Winning G H p1 := he a
  have hi1 : p1 i = some (v,w) := by simp [p1,p0,TypedGame.keep,Function.update_of_ne hji.symm,hi]
  have hj1 : p1 j = some (a,e a) := by simp [p1]
  obtain ⟨f,hf⟩ := h1.move l (by simp [p1,p0,TypedGame.keep,hlj,hli])
  let p2 := Function.update p1 l (some (b,f b))
  have h2 : Winning G H p2 := hf b
  have hi2 : p2 i = some (v,w) := by simp [p2,Function.update_of_ne hli.symm,hi1]
  have hj2 : p2 j = some (a,e a) := by simp [p2,Function.update_of_ne hlj.symm,hj1]
  have hl2 : p2 l = some (b,f b) := by simp [p2]
  exact ⟨e a,f b,(h2.partialIso hi2 hj2).2.mp hva,
    (h2.partialIso hj2 hl2).2.mp hab,(h2.partialIso hl2 hi2).2.mp hbv⟩

theorem Winning.triangle_iff {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    (hq : 3 ≤ q) {p : Position V W q} (hp : Winning G H p)
    {i : Fin q} {v : V} {w : W} (hi : p i = some (v,w)) : Triangle G v ↔ Triangle H w := by
  refine ⟨hp.triangle_forward hq hi,?_⟩
  exact hp.symm.triangle_forward hq (i := i) (by simp [TypedGame.swap,hi])

def Tail (G : SimpleGraph V) : ℕ → V → V → Prop
  | 0,_,v => G.degree v = 1
  | n+1,u,v => G.degree v = 2 ∧ ∃ w, w ≠ u ∧ G.Adj v w ∧ Tail G n v w

theorem Winning.tail_forward {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    (hq : 3 ≤ q) (n : ℕ) {p : Position V W q} (hp : Winning G H p)
    {i j : Fin q} {a b : V} {c d : W} (hi : p i = some (a,c)) (hj : p j = some (b,d)) :
    Tail G n a b → Tail H n c d := by
  classical
  induction n generalizing p i j a b c d with
  | zero => intro hh; change H.degree d = 1; exact (hp.degree_eq (by omega) hj).symm.trans hh
  | succ n ih =>
    rintro ⟨hd,v,hva,hbv,hv⟩
    refine ⟨(hp.degree_eq (by omega) hj).symm.trans hd,?_⟩
    obtain ⟨l,hli,hlj⟩ := spare hq i j
    let p0 := TypedGame.keep p {i,j}
    have h0 := hp.keep {i,j}
    obtain ⟨e,he⟩ := h0.move l (by simp [TypedGame.keep,hli,hlj])
    let p1 := Function.update p0 l (some (v,e v))
    have h1 : Winning G H p1 := he v
    have hi1 : p1 i = some (a,c) := by simp [p1,p0,TypedGame.keep,Function.update_of_ne hli.symm,hi]
    have hj1 : p1 j = some (b,d) := by simp [p1,p0,TypedGame.keep,Function.update_of_ne hlj.symm,hj]
    have hl1 : p1 l = some (v,e v) := by simp [p1]
    exact ⟨e v,fun h => hva ((h1.partialIso hl1 hi1).1.mpr h),
      (h1.partialIso hj1 hl1).2.mp hbv,ih h1 hj1 hl1 hv⟩

end VariableWL.TypedGame

namespace VariableWL.TypedGame
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable7} {W : Type uVariable8} [Fintype V] [Fintype W]

def ColorTag (G : SimpleGraph V) (t : ℕ) (v : V) : Prop :=
  0 < t ∧ Triangle G v ∧ ∃ c, G.Adj v c ∧ ¬ Triangle G c ∧
    ∃ y, G.Adj c y ∧ y ≠ v ∧ G.degree y ≤ 2 ∧ Tail G (t-1) c y

theorem Winning.colorTag_forward {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    (hq : 3 ≤ q) {p : Position V W q} (hp : Winning G H p) {t : ℕ}
    {i : Fin q} {v : V} {w : W} (hi : p i = some (v,w)) : ColorTag G t v → ColorTag H t w := by
  classical
  rintro ⟨ht,htv,c,hvc,hct,y,hcy,hyv,hdy,htail⟩
  refine ⟨ht,(hp.triangle_iff hq hi).mp htv,?_⟩
  obtain ⟨j,hji,_⟩ := spare hq i i
  obtain ⟨l,hli,hlj⟩ := spare hq i j
  let p0 := TypedGame.keep p {i}
  have h0 := hp.keep {i}
  obtain ⟨e,he⟩ := h0.move j (by simp [TypedGame.keep,hji])
  let p1 := Function.update p0 j (some (c,e c))
  have h1 : Winning G H p1 := he c
  have hi1 : p1 i = some (v,w) := by simp [p1,p0,TypedGame.keep,Function.update_of_ne hji.symm,hi]
  have hj1 : p1 j = some (c,e c) := by simp [p1]
  refine ⟨e c,(h1.partialIso hi1 hj1).2.mp hvc,fun h => hct ((h1.triangle_iff hq hj1).mpr h),?_⟩
  obtain ⟨f,hf⟩ := h1.move l (by simp [p1,p0,TypedGame.keep,hlj,hli])
  let p2 := Function.update p1 l (some (y,f y))
  have h2 : Winning G H p2 := hf y
  have hi2 : p2 i = some (v,w) := by simp [p2,Function.update_of_ne hli.symm,hi1]
  have hj2 : p2 j = some (c,e c) := by simp [p2,Function.update_of_ne hlj.symm,hj1]
  have hl2 : p2 l = some (y,f y) := by simp [p2]
  refine ⟨f y,(h2.partialIso hj2 hl2).2.mp hcy,fun h => hyv ((h2.partialIso hl2 hi2).1.mpr h),?_,?_⟩
  · rw [← h2.degree_eq (by omega) hl2]; exact hdy
  · exact h2.tail_forward hq (t-1) hj2 hl2 htail

end VariableWL.TypedGame

namespace VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable9} [Fintype V] (Y : PortGraph V) (color : V → ℕ)
variable (hcolor : ∀ v, 0 < color v)
include hcolor

theorem high_degree_one_iff (x : Vertex color) (hx : 2 ≤ x.level) :
    (graph Y color).degree x = 1 ↔ x.level = color x.owner+1 := by
  constructor
  · intro hd
    by_contra he
    have hb : x.level < color x.owner+1 := by have := x.bound; omega
    have ht := intermediate_degree Y color x hx hb
    omega
  · exact terminal_degree Y color hcolor x

theorem tail_iff (m : ℕ) (prev x : Vertex color) (hx : 2 ≤ x.level)
    (ho : prev.owner=x.owner) (hp : prev.port=x.port) (hl : prev.level+1=x.level) :
    TypedGame.Tail (graph Y color) m prev x ↔ m+x.level=color x.owner+1 := by
  induction m generalizing prev x with
  | zero => simpa only [TypedGame.Tail,zero_add] using high_degree_one_iff Y color hcolor x hx
  | succ m ih =>
    constructor
    · rintro ⟨_,y,hyp,ha,ht⟩
      obtain ⟨hoy,hpy,hly⟩ := (high_adj Y color hx).mp ha
      have hyup : x.level+1=y.level := by
        rcases hly with h | h
        · exact h
        · exfalso
          apply hyp
          exact Vertex.ext (hoy.symm.trans ho.symm) (hpy.symm.trans hp.symm) (by omega)
      have hh := (ih x y (by omega) hoy hpy hyup).mp ht
      rw [← hoy] at hh
      omega
    · intro hh
      have hxb : x.level < color x.owner+1 := by omega
      let y : Vertex color := ⟨x.owner,x.port,x.level+1,by omega⟩
      refine ⟨intermediate_degree Y color x hx hxb,y,?_,?_,?_⟩
      · intro he
        have := congrArg Vertex.level he
        dsimp [y] at this
        omega
      · exact (high_adj Y color hx).mpr ⟨rfl,rfl,Or.inl rfl⟩
      · apply (ih x y (by dsimp [y]; omega) rfl rfl rfl).mpr
        dsimp [y]
        omega

omit hcolor [Fintype V] in
theorem connector_adj (v : V) (j : Fin 3) (y : Vertex color) :
    (graph Y color).Adj (Vertex.connector v j) y ↔
    y = Vertex.triangle v j ∨
      (y.owner=v ∧ y.port=j ∧ y.level=2) ∨
      (y.level=1 ∧ Y.edge (v,j) (y.owner,y.port)) := by
  constructor
  · rintro (h | h)
    · obtain ⟨ho,hp,hl⟩ := internal_of_nontriangle color (by simp [Vertex.connector]) h
      rcases hl with hl | hl
      · exact Or.inr (Or.inl ⟨ho.symm,hp.symm,hl.symm⟩)
      · exact Or.inl (Vertex.ext ho.symm hp.symm (by change y.level+1=1 at hl; dsimp [Vertex.triangle]; omega))
    · exact Or.inr (Or.inr ⟨h.2.1,h.2.2⟩)
  · rintro (rfl | ⟨ho,hp,hl⟩ | ⟨hl,he⟩)
    · exact Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inr rfl⟩⟩
    · exact Or.inl ⟨ho.symm,Or.inr ⟨hp.symm,Or.inl hl.symm⟩⟩
    · exact Or.inr ⟨rfl,hl,he⟩

theorem first_path_recognized {v : V} {j : Fin 3} {y : Vertex color}
    (ha : (graph Y color).Adj (Vertex.connector v j) y)
    (hne : y ≠ Vertex.triangle v j) (hd : (graph Y color).degree y ≤ 2) :
    y.owner=v ∧ y.port=j ∧ y.level=2 := by
  rcases (connector_adj Y color v j y).mp ha with h | h | ⟨hl,he⟩
  · exact (hne h).elim
  · exact h
  · have hy : y = Vertex.connector y.owner y.port := Vertex.ext rfl rfl hl
    have hdeg := connector_used_degree Y color hcolor (Y.symm he)
    rw [hy] at hd
    omega

theorem colorTag_iff (t : ℕ) (x : Vertex color) :
    TypedGame.ColorTag (graph Y color) t x ↔ x.level=0 ∧ t=color x.owner := by
  constructor
  · rintro ⟨ht,htri,c,hxc,hct,y,hcy,hyx,hdy,htail⟩
    have hx := (triangle_characterization Y color x).mp htri
    have hxe : x = Vertex.triangle x.owner x.port := Vertex.ext rfl rfl hx
    have hc : c = Vertex.connector x.owner x.port := by
      rw [hxe] at hxc
      rcases (triangle_adj Y color _ _).mp hxc with ⟨_,hc0,_⟩ | hc
      · exact (hct ((triangle_characterization Y color _).mpr hc0)).elim
      · exact hc
    subst c
    have hy := first_path_recognized Y color hcolor hcy (by simpa only [← hxe] using hyx) hdy
    have hlen := (tail_iff Y color hcolor (t-1) (Vertex.connector x.owner x.port) y (by omega)
      hy.1.symm hy.2.1.symm (by dsimp [Vertex.connector]; omega)).mp htail
    rw [hy.1] at hlen
    exact ⟨hx,by omega⟩
  · rintro ⟨hx,rfl⟩
    let y : Vertex color := ⟨x.owner,x.port,2,by have := hcolor x.owner; omega⟩
    refine ⟨hcolor x.owner,(triangle_characterization Y color x).mpr hx,
      Vertex.connector x.owner x.port,?_,?_,y,?_,?_,high_degree_le_two Y color y (by rfl),?_⟩
    · exact Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inl (by dsimp [Vertex.connector]; omega)⟩⟩
    · change ¬ (∃ a b, (graph Y color).Adj (Vertex.connector x.owner x.port) a ∧
          (graph Y color).Adj a b ∧ (graph Y color).Adj b (Vertex.connector x.owner x.port))
      rw [triangle_characterization]
      simp [Vertex.connector]
    · exact Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inl rfl⟩⟩
    · intro he
      have := congrArg Vertex.level he
      dsimp [y] at this
      omega
    · apply (tail_iff Y color hcolor _ (Vertex.connector x.owner x.port) y (by rfl) rfl rfl rfl).mpr
      dsimp [y]
      have := hcolor x.owner
      omega

end VariableWL.SubcubicRealization

end OAI
