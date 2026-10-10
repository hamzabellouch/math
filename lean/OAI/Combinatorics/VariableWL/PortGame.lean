import OAI.Combinatorics.VariableWL.TypedGame

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7

namespace VariableWL.TypedGame
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable1} {W : Type uVariable2} [Fintype V] [Fintype W]

def Preserved (G : SimpleGraph V) (H : SimpleGraph W) (q : ℕ)
    (R : V → V → Prop) (S : W → W → Prop) : Prop :=
  ∀ (p : Position V W q), Winning G H p → ∀ {i j a b c d},
    p i = some (a,c) → p j = some (b,d) → R a b → S c d

def Compose {A : Type uVariable3} (R S : A → A → Prop) (a b : A) : Prop := ∃ m, R a m ∧ S m b

theorem Preserved.compose {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ} (hq : 3 ≤ q)
    {R R' : V → V → Prop} {S S' : W → W → Prop}
    (hR : Preserved G H q R S) (hT : Preserved G H q R' S') :
    Preserved G H q (Compose R R') (Compose S S') := by
  classical
  intro p hp i j a b c d hi hj hm
  obtain ⟨m,ham,hmb⟩ := hm
  obtain ⟨l,hli,hlj⟩ := spare hq i j
  let p0 := TypedGame.keep p {i,j}
  have h0 := hp.keep {i,j}
  obtain ⟨e,he⟩ := h0.move l (by simp [TypedGame.keep,hli,hlj])
  let p1 := Function.update p0 l (some (m,e m))
  have h1 : Winning G H p1 := he m
  have hi1 : p1 i = some (a,c) := by simp [p1,p0,TypedGame.keep,Function.update_of_ne hli.symm,hi]
  have hj1 : p1 j = some (b,d) := by simp [p1,p0,TypedGame.keep,Function.update_of_ne hlj.symm,hj]
  have hl1 : p1 l = some (m,e m) := by simp [p1]
  exact ⟨e m,hR p1 h1 hi1 hl1 ham,hT p1 h1 hl1 hj1 hmb⟩

theorem Preserved.flip {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    {R : V → V → Prop} {S : W → W → Prop} (h : Preserved G H q R S) :
    Preserved G H q (fun a b => R b a) (fun a b => S b a) := by
  intro p hp i j a b c d hi hj hr
  exact h p hp hj hi hr

theorem adjacency_preserved (G : SimpleGraph V) (H : SimpleGraph W) (q : ℕ) :
    Preserved G H q G.Adj H.Adj := by
  intro p hp i j a b c d hi hj ha
  exact (hp.partialIso hi hj).2.mp ha

def SameTriangle (G : SimpleGraph V) (a b : V) : Prop :=
  Triangle G a ∧ Triangle G b ∧ (a=b ∨ G.Adj a b)

def Exit (G : SimpleGraph V) (a b : V) : Prop :=
  Triangle G a ∧ ¬ Triangle G b ∧ G.Adj a b

def Access (G : SimpleGraph V) : V → V → Prop := Compose (SameTriangle G) (Exit G)

def UnderlyingEdge (G : SimpleGraph V) : V → V → Prop :=
  Compose (Access G) (Compose G.Adj (fun a b => Access G b a))

theorem sameTriangle_preserved {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ} (hq : 3 ≤ q) :
    Preserved G H q (SameTriangle G) (SameTriangle H) := by
  intro p hp i j a b c d hi hj h
  refine ⟨(hp.triangle_iff hq hi).mp h.1,(hp.triangle_iff hq hj).mp h.2.1,?_⟩
  rcases h.2.2 with he | ha
  · exact Or.inl ((hp.partialIso hi hj).1.mp he)
  · exact Or.inr ((hp.partialIso hi hj).2.mp ha)

theorem exit_preserved {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ} (hq : 3 ≤ q) :
    Preserved G H q (Exit G) (Exit H) := by
  intro p hp i j a b c d hi hj h
  exact ⟨(hp.triangle_iff hq hi).mp h.1,fun hh => h.2.1 ((hp.triangle_iff hq hj).mpr hh),
    (hp.partialIso hi hj).2.mp h.2.2⟩

theorem access_preserved {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ} (hq : 3 ≤ q) :
    Preserved G H q (Access G) (Access H) :=
  (sameTriangle_preserved hq).compose hq (exit_preserved hq)

theorem underlyingEdge_preserved {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ} (hq : 3 ≤ q) :
    Preserved G H q (UnderlyingEdge G) (UnderlyingEdge H) :=
  (access_preserved hq).compose hq ((adjacency_preserved G H q).compose hq (access_preserved hq).flip)

end VariableWL.TypedGame

namespace VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable4} [Fintype V] (Y : PortGraph V) (color : V → ℕ)

omit [Fintype V] in
theorem sameTriangle_iff (x y : Vertex color) :
    TypedGame.SameTriangle (graph Y color) x y ↔ x.level=0 ∧ y.level=0 ∧ x.owner=y.owner := by
  constructor
  · rintro ⟨hx,hy,h⟩
    have hx0 := (triangle_characterization Y color x).mp hx
    have hy0 := (triangle_characterization Y color y).mp hy
    refine ⟨hx0,hy0,?_⟩
    rcases h with rfl | h
    · rfl
    · rcases h with h | h
      · exact h.1
      · have := h.1; omega
  · rintro ⟨hx,hy,ho⟩
    refine ⟨(triangle_characterization Y color x).mpr hx,(triangle_characterization Y color y).mpr hy,?_⟩
    by_cases hp : x.port=y.port
    · exact Or.inl (Vertex.ext ho hp (hx.trans hy.symm))
    · exact Or.inr (Or.inl ⟨ho,Or.inl ⟨hx,hy,hp⟩⟩)

omit [Fintype V] in
theorem exit_iff (x y : Vertex color) :
    TypedGame.Exit (graph Y color) x y ↔ x.level=0 ∧ y = Vertex.connector x.owner x.port := by
  constructor
  · rintro ⟨hx,hy,ha⟩
    have hx0 := (triangle_characterization Y color x).mp hx
    have hxe : x = Vertex.triangle x.owner x.port := Vertex.ext rfl rfl hx0
    rw [hxe] at ha
    refine ⟨hx0,?_⟩
    rcases (triangle_adj Y color _ _).mp ha with h | h
    · exact (hy ((triangle_characterization Y color y).mpr h.2.1)).elim
    · exact h
  · rintro ⟨hx,rfl⟩
    refine ⟨(triangle_characterization Y color x).mpr hx,?_,?_⟩
    · intro h
      have := (triangle_characterization Y color _).mp h
      change 1=0 at this
      omega
    · exact Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inl (by dsimp [Vertex.connector]; omega)⟩⟩

omit [Fintype V] in
theorem access_iff (x y : Vertex color) :
    TypedGame.Access (graph Y color) x y ↔ x.level=0 ∧ y.level=1 ∧ x.owner=y.owner := by
  constructor
  · rintro ⟨t,hxt,hty⟩
    obtain ⟨hx,_,ho⟩ := (sameTriangle_iff Y color x t).mp hxt
    obtain ⟨_,hy⟩ := (exit_iff Y color t y).mp hty
    exact ⟨hx,by rw [hy]; rfl,by rw [hy]; exact ho⟩
  · rintro ⟨hx,hy,ho⟩
    refine ⟨Vertex.triangle x.owner y.port,(sameTriangle_iff Y color _ _).mpr ⟨hx,rfl,rfl⟩,?_⟩
    exact (exit_iff Y color _ _).mpr ⟨rfl,Vertex.ext ho.symm rfl hy⟩

omit [Fintype V] in
theorem underlyingEdge_iff (x y : Vertex color) :
    TypedGame.UnderlyingEdge (graph Y color) x y ↔
      x.level=0 ∧ y.level=0 ∧ Y.graph.Adj x.owner y.owner := by
  constructor
  · rintro ⟨c,hxc,d,hcd,hyd⟩
    obtain ⟨hx,hc,hoc⟩ := (access_iff Y color x c).mp hxc
    obtain ⟨hy,hd,hod⟩ := (access_iff Y color y d).mp hyd
    refine ⟨hx,hy,?_⟩
    rcases hcd with h | h
    · rcases h.2 with h | h
      · omega
      · omega
    · exact ⟨c.port,d.port,by rw [hoc,hod]; exact h.2.2⟩
  · rintro ⟨hx,hy,j,k,he⟩
    exact ⟨Vertex.connector x.owner j,(access_iff Y color _ _).mpr ⟨hx,rfl,rfl⟩,
      Vertex.connector y.owner k,Or.inr ⟨rfl,rfl,he⟩,(access_iff Y color _ _).mpr ⟨hy,rfl,rfl⟩⟩

end VariableWL.SubcubicRealization

namespace VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable5} {W : Type uVariable6} [Fintype V] [Fintype W]
variable (Y : PortGraph V) (Z : PortGraph W) (color : V → ℕ) (color' : W → ℕ)

theorem winning_color {q : ℕ} (hq : 3 ≤ q)
    (hc : ∀ v, 0 < color v) (hc' : ∀ w, 0 < color' w)
    {p : TypedGame.Position (Vertex color) (Vertex color') q}
    (hp : TypedGame.Winning (graph Y color) (graph Z color') p)
    {i : Fin q} {x : Vertex color} {y : Vertex color'}
    (hi : p i = some (x,y)) (hx : x.level=0) :
    y.level=0 ∧ color x.owner=color' y.owner := by
  have ht := (colorTag_iff Y color hc (color x.owner) x).mpr ⟨hx,rfl⟩
  exact (colorTag_iff Z color' hc' _ y).mp (hp.colorTag_forward hq hi ht)

def SortWalk {A : Type uVariable7} (G : SimpleGraph A) (c : A → ℕ) : List ℕ → A → A → Prop
  | [], _, _ => False
  | [t], x, y => x=y ∧ c x=t
  | t::u::ts, x, y => c x=t ∧ ∃ z, G.Adj x z ∧ SortWalk G c (u::ts) z y

theorem winning_sortWalk {q : ℕ} (hq : 3 ≤ q)
    (hc : ∀ v, 0 < color v) (hc' : ∀ w, 0 < color' w)
    (ts : List ℕ) :
    TypedGame.Preserved (graph Y color) (graph Z color') q
      (fun x y => x.level=0 ∧ y.level=0 ∧ SortWalk Y.graph color ts x.owner y.owner)
      (fun x y => x.level=0 ∧ y.level=0 ∧ SortWalk Z.graph color' ts x.owner y.owner) := by
  induction ts using List.twoStepInduction with
  | nil => intro p hp i j x y x' y' hi hj h; exact h.2.2.elim
  | singleton t =>
    intro p hp i j x y x' y' hi hj h
    obtain ⟨hx',hcx⟩ := winning_color Y Z color color' hq hc hc' hp hi h.1
    obtain ⟨hy',_⟩ := winning_color Y Z color color' hq hc hc' hp hj h.2.1
    have hs := TypedGame.sameTriangle_preserved (G := graph Y color) (H := graph Z color') hq p hp hi hj
      ((sameTriangle_iff Y color x y).mpr ⟨h.1,h.2.1,h.2.2.1⟩)
    have ho := (sameTriangle_iff Z color' x' y').mp hs
    exact ⟨hx',hy',ho.2.2,hcx.symm.trans h.2.2.2⟩
  | cons_cons t u ts _ ih =>
    intro p hp i j x y x' y' hi hj h
    obtain ⟨hx',hcx⟩ := winning_color Y Z color color' hq hc hc' hp hi h.1
    obtain ⟨hy',_⟩ := winning_color Y Z color color' hq hc hc' hp hj h.2.1
    obtain ⟨hct,z,hxz,hzy⟩ := h.2.2
    let z0 : Vertex color := Vertex.triangle z 0
    have hm : TypedGame.Compose (TypedGame.UnderlyingEdge (graph Y color))
        (fun a b => a.level=0 ∧ b.level=0 ∧ SortWalk Y.graph color (u::ts) a.owner b.owner) x y :=
      ⟨z0,(underlyingEdge_iff Y color x z0).mpr ⟨h.1,rfl,hxz⟩,rfl,h.2.1,hzy⟩
    have hz := (TypedGame.underlyingEdge_preserved (G := graph Y color) (H := graph Z color') hq).compose
      hq (ih u) p hp hi hj hm
    obtain ⟨z',hxz',hz'⟩ := hz
    have ha := (underlyingEdge_iff Z color' x' z').mp hxz'
    exact ⟨hx',hy',hcx.symm.trans hct,z'.owner,ha.2.2,hz'.2.2⟩

end VariableWL.SubcubicRealization

end OAI
