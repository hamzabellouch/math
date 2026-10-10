import OAI.Combinatorics.VariableWL.PrefixParts

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.SubcubicRealization.PortGraph
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable1}

def ofSlots (G : SimpleGraph V) (slot : V → V → Fin 3)
    (hinj : ∀ x, Function.Injective (fun y : G.neighborSet x => slot x y.val)) : PortGraph V where
  edge a b := G.Adj a.1 b.1 ∧ a.2=slot a.1 b.1 ∧ b.2=slot b.1 a.1
  symm := fun h => ⟨h.1.symm,h.2.2,h.2.1⟩
  unique := by
    rintro ⟨x,i⟩ ⟨y,j⟩ ⟨z,k⟩ h h'
    have he : (⟨y,h.1⟩ : G.neighborSet x)=⟨z,h'.1⟩ := hinj x (h.2.1.symm.trans h'.2.1)
    have hy : y=z := congrArg Subtype.val he
    subst z
    exact Prod.ext rfl (h.2.2.trans h'.2.2.symm)
  different := fun h => h.1.ne

@[simp] theorem ofSlots_graph (G : SimpleGraph V) (slot : V → V → Fin 3)
    (hinj : ∀ x, Function.Injective (fun y : G.neighborSet x => slot x y.val)) :
    (ofSlots G slot hinj).graph=G := by
  ext x y
  exact ⟨fun ⟨_,_,h⟩ => h.1,fun h => ⟨slot x y,slot y x,h,rfl,rfl⟩⟩

def sigma {B : Type uVariable2} {A : B → Type uVariable9} (Y : ∀ b, PortGraph (A b)) : PortGraph (Σ b,A b) where
  edge a b := ∃ h : a.1.1=b.1.1, (Y a.1.1).edge (a.1.2,a.2) (h.symm ▸ b.1.2,b.2)
  symm := by
    rintro ⟨⟨b,x⟩,i⟩ ⟨⟨c,y⟩,j⟩ ⟨h,he⟩
    dsimp at h
    subst c
    exact ⟨rfl,(Y b).symm he⟩
  unique := by
    rintro ⟨⟨b,x⟩,i⟩ ⟨⟨c,y⟩,j⟩ ⟨⟨d,z⟩,k⟩ ⟨h,he⟩ ⟨h',he'⟩
    dsimp at h h'
    subst c
    subst d
    have hh := (Y b).unique he he'
    change (y,j)=(z,k) at hh
    cases hh
    rfl
  different := by
    rintro ⟨⟨b,x⟩,i⟩ ⟨⟨c,y⟩,j⟩ ⟨h,he⟩ hxy
    dsimp at h
    subst c
    exact (Y b).different he (eq_of_heq (Sigma.mk.inj_iff.mp hxy).2)

def union (Y Z : PortGraph V)
    (hd : ∀ a b c, Y.edge a b → Z.edge a c → False) : PortGraph V where
  edge a b := Y.edge a b ∨ Z.edge a b
  symm := fun h => h.elim (fun h => Or.inl (Y.symm h)) (fun h => Or.inr (Z.symm h))
  unique := by
    intro a b c h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · exact Y.unique h h'
    · exact (hd _ _ _ h h').elim
    · exact (hd _ _ _ h' h).elim
    · exact Z.unique h h'
  different := fun h => h.elim Y.different Z.different

end VariableWL.SubcubicRealization.PortGraph

namespace VariableWL.PrefixParts.Data
open VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable

noncomputable def ports (D : Data) (ε : Affine.Bit) : PortGraph (D.Vertex ε) :=
  PortGraph.ofSlots (D.graph ε) slot slot_injective

@[simp] theorem ports_graph (D : Data) (ε : Affine.Bit) : (D.ports ε).graph=D.graph ε :=
  PortGraph.ofSlots_graph _ _ _

end VariableWL.PrefixParts.Data

namespace VariableWL.PrefixParts
open VariableWL.Affine VariableWL.SubcubicRealization
open scoped CharTwo
attribute [local instance] Classical.propDecidable

abbrev Channel {B : Type uVariable3} (D : B → Data) := Σ b, {c : Fin (D b).channels // c.val≠0}

structure Wiring {B : Type uVariable4} (D : B → Data) where
  mate : Channel D ≃ Channel D
  involutive : Function.Involutive mate
  different : ∀ c, (mate c).1≠c.1
  root_eq : ∀ c, (D (mate c).1).root (mate c).2.val=(D c.1).root c.2.val

namespace Wiring
variable {B : Type uVariable5} [Fintype B] [FiniteNumbering B] (D : B → Data) (W : Wiring D)
abbrev Vertex (ε : Bit) := Σ b, (D b).Vertex ε

abbrev Root (ε : Bit) (c : Channel D) :=
  {t : (D c.1).Tree ε // t.channel=c.2.val ∧ t.height=(D c.1).root c.2.val}
abbrev RootLabel (ε : Bit) := Σ c : Channel D, Root D ε c

def rootVertex {ε : Bit} (x : RootLabel D ε) : Vertex D ε :=
  ⟨x.1.1,.inr (.inr x.2.val)⟩

omit [Fintype B] in
theorem rootVertex_injective {ε : Bit} : Function.Injective (rootVertex (D := D) (ε := ε)) := by
  rintro ⟨⟨b,c⟩,t⟩ ⟨⟨d,e⟩,u⟩ h
  have hb : b=d := congrArg Sigma.fst h
  subst d
  have ht : t.val=u.val := Sum.inr_injective (Sum.inr_injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2))
  have hc : c=e := Subtype.ext (t.property.1.symm.trans ((congrArg Data.Tree.channel ht).trans u.property.1))
  subst e
  have hu : t=u := Subtype.ext ht
  subst u
  rfl

def pad {a : ℕ} (v : Vec a) : ℕ → Bit := fun j => if h : j<a then v ⟨j,h⟩ else 0

theorem pad_injective {a : ℕ} : Function.Injective (@pad a) := by
  intro v w h
  ext i
  simpa only [pad,dite_eq_left i.isLt] using congrFun h i.val

@[simp] theorem pad_add {a : ℕ} (v w : Vec a) : pad (v+w)=pad v+pad w := by
  ext i
  simp only [pad,Pi.add_apply]
  split_ifs <;> simp

noncomputable def internal (ε : Bit) : PortGraph (Vertex D ε) :=
  PortGraph.sigma (fun b => (D b).ports ε)

def rootPorts (ε : Bit) : PortGraph (Vertex D ε) where
  edge a b := ∃ x y : RootLabel D ε, a=(rootVertex D x,0) ∧ b=(rootVertex D y,0) ∧
    W.mate x.1=y.1 ∧ pad x.2.val.bits=pad y.2.val.bits
  symm := by
    rintro a b ⟨x,y,rfl,rfl,hm,hv⟩
    refine ⟨y,x,rfl,rfl,?_,hv.symm⟩
    rw [← hm,W.involutive]
  unique := by
    rintro a b c ⟨x,y,rfl,rfl,hm,hv⟩ ⟨x',z,hx,rfl,hm',hv'⟩
    have hxx : x=x' := rootVertex_injective D (congrArg Prod.fst hx)
    subst x'
    have hc : y.1=z.1 := hm.symm.trans hm'
    have hyz : y=z := by
      rcases y with ⟨c,y⟩
      rcases z with ⟨d,z⟩
      dsimp at hc
      subst d
      have hb : y.val.bits=z.val.bits := pad_injective (hv.symm.trans hv')
      have ht : y.val=z.val := Data.Tree.ext (y.property.1.trans z.property.1.symm)
        (y.property.2.trans z.property.2.symm) hb
      exact congrArg (Sigma.mk c) (Subtype.ext ht)
    subst z
    rfl
  different := by
    rintro a b ⟨x,y,rfl,rfl,hm,_⟩ he
    have hblock : x.1.1=y.1.1 := congrArg (fun v : Vertex D ε => v.1) he
    exact W.different x.1 (by rw [hm]; exact hblock.symm)

omit [Fintype B] in

theorem internal_root_disjoint (ε : Bit) (a b c : Vertex D ε × Fin 3)
    (hi : (internal D ε).edge a b) (hr : (W.rootPorts D ε).edge a c) : False := by
  obtain ⟨x,y,rfl,rfl,_,_⟩ := hr
  rcases x with ⟨⟨d,e⟩,t⟩
  rcases b with ⟨⟨f,v⟩,j⟩
  obtain ⟨h,hint⟩ := hi
  dsimp [rootVertex] at h
  subst f
  have hh : ((D d).graph ε).Adj (.inr (.inr t.val)) v := hint.1
  have hs : Data.slot (.inr (.inr t.val)) v=0 := hint.2.1.symm
  exact Data.proper_root_reserved t.val
    (by rw [t.property.1]; exact e.property) (by rw [t.property.1]; exact t.property.2) hh hs

def anchor (ε : Bit) (b : B) : Vertex D ε := ⟨b,.inl ()⟩

def anchorPorts (ε : Bit) : PortGraph (Vertex D ε) where
  edge a b :=
    (∃ x y : B, a=(anchor D ε x,2) ∧ b=(anchor D ε y,1) ∧
      (enumeration B x).val+1=(enumeration B y).val) ∨
    (∃ x y : B, b=(anchor D ε x,2) ∧ a=(anchor D ε y,1) ∧
      (enumeration B x).val+1=(enumeration B y).val)
  symm := fun h => h.symm
  unique := by
    intro a b c h h'
    rcases h with ⟨x,y,rfl,rfl,hxy⟩ | ⟨x,y,rfl,rfl,hxy⟩
    · rcases h' with ⟨x',z,hx,rfl,hxz⟩ | ⟨z,x',rfl,hx,hzx⟩
      · have hxx : x=x' := congrArg (fun a => a.1.1) hx
        subst x'
        have hyz : y=z := (enumeration B).injective (Fin.ext (hxy.symm.trans hxz))
        subst z
        rfl
      · have hs : (2 : Fin 3)=1 := congrArg Prod.snd hx
        exact ((by decide : (2 : Fin 3)≠1) hs).elim
    · rcases h' with ⟨y',z,hy,rfl,hyz⟩ | ⟨z,y',rfl,hy,hzy⟩
      · have hs : (1 : Fin 3)=2 := congrArg Prod.snd hy
        exact ((by decide : (1 : Fin 3)≠2) hs).elim
      · have hyy : y=y' := congrArg (fun a => a.1.1) hy
        subst y'
        have hxz : x=z := (enumeration B).injective (Fin.ext (by omega))
        subst z
        rfl
  different := by
    intro a b he hab
    rcases he with ⟨x,y,rfl,rfl,hxy⟩ | ⟨x,y,rfl,rfl,hxy⟩
    · have h : x=y := congrArg Sigma.fst hab
      subst y
      omega
    · have h : y=x := congrArg Sigma.fst hab
      subst y
      omega

theorem internal_anchor_disjoint (ε : Bit) (a b c : Vertex D ε × Fin 3)
    (hi : (internal D ε).edge a b) (ha : (anchorPorts D ε).edge a c) : False := by
  rcases ha with ⟨x,y,rfl,rfl,_⟩ | ⟨y,x,rfl,rfl,_⟩
  all_goals
    rcases b with ⟨⟨d,v⟩,j⟩
    obtain ⟨h,hint⟩ := hi
    dsimp [anchor] at h
    subst d
    have hs := hint.2.1
    change (_ : Fin 3)=Data.slot (.inl ()) v at hs
    simp only [Data.slot] at hs
    omega

theorem root_anchor_disjoint (ε : Bit) (a b c : Vertex D ε × Fin 3)
    (hr : (W.rootPorts D ε).edge a b) (ha : (anchorPorts D ε).edge a c) : False := by
  obtain ⟨x,y,rfl,rfl,_,_⟩ := hr
  rcases ha with ⟨u,v,hu,_,_⟩ | ⟨u,v,_,hu,_⟩
  · have hs : (0 : Fin 3)=2 := congrArg Prod.snd hu
    exact (by decide : (0 : Fin 3)≠2) hs
  · have hs : (0 : Fin 3)=1 := congrArg Prod.snd hu
    exact (by decide : (0 : Fin 3)≠1) hs

noncomputable def ports (ε : Bit) : PortGraph (Vertex D ε) :=
  (internal D ε).union ((W.rootPorts D ε).union (anchorPorts D ε) (root_anchor_disjoint D W ε))
    (fun a b c hi he => he.elim (internal_root_disjoint D W ε a b c hi)
      (internal_anchor_disjoint D ε a b c hi))

end Wiring
end VariableWL.PrefixParts

namespace VariableWL.PrefixParts.Data
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {D : Data}

abbrev SortTag (D : Data) := Unit ⊕ (Fin D.channels ⊕ (Σ c : Fin D.channels,
  {h : Fin (D.dimension+1) // D.root c ≤ h.val}))

def sort {ε : Bit} : D.Vertex ε → D.SortTag
  | .inl _ => .inl ()
  | .inr (.inl (c,_)) => .inr (.inl c)
  | .inr (.inr t) => .inr (.inr ⟨t.channel,t.val.2.1,t.property.1⟩)

@[simp] theorem sort_translation (ξ : D.Valuation 1) (x : D.Vertex 0) :
    sort (D.vertexTranslation ξ x)=sort x := by
  rcases x with x | (x | x) <;> rfl

theorem ports_translation (ξ : D.Valuation 1) (x y : D.Vertex 0) (i j : Fin 3) :
    (D.ports 1).edge (D.vertexTranslation ξ x,localPorts ξ x i)
      (D.vertexTranslation ξ y,localPorts ξ y j) ↔ (D.ports 0).edge (x,i) (y,j) := by
  change ((D.graph 1).Adj (D.vertexTranslation ξ x) (D.vertexTranslation ξ y) ∧
    localPorts ξ x i=slot (D.vertexTranslation ξ x) (D.vertexTranslation ξ y) ∧
    localPorts ξ y j=slot (D.vertexTranslation ξ y) (D.vertexTranslation ξ x)) ↔
    ((D.graph 0).Adj x y ∧ i=slot x y ∧ j=slot y x)
  have hAdj : (D.graph 1).Adj (D.vertexTranslation ξ x) (D.vertexTranslation ξ y) ↔
      (D.graph 0).Adj x y := (D.translationIso ξ).map_adj_iff
  rw [hAdj]
  constructor
  · rintro ⟨h,hi,hj⟩
    rw [slot_translation ξ x y h] at hi
    rw [slot_translation ξ y x h.symm] at hj
    exact ⟨h,(localPorts ξ x).injective hi,(localPorts ξ y).injective hj⟩
  · rintro ⟨h,hi,hj⟩
    rw [slot_translation ξ x y h,slot_translation ξ y x h.symm]
    exact ⟨h,congrArg _ hi,congrArg _ hj⟩

@[simp] theorem localPorts_anchor (ξ : D.Valuation 1) (i : Fin 3) :
    localPorts ξ (.inl ()) i=i := rfl

end VariableWL.PrefixParts.Data

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable6} [Fintype B] (D : B → Data) (W : Wiring D)

abbrev SortTag := Σ b, (D b).SortTag
variable [FiniteNumbering B] [FiniteNumbering (SortTag D)]

def sort {ε : Bit} (x : Vertex D ε) : SortTag D := ⟨x.1,Data.sort x.2⟩

noncomputable def color {ε : Bit} (x : Vertex D ε) : ℕ :=
  (enumeration (SortTag D) (sort D x)).val+1

omit [FiniteNumbering B] in
theorem color_pos {ε : Bit} (x : Vertex D ε) : 0 < color D x := Nat.zero_lt_succ _

omit [FiniteNumbering B] in
theorem color_eq_iff {ε δ : Bit} (x : Vertex D ε) (y : Vertex D δ) :
    color D x=color D y ↔ sort D x=sort D y := by
  unfold color
  exact ⟨fun h => (enumeration (SortTag D)).injective (Fin.ext (by omega)),fun h => congrArg (fun t : SortTag D => (enumeration (SortTag D) t).val+1) h⟩

noncomputable def vertexTranslation (ξ : ∀ b, (D b).Valuation 1) : Vertex D 0 ≃ Vertex D 1 :=
  Equiv.sigmaCongrRight (fun b => (D b).vertexTranslation (ξ b))

omit [Fintype B] in
@[simp] theorem vertexTranslation_apply (ξ : ∀ b, (D b).Valuation 1) (b : B) (v : (D b).Vertex 0) :
    vertexTranslation D ξ ⟨b,v⟩=⟨b,(D b).vertexTranslation (ξ b) v⟩ := rfl

omit [FiniteNumbering B] in
@[simp] theorem color_translation (ξ : ∀ b, (D b).Valuation 1) (x : Vertex D 0) :
    color D (vertexTranslation D ξ x)=color D x := by
  apply (color_eq_iff D _ _).mpr
  exact congrArg (Sigma.mk x.1) (Data.sort_translation _ _)

noncomputable def localPorts (ξ : ∀ b, (D b).Valuation 1) (x : Vertex D 0) : Equiv.Perm (Fin 3) :=
  Data.localPorts (ξ x.1) x.2

noncomputable def incidenceTranslation (ξ : ∀ b, (D b).Valuation 1) :
    (Vertex D 0 × Fin 3) ≃ (Vertex D 1 × Fin 3) where
  toFun a := (vertexTranslation D ξ a.1,localPorts D ξ a.1 a.2)
  invFun a := ((vertexTranslation D ξ).symm a.1,
    (localPorts D ξ ((vertexTranslation D ξ).symm a.1)).symm a.2)
  left_inv a := by simp
  right_inv a := by simp

omit [Fintype B] in
@[simp] theorem root_truncated {ε : Bit} (x : RootLabel D ε) :
    Data.truncate ((D x.1.1).root x.1.2.val) x.2.val.bits=x.2.val.bits := by
  calc
    _ = Data.truncate x.2.val.height x.2.val.bits :=
      congrArg (fun h => Data.truncate h x.2.val.bits) x.2.property.2.symm
    _ = _ := x.2.val.truncated

noncomputable def rootTranslation (ξ : ∀ b, (D b).Valuation 1) : RootLabel D 0 ≃ RootLabel D 1 :=
  Equiv.sigmaCongrRight (fun c =>
    { toFun := fun t => ⟨(D c.1).treeTranslation (ξ c.1) t.val,t.property⟩
      invFun := fun t => ⟨((D c.1).treeTranslation (ξ c.1)).symm t.val,t.property⟩
      left_inv := fun t => Subtype.ext (((D c.1).treeTranslation (ξ c.1)).symm_apply_apply t.val)
      right_inv := fun t => Subtype.ext (((D c.1).treeTranslation (ξ c.1)).apply_symm_apply t.val) })

omit [Fintype B] in
@[simp] theorem translate_root_incidence (ξ : ∀ b, (D b).Valuation 1) (x : RootLabel D 0) :
    incidenceTranslation D ξ (rootVertex D x,0)=(rootVertex D (rootTranslation D ξ x),0) := by
  apply Prod.ext
  · rfl
  · exact Data.localPorts_zero _ _

noncomputable def rootShift (ξ : ∀ b, (D b).Valuation 1) (c : Channel D) : ℕ → Bit :=
  pad (Data.truncate ((D c.1).root c.2.val) ((ξ c.1).val ∘ (D c.1).order c.2.val))

def Compatible (ξ : ∀ b, (D b).Valuation 1) : Prop :=
  ∀ c, rootShift D ξ c=rootShift D ξ (W.mate c)

omit [Fintype B] in
@[simp] theorem rootTranslation_bits (ξ : ∀ b, (D b).Valuation 1) (x : RootLabel D 0) :
    pad (rootTranslation D ξ x).2.val.bits=pad x.2.val.bits+rootShift D ξ x.1 := by
  change pad (x.2.val.bits+Data.truncate x.2.val.height ((ξ x.1.1).val ∘ (D x.1.1).order x.2.val.channel))=_
  rw [pad_add,x.2.property.1,x.2.property.2]
  rfl

end VariableWL.PrefixParts.Wiring

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable7} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)] (W : Wiring D)

omit [Fintype B] in
theorem internal_translation (ξ : ∀ b, (D b).Valuation 1)
    (a b : Vertex D 0 × Fin 3) :
    (internal D 1).edge (incidenceTranslation D ξ a) (incidenceTranslation D ξ b) ↔
      (internal D 0).edge a b := by
  rcases a with ⟨⟨d,x⟩,i⟩
  rcases b with ⟨⟨e,y⟩,j⟩
  constructor
  · rintro ⟨h,he⟩
    change d=e at h
    subst e
    exact ⟨rfl,(Data.ports_translation (ξ d) x y i j).mp he⟩
  · rintro ⟨h,he⟩
    change d=e at h
    subst e
    exact ⟨rfl,(Data.ports_translation (ξ d) x y i j).mpr he⟩

def CompatiblePair (ξ : ∀ b, (D b).Valuation 1) (b c : B) : Prop :=
  ∀ d : Channel D, d.1=b → (W.mate d).1=c → rootShift D ξ d=rootShift D ξ (W.mate d)

omit [Fintype B] in
theorem compatiblePair_symm (ξ : ∀ b, (D b).Valuation 1) {b c : B}
    (h : CompatiblePair D W ξ b c) : CompatiblePair D W ξ c b := by
  intro d hd he
  have hh := h (W.mate d) he (by rw [W.involutive]; exact hd)
  rw [W.involutive d] at hh
  exact hh.symm

omit [Fintype B] in
theorem rootPorts_translation (ξ : ∀ b, (D b).Valuation 1)
    (a b : Vertex D 0 × Fin 3) (hξ : CompatiblePair D W ξ a.1.1 b.1.1) :
    (W.rootPorts D 1).edge (incidenceTranslation D ξ a) (incidenceTranslation D ξ b) ↔
      (W.rootPorts D 0).edge a b := by
  constructor
  · rintro ⟨x,y,ha,hb,hm,hv⟩
    let x₀ := (rootTranslation D ξ).symm x
    let y₀ := (rootTranslation D ξ).symm y
    have hx : rootTranslation D ξ x₀=x := (rootTranslation D ξ).apply_symm_apply x
    have hy : rootTranslation D ξ y₀=y := (rootTranslation D ξ).apply_symm_apply y
    have ha₀ : a=(rootVertex D x₀,0) := (incidenceTranslation D ξ).injective (by
      rw [translate_root_incidence,hx]; exact ha)
    have hb₀ : b=(rootVertex D y₀,0) := (incidenceTranslation D ξ).injective (by
      rw [translate_root_incidence,hy]; exact hb)
    have hm₀ : W.mate x₀.1=y₀.1 := hm
    have hs : rootShift D ξ x₀.1=rootShift D ξ y₀.1 := by
      rw [← hm₀]
      apply hξ
      · rw [ha₀]; rfl
      · rw [hb₀,hm₀]; rfl
    rw [← hx,← hy,rootTranslation_bits,rootTranslation_bits,hs] at hv
    exact ⟨x₀,y₀,ha₀,hb₀,hm₀,add_right_cancel hv⟩
  · rintro ⟨x,y,rfl,rfl,hm,hv⟩
    refine ⟨rootTranslation D ξ x,rootTranslation D ξ y,
      translate_root_incidence D ξ x,translate_root_incidence D ξ y,hm,?_⟩
    have hs : rootShift D ξ x.1=rootShift D ξ y.1 := by
      rw [← hm]
      exact hξ x.1 rfl (congrArg Sigma.fst hm)
    rw [rootTranslation_bits,rootTranslation_bits,hv,hs]

omit [Fintype B] in
@[simp] theorem translate_anchor_incidence (ξ : ∀ b, (D b).Valuation 1) (b : B) (i : Fin 3) :
    incidenceTranslation D ξ (anchor D 0 b,i)=(anchor D 1 b,i) := rfl

omit [FiniteNumbering (SortTag D)] in
theorem anchorPorts_translation (ξ : ∀ b, (D b).Valuation 1)
    (a b : Vertex D 0 × Fin 3) :
    (anchorPorts D 1).edge (incidenceTranslation D ξ a) (incidenceTranslation D ξ b) ↔
      (anchorPorts D 0).edge a b := by
  have hf : ∀ a b, (anchorPorts D 0).edge a b →
      (anchorPorts D 1).edge (incidenceTranslation D ξ a) (incidenceTranslation D ξ b) := by
    intro a b h
    rcases h with ⟨x,y,rfl,rfl,hxy⟩ | ⟨x,y,rfl,rfl,hxy⟩
    · exact Or.inl ⟨x,y,rfl,rfl,hxy⟩
    · exact Or.inr ⟨x,y,rfl,rfl,hxy⟩
  refine ⟨?_,hf a b⟩
  intro h
  have hi : ∀ v x i, incidenceTranslation D ξ v=(anchor D 1 x,i) → v=(anchor D 0 x,i) := by
    intro v x i hv
    exact (incidenceTranslation D ξ).injective hv
  rcases h with ⟨x,y,ha,hb,hxy⟩ | ⟨x,y,hb,ha,hxy⟩
  · exact Or.inl ⟨x,y,hi a x 2 ha,hi b y 1 hb,hxy⟩
  · exact Or.inr ⟨x,y,hi b x 2 hb,hi a y 1 ha,hxy⟩

omit [FiniteNumbering (SortTag D)] in

theorem ports_translation (ξ : ∀ b, (D b).Valuation 1)
    (a b : Vertex D 0 × Fin 3) (hξ : CompatiblePair D W ξ a.1.1 b.1.1) :
    (W.ports D 1).edge (incidenceTranslation D ξ a) (incidenceTranslation D ξ b) ↔
      (W.ports D 0).edge a b := by
  change (_ ∨ _ ∨ _) ↔ (_ ∨ _ ∨ _)
  rw [internal_translation D ξ a b,rootPorts_translation D W ξ a b hξ,
    anchorPorts_translation D ξ a b]

end VariableWL.PrefixParts.Wiring

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable8} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)] (W : Wiring D)

noncomputable def partHom (ε : Bit) (b : B) : (D b).graph ε →g (W.ports D ε).graph where
  toFun x := ⟨b,x⟩
  map_rel' {x y} h := ⟨Data.slot x y,Data.slot y x,Or.inl ⟨rfl,h,rfl,rfl⟩⟩

omit [FiniteNumbering (SortTag D)] in
theorem part_reachable (ε : Bit) (b : B) (x y : (D b).Vertex ε) :
    (W.ports D ε).graph.Reachable ⟨b,x⟩ ⟨b,y⟩ :=
  ((D b).connected ε x y).map (partHom D W ε b)

omit [FiniteNumbering (SortTag D)] in
theorem anchor_adj (ε : Bit) (b c : B)
    (h : (enumeration B b).val+1=(enumeration B c).val) :
    (W.ports D ε).graph.Adj (anchor D ε b) (anchor D ε c) :=
  ⟨2,1,Or.inr (Or.inr (Or.inl ⟨b,c,rfl,rfl,h⟩))⟩

omit [FiniteNumbering (SortTag D)] in

theorem connected [Nonempty B] (ε : Bit) : (W.ports D ε).graph.Connected := by
  have hn : 0 < Fintype.card B := Fintype.card_pos
  let b₀ : B := (enumeration B).symm ⟨0,hn⟩
  have hp : ∀ (j : ℕ) (hj : j<Fintype.card B),
      (W.ports D ε).graph.Reachable (anchor D ε ((enumeration B).symm ⟨j,hj⟩))
        (anchor D ε b₀) := by
    intro j
    induction j with
    | zero => intro hj; exact SimpleGraph.Reachable.refl _
    | succ j ih =>
        intro hj
        have hj' : j<Fintype.card B := by omega
        have hadj := anchor_adj D W ε ((enumeration B).symm ⟨j,hj'⟩)
          ((enumeration B).symm ⟨j+1,hj⟩) (by simp only [Equiv.apply_symm_apply])
        exact hadj.reachable.symm.trans (ih hj')
  have hv : ∀ x : Vertex D ε, (W.ports D ε).graph.Reachable x (anchor D ε b₀) := by
    rintro ⟨b,x⟩
    have hb := hp (enumeration B b).val (enumeration B b).isLt
    rw [Fin.eta,Equiv.symm_apply_apply] at hb
    exact (part_reachable D W ε b x (.inl ())).trans hb
  have : Nonempty (Vertex D ε) := ⟨anchor D ε b₀⟩
  exact ⟨fun x y => (hv x).trans (hv y).symm⟩

abbrev UncoloredVertex (ε : Bit) := SubcubicRealization.Vertex (@color B _ D _ ε)

noncomputable def uncolored (ε : Bit) : SimpleGraph (UncoloredVertex D ε) :=
  SubcubicRealization.graph (W.ports D ε) (color D)

theorem uncolored_connected [Nonempty B] (ε : Bit) : (uncolored D W ε).Connected :=
  SubcubicRealization.connected (W.ports D ε) (color D) (connected D W ε)

theorem uncolored_subcubic (ε : Bit) (x : UncoloredVertex D ε) :
    (uncolored D W ε).degree x ≤ 3 := SubcubicRealization.degree_le_three _ _ x

noncomputable def uncoloredTranslation (ξ : ∀ b, (D b).Valuation 1) :
    UncoloredVertex D 0 ≃ UncoloredVertex D 1 :=
  SubcubicRealization.vertexEquiv (vertexTranslation D ξ) (localPorts D ξ) (color_translation D ξ)

theorem uncoloredTranslation_adj (ξ : ∀ b, (D b).Valuation 1)
    (x y : UncoloredVertex D 0) (hξ : CompatiblePair D W ξ x.owner.1 y.owner.1) :
    (uncolored D W 1).Adj (uncoloredTranslation D ξ x) (uncoloredTranslation D ξ y) ↔
      (uncolored D W 0).Adj x y :=
  SubcubicRealization.vertexEquiv_adj (W.ports D 0) (W.ports D 1) _ _ _ x y
    (ports_translation D W ξ (x.owner,x.port) (y.owner,y.port) hξ).symm

omit [FiniteNumbering B] in
theorem equal_order : Fintype.card (UncoloredVertex D 0)=Fintype.card (UncoloredVertex D 1) := by
  let ξ : ∀ b, (D b).Valuation 1 := fun b => ⟨(D b).nonempty 1 |>.choose,(D b).nonempty 1 |>.choose_spec⟩
  exact Fintype.card_congr (uncoloredTranslation D ξ)

end VariableWL.PrefixParts.Wiring

end OAI
