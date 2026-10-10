import OAI.Combinatorics.VariableWL.BlockGame

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable

structure PortGraph (V : Type uVariable1) where
  edge : (V × Fin 3) → (V × Fin 3) → Prop
  symm : ∀ {a b}, edge a b → edge b a
  unique : ∀ {a b c}, edge a b → edge a c → b = c
  different : ∀ {a b}, edge a b → a.1 ≠ b.1

def PortGraph.graph {V : Type uVariable2} (Y : PortGraph V) : SimpleGraph V where
  Adj v w := ∃ j k, Y.edge (v,j) (w,k)
  symm := ⟨fun _ _ ⟨j,k,h⟩ => ⟨k,j,Y.symm h⟩⟩
  loopless := ⟨fun _ ⟨_,_,h⟩ => Y.different h rfl⟩

@[ext] structure Vertex {V : Type uVariable3} (color : V → ℕ) where
  owner : V
  port : Fin 3
  level : ℕ
  bound : level < color owner + 2

namespace Vertex
variable {V : Type uVariable4} {color : V → ℕ}

def triangle (v : V) (j : Fin 3) : Vertex color := ⟨v,j,0,by omega⟩
def connector (v : V) (j : Fin 3) : Vertex color := ⟨v,j,1,by omega⟩

def equivSigma : Vertex color ≃ (Σ v : V, Fin 3 × Fin (color v+2)) where
  toFun x := ⟨x.owner,x.port,⟨x.level,x.bound⟩⟩
  invFun x := ⟨x.1,x.2.1,x.2.2.val,x.2.2.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance [Fintype V] : Fintype (Vertex color) :=
  Fintype.ofEquiv _ equivSigma.symm

end Vertex

variable {V : Type uVariable5} (Y : PortGraph V) (color : V → ℕ)

def Internal (x y : Vertex color) : Prop :=
  x.owner = y.owner ∧
    ((x.level = 0 ∧ y.level = 0 ∧ x.port ≠ y.port) ∨
      (x.port = y.port ∧ (x.level+1 = y.level ∨ y.level+1 = x.level)))

def External (x y : Vertex color) : Prop :=
  x.level = 1 ∧ y.level = 1 ∧ Y.edge (x.owner,x.port) (y.owner,y.port)

def graph : SimpleGraph (Vertex color) where
  Adj x y := Internal color x y ∨ External Y color x y
  symm := ⟨by
    intro x y h
    rcases h with ⟨ho,(⟨hx,hy,hp⟩ | ⟨hp,hl⟩)⟩ | ⟨hx,hy,he⟩
    · exact Or.inl ⟨ho.symm,Or.inl ⟨hy,hx,hp.symm⟩⟩
    · exact Or.inl ⟨ho.symm,Or.inr ⟨hp.symm,hl.symm⟩⟩
    · exact Or.inr ⟨hy,hx,Y.symm he⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨_,(⟨_,_,hp⟩ | ⟨_,hl⟩)⟩ | ⟨_,_,he⟩
    · exact hp rfl
    · omega
    · exact Y.different he rfl⟩

theorem adjacency_owner {x y : Vertex color} (h : (graph Y color).Adj x y) :
    x.owner = y.owner ∨ Y.graph.Adj x.owner y.owner := by
  rcases h with h | h
  · exact Or.inl h.1
  · exact Or.inr ⟨x.port,y.port,h.2.2⟩

theorem triangle_adj_triangle (v w : V) (j k : Fin 3) :
    (graph Y color).Adj (Vertex.triangle v j) (Vertex.triangle w k) ↔ v = w ∧ j ≠ k := by
  simp [graph,Internal,External,Vertex.triangle]

theorem triangle_adj {x : Vertex color} (v : V) (j : Fin 3) :
    (graph Y color).Adj (Vertex.triangle v j) x ↔
      (x.owner = v ∧ x.level = 0 ∧ x.port ≠ j) ∨ x = Vertex.connector v j := by
  constructor
  · intro h
    rcases h with ⟨ho,(⟨_,hx,hp⟩ | ⟨hp,hl⟩)⟩ | ⟨hx,_,_⟩
    · exact Or.inl ⟨ho.symm,hx,hp.symm⟩
    · right
      apply Vertex.ext (x := x) (y := Vertex.connector v j) ho.symm hp.symm
      have : x.level = 1 := by change 0+1=x.level ∨ x.level+1=0 at hl; omega
      exact this
    · change (0 : ℕ) = 1 at hx
      omega
  · rintro (⟨ho,hx,hp⟩ | rfl)
    · exact Or.inl ⟨ho.symm,Or.inl ⟨rfl,hx,hp.symm⟩⟩
    · exact Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inl rfl⟩⟩

theorem triangle_characterization (x : Vertex color) :
    (∃ y z, (graph Y color).Adj x y ∧ (graph Y color).Adj y z ∧ (graph Y color).Adj z x) ↔
      x.level = 0 := by
  constructor
  · rintro ⟨y,z,hxy,hyz,hzx⟩
    by_contra hx
    have hxz := (graph Y color).symm.symm _ _ hzx
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · obtain ⟨hoy,hpy,hly⟩ : x.owner=y.owner ∧ x.port=y.port ∧
          (x.level+1=y.level ∨ y.level+1=x.level) := by
        rcases hxy with ⟨ho,h | h⟩
        · exact (hx h.1).elim
        · exact ⟨ho,h⟩
      obtain ⟨hoz,hpz,hlz⟩ : x.owner=z.owner ∧ x.port=z.port ∧
          (x.level+1=z.level ∨ z.level+1=x.level) := by
        rcases hxz with ⟨ho,h | h⟩
        · exact (hx h.1).elim
        · exact ⟨ho,h⟩
      rcases hyz with ⟨_,h | h⟩ | h
      · exact h.2.2 (hpy.symm.trans hpz)
      · omega
      · exact Y.different h.2.2 (hoy.symm.trans hoz)
    · have ho : x.owner ≠ z.owner := Y.different hxz.2.2
      have hy : y.owner = x.owner := hxy.1.symm
      rcases hyz with hyz | hyz
      · exact ho (hy.symm.trans hyz.1)
      · have hx1 : x.level = 1 := hxz.1
        have hlev : y.level = 1 := hyz.1
        rcases hxy.2 with h | h
        · omega
        · omega
    · have ho : x.owner ≠ y.owner := Y.different hxy.2.2
      have hz : z.owner = x.owner := hxz.1.symm
      rcases hyz with hyz | hyz
      · exact ho (hz.symm.trans hyz.1.symm)
      · have hx1 : x.level = 1 := hxy.1
        have hlev : z.level = 1 := hyz.2.1
        rcases hxz.2 with h | h
        · omega
        · omega
    · have he := Y.unique hxy.2.2 hxz.2.2
      have hyz' : y = z := Vertex.ext (congrArg Prod.fst he) (congrArg Prod.snd he)
        (hxy.2.1.trans hxz.2.1.symm)
      subst z
      exact (graph Y color).loopless.irrefl _ hyz
  · intro hx
    have hj : ∃ j k : Fin 3, j ≠ x.port ∧ k ≠ x.port ∧ j ≠ k := by
      generalize x.port = p
      fin_cases p <;> decide
    obtain ⟨j,k,hj,hk,hjk⟩ := hj
    refine ⟨Vertex.triangle x.owner j,Vertex.triangle x.owner k,?_,?_,?_⟩
    · exact Or.inl ⟨rfl,Or.inl ⟨hx,rfl,hj.symm⟩⟩
    · exact (triangle_adj_triangle Y color _ _ _ _).mpr ⟨rfl,hjk⟩
    · exact Or.inl ⟨rfl,Or.inl ⟨rfl,hx,hk⟩⟩

end VariableWL.SubcubicRealization

namespace VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable6} (Y : PortGraph V) (color : V → ℕ)

noncomputable def neighborSlot (x y : Vertex color) : Fin 3 := by
  classical
  exact if x.level = 0 then (if y.level = 0 then y.port else x.port)
    else if y.owner = x.owner then (if y.level < x.level then 0 else 1) else 2

theorem internal_of_nontriangle {x y : Vertex color} (hx : x.level ≠ 0)
    (h : Internal color x y) : x.owner=y.owner ∧ x.port=y.port ∧
      (x.level+1=y.level ∨ y.level+1=x.level) := by
  rcases h with ⟨ho,h | h⟩
  · exact (hx h.1).elim
  · exact ⟨ho,h⟩

theorem neighborSlot_injective (x : Vertex color) :
    Function.Injective (fun y : (graph Y color).neighborSet x => neighborSlot color x y.val) := by
  classical
  rintro ⟨y,hy⟩ ⟨z,hz⟩ he
  apply Subtype.ext
  have hy' : (graph Y color).Adj x y := hy
  have hz' : (graph Y color).Adj x z := hz
  by_cases hx : x.level = 0
  · have hxt : x = Vertex.triangle x.owner x.port := Vertex.ext rfl rfl hx
    rw [hxt,triangle_adj] at hy' hz'
    rcases hy' with ⟨hoy,hly,hpy⟩ | rfl <;> rcases hz' with ⟨hoz,hlz,hpz⟩ | rfl
    · apply Vertex.ext (hoy.trans hoz.symm) _ (hly.trans hlz.symm)
      simpa only [neighborSlot,ite_eq_left hx,ite_eq_left hly,ite_eq_left hlz] using he
    · have he' : y.port = x.port := by simpa [neighborSlot,hx,hly,Vertex.connector] using he
      exact (hpy he').elim
    · have he' : z.port = x.port := by simpa [neighborSlot,hx,hlz,Vertex.connector] using he.symm
      exact (hpz he').elim
    · rfl
  · rcases hy' with hy' | hy' <;> rcases hz' with hz' | hz'
    · obtain ⟨hoy,hpy,hly⟩ := internal_of_nontriangle color hx hy'
      obtain ⟨hoz,hpz,hlz⟩ := internal_of_nontriangle color hx hz'
      apply Vertex.ext (hoy.symm.trans hoz) (hpy.symm.trans hpz)
      simp only [neighborSlot,ite_eq_right hx,ite_eq_left hoy.symm,ite_eq_left hoz.symm] at he
      split_ifs at he <;> try {have := congrArg Fin.val he; norm_num at this}
      all_goals omega
    · obtain ⟨hoy,_,hly⟩ := internal_of_nontriangle color hx hy'
      have hoz := (Y.different hz'.2.2).symm
      simp only [neighborSlot,ite_eq_right hx,ite_eq_left hoy.symm,ite_eq_right hoz] at he
      split_ifs at he <;> cases (by simpa using congrArg Fin.val he : False)
    · obtain ⟨hoz,_,hlz⟩ := internal_of_nontriangle color hx hz'
      have hoy := (Y.different hy'.2.2).symm
      simp only [neighborSlot,ite_eq_right hx,ite_eq_right hoy,ite_eq_left hoz.symm] at he
      split_ifs at he <;> cases (by simpa using congrArg Fin.val he : False)
    · have hpair := Y.unique hy'.2.2 hz'.2.2
      exact Vertex.ext (congrArg Prod.fst hpair) (congrArg Prod.snd hpair)
        (hy'.2.1.trans hz'.2.1.symm)

theorem degree_le_three [Fintype V] (x : Vertex color) : (graph Y color).degree x ≤ 3 := by
  classical
  have hc := Fintype.card_le_of_injective _ (neighborSlot_injective Y color x)
  simpa only [SimpleGraph.card_neighborSet_eq_degree,Fintype.card_fin] using hc

theorem triangle_degree [Fintype V] (v : V) (j : Fin 3) :
    (graph Y color).degree (Vertex.triangle v j) = 3 := by
  classical
  apply Nat.le_antisymm (degree_le_three Y color _)
  let f : Fin 3 → (graph Y color).neighborSet (Vertex.triangle v j) := fun k =>
    if h : k = j then ⟨Vertex.connector v j,(triangle_adj Y color v j).mpr (Or.inr rfl)⟩
    else ⟨Vertex.triangle v k,(triangle_adj_triangle Y color v v j k).mpr ⟨rfl,Ne.symm h⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h := congrArg Subtype.val hab
    by_cases ha : a=j <;> by_cases hb : b=j
    · exact ha.trans hb.symm
    · simp only [f,dite_eq_left ha,dite_eq_right hb] at h
      have := congrArg Vertex.level h
      simp [Vertex.connector,Vertex.triangle] at this
    · simp only [f,dite_eq_right ha,dite_eq_left hb] at h
      have := congrArg Vertex.level h
      simp [Vertex.connector,Vertex.triangle] at this
    · simp only [f,dite_eq_right ha,dite_eq_right hb] at h
      exact congrArg Vertex.port h
  have hc := Fintype.card_le_of_injective f hf
  simpa only [SimpleGraph.card_neighborSet_eq_degree,Fintype.card_fin] using hc

end VariableWL.SubcubicRealization

namespace VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable7} (Y : PortGraph V) (color : V → ℕ)

theorem high_adj {x y : Vertex color} (hx : 2 ≤ x.level) :
    (graph Y color).Adj x y ↔ x.owner=y.owner ∧ x.port=y.port ∧
      (x.level+1=y.level ∨ y.level+1=x.level) := by
  constructor
  · rintro (h | h)
    · exact internal_of_nontriangle color (by omega) h
    · have := h.1; omega
  · rintro ⟨ho,hp,hl⟩
    exact Or.inl ⟨ho,Or.inr ⟨hp,hl⟩⟩

theorem high_degree_le_two [Fintype V] (x : Vertex color) (hx : 2 ≤ x.level) :
    (graph Y color).degree x ≤ 2 := by
  classical
  let f : (graph Y color).neighborSet x → Fin 2 :=
    fun y => if y.val.level < x.level then 0 else 1
  have hf : Function.Injective f := by
    rintro ⟨y,hy⟩ ⟨z,hz⟩ he
    obtain ⟨hoy,hpy,hly⟩ := (high_adj Y color hx).mp hy
    obtain ⟨hoz,hpz,hlz⟩ := (high_adj Y color hx).mp hz
    apply Subtype.ext
    apply Vertex.ext (hoy.symm.trans hoz) (hpy.symm.trans hpz)
    dsimp [f] at he
    split_ifs at he <;> try {have := congrArg Fin.val he; norm_num at this}
    all_goals omega
  simpa only [Fintype.card_fin,SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective f hf

theorem terminal_degree [Fintype V] (hcolor : ∀ v, 0 < color v) (x : Vertex color)
    (hx : x.level = color x.owner+1) : (graph Y color).degree x = 1 := by
  classical
  have hl : 2 ≤ x.level := by have := hcolor x.owner; omega
  let y : Vertex color := ⟨x.owner,x.port,x.level-1,by have := x.bound; omega⟩
  apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
  refine ⟨y,?_,?_⟩
  · exact (high_adj Y color hl).mpr ⟨rfl,rfl,Or.inr (by dsimp [y]; omega)⟩
  · intro z hz
    obtain ⟨ho,hp,hh⟩ := (high_adj Y color hl).mp hz
    apply Vertex.ext (x := z) (y := y) ho.symm hp.symm
    have hb := z.bound
    rw [← ho] at hb
    dsimp only [y]
    omega

theorem intermediate_degree [Fintype V] (x : Vertex color)
    (hx : 2 ≤ x.level) (hb : x.level < color x.owner+1) : (graph Y color).degree x = 2 := by
  classical
  apply Nat.le_antisymm (high_degree_le_two Y color x hx)
  let lo : Vertex color := ⟨x.owner,x.port,x.level-1,by have := x.bound; omega⟩
  let hi : Vertex color := ⟨x.owner,x.port,x.level+1,by omega⟩
  let f : Fin 2 → (graph Y color).neighborSet x := fun i =>
    if i = 0 then ⟨lo,(high_adj Y color hx).mpr ⟨rfl,rfl,Or.inr (by dsimp [lo]; omega)⟩⟩
    else ⟨hi,(high_adj Y color hx).mpr ⟨rfl,rfl,Or.inl rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j he
    have h := congrArg (fun z => z.val.level) he
    fin_cases i <;> fin_cases j <;> simp [f,lo,hi] at h ⊢
    omega
  simpa only [Fintype.card_fin,SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective f hf

theorem connector_used_degree [Fintype V] (hcolor : ∀ v, 0 < color v)
    {v w : V} {j k : Fin 3} (he : Y.edge (v,j) (w,k)) :
    (graph Y color).degree (Vertex.connector v j) = 3 := by
  classical
  apply Nat.le_antisymm (degree_le_three Y color _)
  let first : Vertex color := ⟨v,j,2,by have := hcolor v; omega⟩
  let f : Fin 3 → (graph Y color).neighborSet (Vertex.connector v j) := fun i =>
    if i = 0 then ⟨Vertex.triangle v j,Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inr rfl⟩⟩⟩
    else if i = 1 then ⟨first,Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inl rfl⟩⟩⟩
    else ⟨Vertex.connector w k,Or.inr ⟨rfl,rfl,he⟩⟩
  have hf : Function.LeftInverse (fun z => neighborSlot color (Vertex.connector v j) z.val) f := by
    intro i
    have hw : w ≠ v := (Y.different he).symm
    fin_cases i <;> simp [f,neighborSlot,Vertex.connector,Vertex.triangle,first,hw]
  simpa only [Fintype.card_fin,SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective f hf.injective

theorem same_owner_reachable (x y : Vertex color) (ho : x.owner = y.owner) :
    (graph Y color).Reachable x y := by
  have hbase (z : Vertex color) : (graph Y color).Reachable z (Vertex.triangle z.owner z.port) := by
    induction he : z.level using Nat.strong_induction_on generalizing z with
    | h l ih =>
      by_cases hl : l = 0
      · have hz : z = Vertex.triangle z.owner z.port := Vertex.ext rfl rfl (he.trans hl)
        exact (congrArg ((graph Y color).Reachable z) hz).mp (.refl z)
      · let prev : Vertex color := ⟨z.owner,z.port,l-1,by have := z.bound; omega⟩
        have ha : (graph Y color).Adj z prev := Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inr (by dsimp [prev]; omega)⟩⟩
        exact ha.reachable.trans (ih (l-1) (by omega) prev rfl)
  have htri : (graph Y color).Reachable (Vertex.triangle x.owner x.port) (Vertex.triangle y.owner y.port) := by
    by_cases hp : x.port = y.port
    · have he : Vertex.triangle (color := color) x.owner x.port = Vertex.triangle y.owner y.port := by rw [ho,hp]
      rw [he]
    · exact ((triangle_adj_triangle Y color _ _ _ _).mpr ⟨ho,hp⟩).reachable
  exact (hbase x).trans (htri.trans (hbase y).symm)

theorem underlying_edge_reachable {v w : V} (h : Y.graph.Adj v w) (j k : Fin 3) :
    (graph Y color).Reachable (Vertex.triangle v j) (Vertex.triangle w k) := by
  obtain ⟨a,b,he⟩ := h
  have hc : (graph Y color).Adj (Vertex.connector v a) (Vertex.connector w b) := Or.inr ⟨rfl,rfl,he⟩
  exact (same_owner_reachable Y color (Vertex.triangle v j) (Vertex.connector v a) rfl).trans
    (hc.reachable.trans (same_owner_reachable Y color (Vertex.connector w b) (Vertex.triangle w k) rfl))

theorem connected (hY : Y.graph.Connected) : (graph Y color).Connected := by
  have : Nonempty V := hY.nonempty
  have : Nonempty (Vertex color) := ⟨Vertex.triangle (Classical.choice ‹Nonempty V›) 0⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨p⟩ := hY x.owner y.owner
  have walk_lift {v w : V} (q : Y.graph.Walk v w) :
      (graph Y color).Reachable (Vertex.triangle v 0) (Vertex.triangle w 0) := by
    induction q with
    | nil => exact .refl _
    | cons ha q ih => exact (underlying_edge_reachable Y color ha 0 0).trans ih
  exact (same_owner_reachable Y color x (Vertex.triangle x.owner 0) rfl).trans
    ((walk_lift p).trans (same_owner_reachable Y color (Vertex.triangle y.owner 0) y rfl))

end VariableWL.SubcubicRealization

namespace VariableWL.SubcubicRealization
variable {V : Type uVariable8} {W : Type uVariable9} {color : V → ℕ} {color' : W → ℕ}

def vertexEquiv (f : V ≃ W) (ports : V → Equiv.Perm (Fin 3))
    (hc : ∀ v, color' (f v) = color v) : Vertex color ≃ Vertex color' where
  toFun x := ⟨f x.owner,ports x.owner x.port,x.level,by rw [hc]; exact x.bound⟩
  invFun y := ⟨f.symm y.owner,(ports (f.symm y.owner)).symm y.port,y.level,by
    rw [← hc,f.apply_symm_apply]; exact y.bound⟩
  left_inv x := by apply Vertex.ext <;> simp
  right_inv y := by apply Vertex.ext <;> simp

theorem vertexEquiv_internal (f : V ≃ W) (ports : V → Equiv.Perm (Fin 3))
    (hc : ∀ v, color' (f v) = color v) (x y : Vertex color) :
    Internal color' (vertexEquiv f ports hc x) (vertexEquiv f ports hc y) ↔ Internal color x y := by
  change (f x.owner = f y.owner ∧ _) ↔ _
  rw [f.injective.eq_iff]
  by_cases ho : x.owner = y.owner
  · simp only [Internal,vertexEquiv,Equiv.coe_fn_mk,ho,true_and]
    simp only [ne_eq,(ports y.owner).injective.eq_iff]
  · simp only [ho,false_and,Internal]

theorem vertexEquiv_adj (Y : PortGraph V) (Z : PortGraph W)
    (f : V ≃ W) (ports : V → Equiv.Perm (Fin 3))
    (hc : ∀ v, color' (f v) = color v) (x y : Vertex color)
    (he : Y.edge (x.owner,x.port) (y.owner,y.port) ↔
      Z.edge (f x.owner,ports x.owner x.port) (f y.owner,ports y.owner y.port)) :
    (graph Z color').Adj (vertexEquiv f ports hc x) (vertexEquiv f ports hc y) ↔
      (graph Y color).Adj x y := by
  change (Internal color' _ _ ∨ _) ↔ (Internal color x y ∨ _)
  rw [vertexEquiv_internal]
  change (Internal color x y ∨ x.level=1 ∧ y.level=1 ∧
    Z.edge (f x.owner,ports x.owner x.port) (f y.owner,ports y.owner y.port)) ↔ _
  rw [← he]
  rfl

end VariableWL.SubcubicRealization

end OAI
