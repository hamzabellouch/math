import OAI.Computability.WeisfeilerLeman.Writer

namespace OAI

universe uV uW uT uS uJ uR uJ'

namespace WLTime.Enumeration
variable {V : Type uV} {W : Type uW}
structure Listing (V : Type uV) where
  items : List V
  nodup : items.Nodup
  complete : ∀v,v∈items

noncomputable def Listing.equiv (l : Listing V) : Fin l.items.length ≃ V :=
  Equiv.ofBijective l.items.get ⟨List.nodup_iff_injective_get.mp l.nodup,
    fun v => List.mem_iff_get.mp (l.complete v)⟩
@[simp] theorem Listing.equiv_apply (l : Listing V) (i : Fin l.items.length) : l.equiv i=l.items.get i := rfl

noncomputable def ofFintype (V : Type uV) [Fintype V] : Listing V := by
  classical
  exact ⟨Finset.univ.toList,Finset.nodup_toList _,fun v => by simp⟩

def fin (n : ℕ) : Listing (Fin n) := ⟨List.finRange n,List.nodup_finRange n,List.mem_finRange⟩

def Listing.prod (l : Listing V) (k : Listing W) : Listing (V × W) where
  items := l.items.flatMap (fun v => k.items.map (fun w => (v,w)))
  nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun v _ => (List.nodup_map_iff (fun x y h => (Prod.mk.inj h).2)).mpr k.nodup,?_⟩
    apply l.nodup.imp
    intro x y hxy
    apply List.disjoint_left.mpr
    intro a ha hb
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨v,_,he⟩ := List.mem_map.mp hb
    exact hxy (Prod.mk.inj he).1.symm
  complete := by
    rintro ⟨v,w⟩
    exact List.mem_flatMap.mpr ⟨v,l.complete v,List.mem_map.mpr ⟨w,k.complete w,rfl⟩⟩

def Listing.sum (l : Listing V) (k : Listing W) : Listing (V ⊕ W) where
  items := l.items.map Sum.inl ++ k.items.map Sum.inr
  nodup := by
    apply List.nodup_append.mpr
    refine ⟨(List.nodup_map_iff Sum.inl_injective).mpr l.nodup,
      (List.nodup_map_iff Sum.inr_injective).mpr k.nodup,?_⟩
    intro a ha b hb
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
    exact Sum.inl_ne_inr
  complete := by
    intro v; cases v with
    | inl v => exact List.mem_append_left _ (List.mem_map.mpr ⟨v,l.complete v,rfl⟩)
    | inr w => exact List.mem_append_right _ (List.mem_map.mpr ⟨w,k.complete w,rfl⟩)

def Listing.option (l : Listing V) : Listing (Option V) where
  items := none::l.items.map some
  nodup := by
    rw [List.nodup_cons]
    exact ⟨by simp,(List.nodup_map_iff (Option.some_injective V)).mpr l.nodup⟩
  complete := by
    intro v; cases v with
    | none => exact List.mem_cons_self
    | some v => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨v,l.complete v,rfl⟩)

 theorem fin_values (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj; simp

 theorem range_flatMap {T : Type uT} (n : ℕ) (f : ℕ → List T) :
    (List.range n).flatMap f=(List.finRange n).flatMap (fun i => f i.val) := by
  rw [← fin_values,List.flatMap_map]

 theorem Listing.length_eq_card [Fintype V] (l : Listing V) : l.items.length=Fintype.card V := by
  rw [← Fintype.card_fin l.items.length]
  exact Fintype.card_congr l.equiv
end WLTime.Enumeration

namespace WLTime.Enumeration
open NatCode
variable {T : Type uT} {S : Type uS} {J : Type uJ}
abbrev Vertex (T : Type uT) (S : Type uS) (m L p : ℕ) := Option ((((T × S × Fin m × Fin m) × Fin L)) ⊕ Fin p)

def rectangle (t : Listing T) (s : Listing S) (m L p : ℕ) : Listing (Vertex T S m L p) :=
  ((t.prod (s.prod ((fin m).prod (fin m)))).prod (fin L) |>.sum (fin p)).option

 theorem rectangle_flatMap {R : Type uR} (t : Listing T) (s : Listing S) (m L p : ℕ)
    (f : Vertex T S m L p → List R) :
    (rectangle t s m L p).items.flatMap f=f none ++
      t.items.flatMap (fun t => s.items.flatMap (fun s => (List.finRange m).flatMap (fun a =>
        (List.finRange m).flatMap (fun b => (List.finRange L).flatMap (fun i => f (some (.inl ((t,s,a,b),i)))))))) ++
      (List.finRange p).flatMap (fun i => f (some (.inr i))) := by
  simp only [rectangle,Listing.option,Listing.sum,Listing.prod,fin,List.flatMap_cons,
    List.flatMap_append,List.flatMap_map,List.flatMap_assoc,List.append_assoc]

def writer (t : Listing T) (s : Listing S) (N L P : Expr J)
    (hub : Writer J) (slot : T → S → Writer (Option (Option (Option J))))
    (pad : Writer (Option J)) : Writer J :=
  .seq hub (.seq (Writer.each t.items (fun t => Writer.each s.items (fun s => Writer.grid N L (slot t s))))
    (.loop P pad))

 theorem writer_eval (t : Listing T) (s : Listing S) (N L P : Expr J)
    (hub : Writer J) (slot : T → S → Writer (Option (Option (Option J)))) (pad : Writer (Option J))
    (σ : J → ℕ) (w : List Bool) (m a p : ℕ)
    (hN : N.eval σ w=m) (hL : L.eval σ w=a) (hP : P.eval σ w=p)
    (f : Vertex T S m a p → List Bool)
    (hh : hub.eval σ w=f none)
    (hs : ∀t s (x y : Fin m) (i : Fin a),
      (slot t s).eval (Option.elim' i.val (Option.elim' y.val (Option.elim' x.val σ))) w=
        f (some (.inl ((t,s,x,y),i))))
    (hp : ∀i : Fin p,pad.eval (Option.elim' i.val σ) w=f (some (.inr i))) :
    (writer t s N L P hub slot pad).eval σ w=(rectangle t s m a p).items.flatMap f := by
  rw [rectangle_flatMap]
  simp only [writer,Writer.eval,Writer.each_eval,Writer.grid_eval,hN,hL,hP,hh,
    ← List.append_assoc,range_flatMap]
  simp only [hs,hp]

 theorem writer_safe (t : Listing T) (s : Listing S) (N L P : Expr J)
    (hub : Writer J) (slot : T → S → Writer (Option (Option (Option J)))) (pad : Writer (Option J))
    (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (hN : N.Bounded σ w B) (hL : L.Bounded σ w B) (hP : P.Bounded σ w B)
    (hh : hub.Safe σ w B)
    (hs : ∀t s x,x < N.eval σ w → ∀y,y<N.eval σ w → ∀i,i<L.eval σ w →
      (slot t s).Safe (Option.elim' i (Option.elim' y (Option.elim' x σ))) w B)
    (hp : ∀i<P.eval σ w,pad.Safe (Option.elim' i σ) w B) :
    (writer t s N L P hub slot pad).Safe σ w B := by
  refine ⟨hh,⟨Writer.each_safe _ _ σ w B ?_,⟨hP,hp⟩⟩⟩
  intro tag htag
  apply Writer.each_safe
  intro value hvalue
  exact Writer.grid_safe N L (slot tag value) σ w B hN hL (hs tag value)

 theorem writer_depth (t : Listing T) (s : Listing S) (N L P : Expr J)
    (hub : Writer J) (slot : T → S → Writer (Option (Option (Option J)))) (pad : Writer (Option J))
    (b : ℕ) (hh : hub.depth≤b+3) (hs : ∀t s,(slot t s).depth≤b) (hp : pad.depth≤b+2) :
    (writer t s N L P hub slot pad).depth≤b+3 := by
  apply max_le hh
  apply max_le
  · apply Writer.each_depth_le _ _ _ (by omega)
    intro tag htag
    apply Writer.each_depth_le _ _ _ (by omega)
    intro value hvalue
    rw [Writer.grid_depth]
    exact Nat.add_le_add_right (hs tag value) 3
  · exact Nat.add_le_add_right hp 1
end WLTime.Enumeration

namespace WLTime.Enumeration
variable {V : Type uV}
open scoped Classical
noncomputable def Listing.matrix (l : Listing V) (G : SimpleGraph V) : Graph l.items.length :=
  Graph.ofSimple G l.equiv.symm

 theorem Listing.ofFn_eq_map {R : Type uR} (l : Listing V) (f : V → R) :
    List.ofFn (fun i => f (l.items.get i))=l.items.map f := by
  change List.ofFn (f ∘ l.items.get)=_
  rw [←List.map_ofFn,List.ofFn_get]

 theorem Listing.matrix_bits (l : Listing V) (G : SimpleGraph V) :
    matrixBits (l.matrix G)=l.items.flatMap (fun x => l.items.map (fun y => decide (G.Adj x y))) := by
  classical
  have hx : matrixBits (l.matrix G)=
      (List.ofFn fun i => List.ofFn fun j => decide (G.Adj (l.items.get i) (l.items.get j))).flatten := by
    rfl
  rw [hx]
  have hr (v : V) := l.ofFn_eq_map (fun y => decide (G.Adj v y))
  have ho := l.ofFn_eq_map (fun x => l.items.map (fun y => decide (G.Adj x y)))
  calc
    _ = (List.ofFn fun i => l.items.map (fun y => decide (G.Adj (l.items.get i) y))).flatten := by
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext i
      exact hr _
    _ = (l.items.map (fun x => l.items.map (fun y => decide (G.Adj x y)))).flatten := congrArg List.flatten ho
    _ = _ := rfl
end WLTime.Enumeration

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression Enumeration
variable (M : OneTape) (d q K : ℕ)
open scoped Classical

noncomputable instance valuesFintype : Fintype (Values M d q K) := by
  classical
  letI : Fintype (ConsistencyData.Tag (r:=d+q) (P:=Node M d q) (E:=Edge M d q) K) := inferInstance
  letI : ∀ t : ConsistencyData.Tag (r:=d+q) (P:=Node M d q) (E:=Edge M d q) K,
      Fintype ((instanceData M d q []).TagValue K t) := fun t => by
    cases t <;> dsimp [ConsistencyData.TagValue] <;> infer_instance
  change Fintype ((t : ConsistencyData.Tag (r:=d+q) (P:=Node M d q) (E:=Edge M d q) K) →
    (instanceData M d q []).TagValue K t)
  infer_instance

abbrev RawVertex (w : List Bool) (pad : ℕ) :=
  Enumeration.Vertex (BlockTag M d q K) (Values M d q K) w.length
    ((instanceData M d q w).slotLimit K) pad

noncomputable def listing (w : List Bool) (pad : ℕ) : Listing (RawVertex M d q K w pad) :=
  Enumeration.rectangle (ofFintype (BlockTag M d q K)) (ofFintype (Values M d q K))
    w.length ((instanceData M d q w).slotLimit K) pad

inductive Location (J : Type uJ) where
  | hub | hole
  | slot (tag : BlockTag M d q K) (value : Values M d q K) (a b i : Expr J)

namespace Location
variable {M d q K} {J : Type uJ} {J' : Type uJ'}
def rename (f : J → J') : Location M d q K J → Location M d q K J'
  | .hub => .hub
  | .hole => .hole
  | .slot t v a b i => .slot t v (a.rename f) (b.rename f) (i.rename f)
end Location

variable {J : Type uJ}
inductive Represents (σ : J → ℕ) (w : List Bool) (pad : ℕ) :
    Location M d q K J → RawVertex M d q K w pad → Prop
  | hub : Represents σ w pad .hub none
  | hole (i : Fin pad) : Represents σ w pad .hole (some (.inr i))
  | slot (t : BlockTag M d q K) (v : Values M d q K) (a b i : Expr J)
      (x y : Fin w.length) (s : Fin ((instanceData M d q w).slotLimit K))
      (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val) (hi : i.eval σ w=s.val) :
      Represents σ w pad (.slot t v a b i) (some (.inl ((t,v,x,y),s)))

 theorem Represents.rename {J' : Type uJ'} (f : J → J') (σ : J' → ℕ) (w : List Bool) (pad : ℕ)
    (x : Location M d q K J) (v : RawVertex M d q K w pad)
    (h : Represents M d q K (σ ∘ f) w pad x v) :
    Represents M d q K σ w pad (x.rename f) v := by
  cases h with
  | hub => exact .hub
  | hole i => exact .hole i
  | slot t v a b i x y s ha hb hi =>
    exact .slot t v _ _ _ x y s (by simpa only [Expr.rename_eval] using ha)
      (by simpa only [Expr.rename_eval] using hb) (by simpa only [Expr.rename_eval] using hi)

noncomputable def adjacency (N : Expr J) (ε : F₂) :
    Location M d q K J → Location M d q K J → Predicate J
  | .hub,.hub => .truth false
  | .hub,_ => .truth true
  | _,.hub => .truth true
  | .slot t v a b i,.slot u z c e j => slotPredicate M d q K N ε t u v z a b i c e j
  | _,_ => .truth false

 theorem adjacency_correct (N : Expr J) (hK : 0<K) (hr : 1≤d+q) (ε : F₂)
    (σ : J → ℕ) (w : List Bool) (pad : ℕ) (hN : N.eval σ w=w.length)
    (x y : Location M d q K J) (v z : RawVertex M d q K w pad)
    (hx : Represents M d q K σ w pad x v) (hy : Represents M d q K σ w pad y z) :
    (adjacency M d q K N ε x y).Holds σ w ↔
      ((instanceData M d q w).rectangularGraph K hK hr ε pad).Adj v z := by
  cases hx <;> cases hy
  case slot.slot t v a b i x y s ha hb hi u z c e j l h t' hc he hj =>
    exact slotPredicate_correct M d q K N hK hr ε σ w hN t u v z a b i c e j x y l h s t' pad ha hb hi hc he hj
  all_goals simp [adjacency,Predicate.Holds,ConsistencyData.rectangularGraph,
    ConsistencyData.slots,Marking.rawGraph,Marking.rawAdj,Marking.decodeSlots]

abbrev up3 {J : Type uJ} : J → Option (Option (Option J)) := some ∘ some ∘ some

def slotLocation (t : BlockTag M d q K) (v : Values M d q K) : Location M d q K (Option (Option (Option J))) :=
  .slot t v (.var (some (some none))) (.var (some none)) (.var none)

noncomputable def columns (N L P : Expr J) (ε : F₂) (row : Location M d q K J) : Writer J :=
  Enumeration.writer (ofFintype (BlockTag M d q K)) (ofFintype (Values M d q K)) N L P
    (.emit (adjacency M d q K N ε row .hub))
    (fun t v => .emit (adjacency M d q K (N.rename up3) ε (row.rename up3) (slotLocation M d q K t v)))
    (.emit (adjacency M d q K (N.rename some) ε (row.rename some) .hole))

 theorem columns_eval (N L P : Expr J) (hK : 0<K) (hr : 1≤d+q) (ε : F₂)
    (σ : J → ℕ) (w : List Bool) (pad : ℕ)
    (hN : N.eval σ w=w.length) (hL : L.eval σ w=(instanceData M d q w).slotLimit K)
    (hP : P.eval σ w=pad) (row : Location M d q K J) (x : RawVertex M d q K w pad)
    (hx : Represents M d q K σ w pad row x) :
    (columns M d q K N L P ε row).eval σ w=
      (listing M d q K w pad).items.map
        (fun y => decide (((instanceData M d q w).rectangularGraph K hK hr ε pad).Adj x y)) := by
  classical
  rw [show (listing M d q K w pad).items.map
      (fun y => decide (((instanceData M d q w).rectangularGraph K hK hr ε pad).Adj x y)) =
    (listing M d q K w pad).items.flatMap
      (fun y => [decide (((instanceData M d q w).rectangularGraph K hK hr ε pad).Adj x y)]) from
        List.map_eq_flatMap]
  apply Enumeration.writer_eval _ _ N L P _ _ _ σ w w.length _ pad hN hL hP
  · simp only [Writer.eval,List.singleton_inj]
    exact decide_eq_decide.mpr (adjacency_correct M d q K N hK hr ε σ w pad hN row .hub x none hx .hub)
  · intro t v a b i
    simp only [Writer.eval,List.singleton_inj]
    apply decide_eq_decide.mpr
    apply adjacency_correct M d q K _ hK hr ε _ w pad
    · simpa only [Expr.rename_eval,up3,Function.comp_def,Option.elim'_some] using hN
    · exact Represents.rename M d q K up3 _ w pad row x hx
    · exact .slot t v _ _ _ a b i rfl rfl rfl
  · intro i
    simp only [Writer.eval,List.singleton_inj]
    apply decide_eq_decide.mpr
    apply adjacency_correct M d q K _ hK hr ε _ w pad
    · simpa only [Expr.rename_eval,Function.comp_def,Option.elim'_some] using hN
    · exact Represents.rename M d q K some _ w pad row x hx
    · exact .hole i

noncomputable def matrixWriter (N L P : Expr J) (ε : F₂) : Writer J :=
  Enumeration.writer (ofFintype (BlockTag M d q K)) (ofFintype (Values M d q K)) N L P
    (columns M d q K N L P ε .hub)
    (fun t v => columns M d q K (N.rename up3) (L.rename up3) (P.rename up3) ε (slotLocation M d q K t v))
    (columns M d q K (N.rename some) (L.rename some) (P.rename some) ε .hole)

 theorem matrixWriter_eval (N L P : Expr J) (hK : 0<K) (hr : 1≤d+q) (ε : F₂)
    (σ : J → ℕ) (w : List Bool) (pad : ℕ)
    (hN : N.eval σ w=w.length) (hL : L.eval σ w=(instanceData M d q w).slotLimit K)
    (hP : P.eval σ w=pad) :
    (matrixWriter M d q K N L P ε).eval σ w=
      (listing M d q K w pad).items.flatMap (fun x => (listing M d q K w pad).items.map
        (fun y => decide (((instanceData M d q w).rectangularGraph K hK hr ε pad).Adj x y))) := by
  apply Enumeration.writer_eval _ _ N L P _ _ _ σ w w.length _ pad hN hL hP
  · exact columns_eval M d q K N L P hK hr ε σ w pad hN hL hP .hub none .hub
  · intro t v a b i
    apply columns_eval M d q K _ _ _ hK hr ε _ w pad
    · simpa only [Expr.rename_eval,up3,Function.comp_def,Option.elim'_some] using hN
    · simpa only [Expr.rename_eval,up3,Function.comp_def,Option.elim'_some] using hL
    · simpa only [Expr.rename_eval,up3,Function.comp_def,Option.elim'_some] using hP
    · exact .slot t v _ _ _ a b i rfl rfl rfl
  · intro i
    apply columns_eval M d q K _ _ _ hK hr ε _ w pad
    · simpa only [Expr.rename_eval,Function.comp_def,Option.elim'_some] using hN
    · simpa only [Expr.rename_eval,Function.comp_def,Option.elim'_some] using hL
    · simpa only [Expr.rename_eval,Function.comp_def,Option.elim'_some] using hP
    · exact .hole i

 theorem columns_depth (N L P : Expr J) (ε : F₂) (row : Location M d q K J) :
    (columns M d q K N L P ε row).depth≤3 :=
  Enumeration.writer_depth _ _ _ _ _ _ _ _ 0 (by exact Nat.zero_le _) (fun _ _ => le_rfl) (by exact Nat.zero_le _)

 theorem matrixWriter_depth (N L P : Expr J) (ε : F₂) : (matrixWriter M d q K N L P ε).depth≤6 :=
  Enumeration.writer_depth _ _ _ _ _ _ _ _ 3 ((columns_depth M d q K N L P ε .hub).trans (by omega))
    (fun t v => columns_depth M d q K _ _ _ ε _) ((columns_depth M d q K _ _ _ ε .hole).trans (by omega))
end WLTime.OneTape.Symbolic

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression Enumeration
variable (M : OneTape) (d q K : ℕ) {J : Type uJ}
open scoped Classical

 theorem coefficient_eq (w : List Bool) :
    coefficient M d q K=(instanceData M d q w).rectCoefficient K := rfl

 theorem tagIndex_le (t : BlockTag M d q K) :
    (Fintype.equivFin _ t).val≤coefficient M d q K := by
  apply (Nat.le_of_lt (Fintype.equivFin _ t).isLt).trans
  exact Nat.le_mul_of_pos_right _ ((instanceData M d q []).tagValues_card_pos K)

 theorem countExpr_bounded (N : Expr J) (t : BlockTag M d q K) (a b : Expr J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hm : 1≤w.length)
    (hN : N.eval σ w=w.length) (hNB : N.Bounded σ w B)
    (ha : a.Bounded σ w B) (hb : b.Bounded σ w B)
    (hax : a.eval σ w<w.length) (hbx : b.eval σ w<w.length)
    (hC : coefficient M d q K≤B) (hL : (instanceData M d q w).slotLimit K≤B) :
    (countExpr M d q K N t a b).Bounded σ w B := by
  let c := coefficient M d q K
  let m := w.length
  let z := (Fintype.equivFin _ t).val
  let x := a.eval σ w
  let y := b.eval σ w
  have hz : z≤c := tagIndex_le M d q K t
  have ht : z<Fintype.card (BlockTag M d q K) := (Fintype.equivFin _ t).isLt
  have hraw : y+m*(x+m*z)+1≤c*m^2 := by
    have hh := ConsistencyData.mixedCode_le K t (⟨x,hax⟩ : Fin m) (⟨y,hbx⟩ : Fin m)
    have hc : Fintype.card (BlockTag M d q K)≤c :=
      Nat.le_mul_of_pos_right _ ((instanceData M d q []).tagValues_card_pos K)
    exact hh.trans (Nat.mul_le_mul_right _ hc)
  have hQ : (c*m^2+1)^2+1≤B := hL
  have hcpos : 1≤c := by
    by_contra h
    have hc0 : c=0 := by omega
    rw [hc0,zero_mul] at hraw
    omega
  have hm2 : m*m≤c*m^2 := by simpa only [pow_two] using Nat.le_mul_of_pos_left (m*m) hcpos
  have hcm : c*m^2+1≤B := by nlinarith [Nat.zero_le ((c*m^2)*(c*m^2))]
  have hzm : m*z≤x+m*z := Nat.le_add_left _ _
  have hxm : x+m*z ≤ m*(x+m*z) := Nat.le_mul_of_pos_left _ hm
  have hsum : y+m*(x+m*z)+1≤B := hraw.trans (by omega)
  have hmul : (y+m*(x+m*z)+1)*(c*m^2+1)≤B := by
    calc
      _ ≤ (c*m^2+1)*(c*m^2+1) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ B := by nlinarith
  unfold countExpr
  simp only [Expr.mul,Expr.add,Expr.Bounded,Expr.eval,Binary.eval,hN]
  change (((b.Bounded σ w B ∧ (N.Bounded σ w B ∧ (a.Bounded σ w B ∧
    (N.Bounded σ w B ∧ z≤B ∧ m*z≤B) ∧ x+m*z≤B) ∧ m*(x+m*z)≤B) ∧ y+m*(x+m*z)≤B) ∧
    1≤B ∧ y+m*(x+m*z)+1≤B) ∧ ((c≤B ∧ (N.Bounded σ w B ∧ N.Bounded σ w B ∧ m*m≤B) ∧
    c*(m*m)≤B) ∧ 1≤B ∧ c*(m*m)+1≤B) ∧ (y+m*(x+m*z)+1)*(c*(m*m)+1)≤B)
  exact ⟨⟨⟨hb,⟨hNB,⟨ha,⟨hNB,hz.trans hC,by omega⟩,by omega⟩,by omega⟩,by omega⟩,
      by omega,hsum⟩,⟨⟨hC,⟨hNB,hNB,hm2.trans (by omega)⟩,by nlinarith [hcm]⟩,
      by omega,by simpa only [pow_two] using hcm⟩,by simpa only [pow_two] using hmul⟩

 theorem sameRect_bounded (t u : BlockTag M d q K) (v z : Values M d q K)
    (a b c e : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (ha : a.Bounded σ w B) (hb : b.Bounded σ w B) (hc : c.Bounded σ w B) (he : e.Bounded σ w B) :
    (sameRect M d q K t u v z a b c e).Bounded σ w B := ⟨trivial,⟨ha,hc⟩,hb,he⟩

 theorem slotPredicate_bounded (N : Expr J) (ε : F₂) (t u : BlockTag M d q K)
    (v z : Values M d q K) (a b i c e j : Expr J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hm : 1≤w.length)
    (hN : N.eval σ w=w.length) (hNB : N.Bounded σ w B)
    (ha : a.Bounded σ w B) (hb : b.Bounded σ w B) (hi : i.Bounded σ w B)
    (hc : c.Bounded σ w B) (he : e.Bounded σ w B) (hj : j.Bounded σ w B)
    (hax : a.eval σ w<w.length) (hbx : b.eval σ w<w.length)
    (hcx : c.eval σ w<w.length) (hex : e.eval σ w<w.length)
    (hC : coefficient M d q K≤B) (hL : (instanceData M d q w).slotLimit K≤B) :
    (slotPredicate M d q K N ε t u v z a b i c e j).Bounded σ w (6*B) := by
  have hB : 1≤B := hm.trans (hN.symm ▸ N.eval_le σ w B hNB)
  have hBB : B≤6*B := by omega
  have hv := validity_bounded M d q N K ε t v a b σ w B hB hNB ha hb
  have hz := validity_bounded M d q N K ε u z c e σ w B hB hNB hc he
  have hR := adjacent_bounded M d q N K t u v z a b c e σ w B hB hNB ha hb hc he
  have hS := sameRect_bounded M d q K t u v z a b c e σ w B ha hb hc he
  have hS' := (sameRect M d q K t u v z a b c e).bounded_mono σ w hS hBB
  have hx := (countExpr M d q K N t a b).bounded_mono σ w
    (countExpr_bounded M d q K N t a b σ w B hm hN hNB ha hb hax hbx hC hL) hBB
  have hy := (countExpr M d q K N u c e).bounded_mono σ w
    (countExpr_bounded M d q K N u c e σ w B hm hN hNB hc he hcx hex hC hL) hBB
  have hi' := i.bounded_mono σ w hi hBB
  have hj' := j.bounded_mono σ w hj hBB
  unfold slotPredicate Predicate.rectangular Predicate.le Predicate.disj
  simp only [Predicate.Bounded]
  exact ⟨hv,hz,⟨hx,hi'⟩,⟨hy,hj'⟩,⟨⟨hi',by exact Nat.zero_le _⟩,⟨hj',by exact Nat.zero_le _⟩,hR⟩,
    ⟨⟨hi',by exact Nat.zero_le _⟩,⟨hj',by exact Nat.zero_le _⟩,hS'⟩,
    ⟨hi',by exact Nat.zero_le _⟩,⟨hj',by exact Nat.zero_le _⟩,hS'⟩

namespace Location
variable {M d q K}
def Bounded (σ : J → ℕ) (w : List Bool) (B : ℕ) : Location M d q K J → Prop
  | .slot _ _ a b i => a.Bounded σ w B ∧ b.Bounded σ w B ∧ i.Bounded σ w B ∧
      a.eval σ w<w.length ∧ b.eval σ w<w.length
  | _ => True
 theorem rename_bounded {J' : Type uJ'} (f : J → J') (x : Location M d q K J)
    (σ : J' → ℕ) (w : List Bool) (B : ℕ) :
    (x.rename f).Bounded σ w B ↔ x.Bounded (σ ∘ f) w B := by
  cases x <;> simp only [rename,Bounded,Expr.rename_bounded,Expr.rename_eval]
end Location

 theorem adjacency_bounded (N : Expr J) (ε : F₂) (x y : Location M d q K J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hm : 1≤w.length)
    (hN : N.eval σ w=w.length) (hNB : N.Bounded σ w B)
    (hx : x.Bounded σ w B) (hy : y.Bounded σ w B)
    (hC : coefficient M d q K≤B) (hL : (instanceData M d q w).slotLimit K≤B) :
    (adjacency M d q K N ε x y).Bounded σ w (6*B) := by
  cases x <;> cases y
  case slot.slot t v a b i u z c e j =>
    exact slotPredicate_bounded M d q K N ε t u v z a b i c e j σ w B hm hN hNB
      hx.1 hx.2.1 hx.2.2.1 hy.1 hy.2.1 hy.2.2.1 hx.2.2.2.1 hx.2.2.2.2 hy.2.2.2.1 hy.2.2.2.2 hC hL
  all_goals trivial

 theorem columns_safe (N L P : Expr J) (ε : F₂) (row : Location M d q K J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hm : 1≤w.length)
    (hN : N.eval σ w=w.length) (hL : L.eval σ w=(instanceData M d q w).slotLimit K)
    (hNB : N.Bounded σ w B) (hLB : L.Bounded σ w B) (hPB : P.Bounded σ w B)
    (hx : row.Bounded σ w B) (hC : coefficient M d q K≤B) :
    (columns M d q K N L P ε row).Safe σ w (6*B) := by
  have hBB : B≤6*B := by omega
  have hlimit : (instanceData M d q w).slotLimit K≤B := hL ▸ L.eval_le σ w B hLB
  apply Enumeration.writer_safe _ _ N L P _ _ _ σ w (6*B)
    (N.bounded_mono σ w hNB hBB) (L.bounded_mono σ w hLB hBB) (P.bounded_mono σ w hPB hBB)
  · exact adjacency_bounded M d q K N ε row .hub σ w B hm hN hNB hx trivial hC hlimit
  · intro t v a ha b hb i hi
    apply adjacency_bounded M d q K _ ε _ _ _ w B hm
    · simpa only [Expr.rename_eval,up3,Function.comp_def,Option.elim'_some] using hN
    · simpa only [Expr.rename_bounded,up3,Function.comp_def,Option.elim'_some] using hNB
    · simpa only [Location.rename_bounded,up3,Function.comp_def,Option.elim'_some] using hx
    · change a≤B ∧ b≤B ∧ i≤B ∧ a<w.length ∧ b<w.length
      have hnB := N.eval_le σ w B hNB
      have hlB := L.eval_le σ w B hLB
      exact ⟨by omega,by omega,by omega,by omega,by omega⟩
    · exact hC
    · exact hlimit
  · intro i hi
    apply adjacency_bounded M d q K _ ε _ _ _ w B hm
    · simpa only [Expr.rename_eval,Function.comp_def,Option.elim'_some] using hN
    · simpa only [Expr.rename_bounded,Function.comp_def,Option.elim'_some] using hNB
    · simpa only [Location.rename_bounded,Function.comp_def,Option.elim'_some] using hx
    · trivial
    · exact hC
    · exact hlimit

 theorem matrixWriter_safe (N L P : Expr J) (ε : F₂)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hm : 1≤w.length)
    (hN : N.eval σ w=w.length) (hL : L.eval σ w=(instanceData M d q w).slotLimit K)
    (hNB : N.Bounded σ w B) (hLB : L.Bounded σ w B) (hPB : P.Bounded σ w B)
    (hC : coefficient M d q K≤B) :
    (matrixWriter M d q K N L P ε).Safe σ w (6*B) := by
  have hBB : B≤6*B := by omega
  apply Enumeration.writer_safe _ _ N L P _ _ _ σ w (6*B)
    (N.bounded_mono σ w hNB hBB) (L.bounded_mono σ w hLB hBB) (P.bounded_mono σ w hPB hBB)
  · exact columns_safe M d q K N L P ε .hub σ w B hm hN hL hNB hLB hPB trivial hC
  · intro t v a ha b hb i hi
    apply columns_safe M d q K _ _ _ ε _ _ w B hm
    · simpa only [Expr.rename_eval,up3,Function.comp_def,Option.elim'_some] using hN
    · simpa only [Expr.rename_eval,up3,Function.comp_def,Option.elim'_some] using hL
    · simpa only [Expr.rename_bounded,up3,Function.comp_def,Option.elim'_some] using hNB
    · simpa only [Expr.rename_bounded,up3,Function.comp_def,Option.elim'_some] using hLB
    · simpa only [Expr.rename_bounded,up3,Function.comp_def,Option.elim'_some] using hPB
    · change a≤B ∧ b≤B ∧ i≤B ∧ a<w.length ∧ b<w.length
      have hnB := N.eval_le σ w B hNB
      have hlB := L.eval_le σ w B hLB
      exact ⟨by omega,by omega,by omega,by omega,by omega⟩
    · exact hC
  · intro i hi
    apply columns_safe M d q K _ _ _ ε _ _ w B hm
    · simpa only [Expr.rename_eval,Function.comp_def,Option.elim'_some] using hN
    · simpa only [Expr.rename_eval,Function.comp_def,Option.elim'_some] using hL
    · simpa only [Expr.rename_bounded,Function.comp_def,Option.elim'_some] using hNB
    · simpa only [Expr.rename_bounded,Function.comp_def,Option.elim'_some] using hLB
    · simpa only [Expr.rename_bounded,Function.comp_def,Option.elim'_some] using hPB
    · trivial
    · exact hC
end WLTime.OneTape.Symbolic

end OAI
