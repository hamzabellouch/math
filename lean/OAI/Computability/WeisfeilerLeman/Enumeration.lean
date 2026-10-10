import OAI.Computability.WeisfeilerLeman.Padding

namespace OAI

universe uT uL uA uP uE uV uW uD uU

namespace WLTime.Compression

inductive NameTag (r : ℕ) (T : Type uT) (L : Type uL) where
  | horizontal (row : Fin (r+1)) (type : T)
  | vertical (row : Fin (r+1)) (link : L)
  deriving DecidableEq, Fintype

namespace ReadoutName
variable {r : ℕ} {T : Type uT} {L : Type uL} {A : Type uA}
def tag : ReadoutName r T L A → NameTag r T L
  | .horizontal i t _ _ => .horizontal i t
  | .vertical i l _ => .vertical i l
end ReadoutName

theorem link_endpoints_ne {P : Type uP} {E : Type uE} (K : ℕ) (hK : 0<K)
    (src dst : E → P) (l : TypeLink K E) : linkLeft K src l ≠ linkRight K dst l := by
  intro h
  by_cases h0 : l.2.val=0
  · have h4 : l.2.val≠4*K := by omega
    simp only [linkLeft,linkRight,dite_eq_left h0,dite_eq_right h4,reduceCtorEq] at h
  · by_cases h4 : l.2.val=4*K
    · simp only [linkLeft,linkRight,dite_eq_right h0,dite_eq_left h4,reduceCtorEq] at h
    · simp only [linkLeft,linkRight,dite_eq_right h0,dite_eq_right h4,Sum.inr.injEq,Prod.mk.injEq,
        true_and,Fin.mk.injEq] at h
      omega

namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

abbrev Tag (K : ℕ) := NameTag r (TypeNode K P E) (TypeLink K E)
abbrev TagValue (K : ℕ) : Tag (r:=r) (P:=P) (E:=E) K → Type
  | .horizontal _ t => I.Value K t
  | .vertical _ _ => F₂
abbrev TagValues (K : ℕ) := (v : Tag (r:=r) (P:=P) (E:=E) K) → I.TagValue K v

instance (K : ℕ) (n : Tag (r:=r) (P:=P) (E:=E) K) : Zero (I.TagValue K n) := by
  cases n <;> dsimp [TagValue] <;> infer_instance
instance (K : ℕ) (n : Tag (r:=r) (P:=P) (E:=E) K) : Fintype (I.TagValue K n) := by
  cases n <;> dsimp [TagValue] <;> infer_instance

def tagRead (K : ℕ) (v : I.TagValues K) : I.Readouts K
  | .horizontal i t _ _ => v (.horizontal i t)
  | .vertical i l _ => v (.vertical i l)

theorem tag_injective_on_footprint (K : ℕ) (hK : 0<K) (hr : 1≤r)
    (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K) :
    Set.InjOn ReadoutName.tag {x | x ∈ I.footprint K b} := by
  classical
  intro x hx y hy hxy
  cases b with
  | site i t a b =>
    simp only [footprint,Finset.mem_singleton] at hx hy
    exact hx.trans hy.symm
  | square i l a b =>
    simp only [footprint,Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;>
      simp only [ReadoutName.tag,NameTag.horizontal.injEq,NameTag.vertical.injEq,
        reduceCtorEq,true_and,and_true] at hxy <;> try rfl
    · exact False.elim (link_endpoints_ne K hK I.src I.dst l hxy)
    · exact False.elim (link_endpoints_ne K hK I.src I.dst l hxy.symm)
    · exact False.elim (rotate_ne_self hr i hxy.symm)
    · exact False.elim (rotate_ne_self hr i hxy)

def TagSupported (K : ℕ) (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K)
    (v : I.TagValues K) : Prop :=
  ∀ t, (∀ n ∈ I.footprint K b, ReadoutName.tag n ≠ t) → v t=0

 theorem tagRead_injective (K : ℕ) (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K)
    {v w : I.TagValues K} (hv : I.TagSupported K b v) (hw : I.TagSupported K b w)
    (h : I.atBlock K b (I.tagRead K v)=I.atBlock K b (I.tagRead K w)) : v=w := by
  classical
  funext t
  by_cases ht : ∃ n ∈ I.footprint K b, ReadoutName.tag n=t
  · obtain ⟨n,hn,hnv⟩ := ht
    have he := congrArg (fun z : I.blockSpace K b => z.val n) h
    rw [I.atBlock_apply K b _ n hn,I.atBlock_apply K b _ n hn] at he
    cases n <;> cases hnv <;> exact he
  · have hn : ∀ n ∈ I.footprint K b, ReadoutName.tag n≠t := by simpa using ht
    exact (hv t hn).trans (hw t hn).symm

def toTag (K : ℕ) (n : RawName (r:=r) (m:=m) (P:=P) (E:=E) K)
    (x : I.ReadValue K n) : I.TagValue K (ReadoutName.tag n) := by
  cases n <;> exact x

noncomputable def encodeTags (K : ℕ) (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K)
    (v : I.blockSpace K b) : I.TagValues K := by
  classical
  intro t
  exact if h : ∃ n ∈ I.footprint K b, ReadoutName.tag n=t then
    h.choose_spec.2 ▸ I.toTag K h.choose (v.val h.choose)
  else 0

theorem encodeTags_supported (K : ℕ)
    (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K) (v : I.blockSpace K b) :
    I.TagSupported K b (I.encodeTags K b v) := by
  classical
  intro t ht
  have hn : ¬∃ n ∈ I.footprint K b,ReadoutName.tag n=t := by
    rintro ⟨n,hn,he⟩; exact ht n hn he
  simp only [encodeTags,dite_eq_right hn]

theorem encodeTags_apply (K : ℕ) (hK : 0<K) (hr : 1≤r)
    (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K) (v : I.blockSpace K b)
    (n : RawName (r:=r) (m:=m) (P:=P) (E:=E) K) (hn : n∈I.footprint K b) :
    I.encodeTags K b v (ReadoutName.tag n)=I.toTag K n (v.val n) := by
  classical
  let h : ∃ j ∈ I.footprint K b, ReadoutName.tag j=ReadoutName.tag n := ⟨n,hn,rfl⟩
  have he : h.choose=n := I.tag_injective_on_footprint K hK hr b h.choose_spec.1 hn h.choose_spec.2
  simp only [encodeTags,dite_eq_left h]
  have hh : ∀ (j : RawName (r:=r) (m:=m) (P:=P) (E:=E) K) (_ : j=n)
      (ht : ReadoutName.tag j=ReadoutName.tag n),
      ht ▸ I.toTag K j (v.val j)=I.toTag K n (v.val n) := by
    intro j hj ht; subst j; rfl
  exact hh _ he _

theorem tagRead_encodeTags (K : ℕ) (hK : 0<K) (hr : 1≤r)
    (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K) (v : I.blockSpace K b) :
    I.atBlock K b (I.tagRead K (I.encodeTags K b v))=v := by
  classical
  apply Subtype.ext
  funext n
  by_cases hn : n∈I.footprint K b
  · rw [I.atBlock_apply K b _ n hn]
    have he := I.encodeTags_apply K hK hr b v n hn
    cases n <;> exact he
  · change (if n∈I.footprint K b then _ else 0)=v.val n
    rw [ite_eq_right hn,v.property n hn]

noncomputable def tagSpaceEquiv (K : ℕ) (hK : 0<K) (hr : 1≤r)
    (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K) :
    {v : I.TagValues K // I.TagSupported K b v} ≃ I.blockSpace K b where
  toFun v := I.atBlock K b (I.tagRead K v.val)
  invFun v := ⟨I.encodeTags K b v,I.encodeTags_supported K b v⟩
  left_inv v := by
    apply Subtype.ext
    exact I.tagRead_injective K b (I.encodeTags_supported K b _) v.property
      (I.tagRead_encodeTags K hK hr b _)
  right_inv := I.tagRead_encodeTags K hK hr b

abbrev Descriptor (K : ℕ) := RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K × I.TagValues K

def DescriptorValid (K : ℕ) (ε : F₂) (v : I.Descriptor K) : Prop :=
  I.ValidBlock K v.1 ∧ I.TagSupported K v.1 v.2 ∧
    I.blockForm K v.1 (I.tagRead K v.2)=ε*I.blockBias K v.1

noncomputable def descriptorEquiv (K : ℕ) (hK : 0<K) (hr : 1≤r) (ε : F₂) :
    {v : I.Descriptor K // I.DescriptorValid K ε v} ≃ I.Vertex K ε where
  toFun v := ⟨⟨v.val.1,v.property.1⟩,⟨I.atBlock K v.val.1 (I.tagRead K v.val.2),
    by rw [I.blockForm_atBlock]; exact v.property.2.2⟩⟩
  invFun v := ⟨(v.1.val,I.encodeTags K v.1.val v.2.val),v.1.property,
    I.encodeTags_supported K v.1.val v.2.val,by
      rw [← I.blockForm_atBlock,I.tagRead_encodeTags K hK hr]; exact v.2.property⟩
  left_inv v := by
    apply Subtype.ext
    dsimp
    congr 1
    exact I.tagRead_injective K v.val.1 (I.encodeTags_supported K _ _) v.property.2.1
      (I.tagRead_encodeTags K hK hr _ _)
  right_inv v := by
    apply Vertex.ext
    · rfl
    · exact congrArg Subtype.val (I.tagRead_encodeTags K hK hr _ _)

end ConsistencyData
end WLTime.Compression

namespace WLTime.Marking
variable {V : Type uV} {W : Type uW} {D : Type uD} [Fintype V] [Fintype W]

theorem degree_detect_base_spaced (G : SimpleGraph V) (H : SimpleGraph W)
    (c : V → D) (d : W → D) (code : D → ℕ) (hcode : Function.Injective code)
    (hpos : ∀ b, 0 < code b) (e : V ≃ W) (hc : ∀ v, c v = d (e v))
    (q B : ℕ) (hB : Fintype.card V ≤ B) (hN : 2 ≤ Fintype.card V) (x : V)
    (y : Vertex W (fun v => code (d v)*(B+1)) q)
    (hd : Pebble.degree (graph G (fun v => code (c v)*(B+1)) q) (.base x) =
      Pebble.degree (graph H (fun v => code (d v)*(B+1)) q) y) :
    ∃ z, y = .base z ∧ c x = d z := by
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr e
  have hx : 2 < Pebble.degree (graph G (fun v => code (c v)*(B+1)) q) (.base x) := by
    rw [degree_base]
    have hm := Nat.mul_le_mul_right (B+1) (hpos (c x))
    nlinarith
  cases y with
  | base z =>
    refine ⟨z,rfl,hcode ?_⟩
    rw [degree_base,degree_base] at hd
    exact code_of_degree ((base_degree_lt G x).trans_le hB) ((hcard ▸ base_degree_lt H z).trans_le hB) hd
  | mark z i => rw [degree_mark] at hd; omega
  | pad i => rw [degree_pad] at hd; omega
  | hub =>
    have hsum : (∑ v : W, code (d v)*(B+1)) =
        ∑ v : V, code (c v)*(B+1) := by
      rw [← e.sum_comp (fun v => code (d v)*(B+1))]
      simp_rw [← hc]
    have hh := hub_above_base G (fun v => code (c v)*(B+1)) q hN
      (fun v => Nat.mul_pos (hpos (c v)) (by omega)) x
    rw [degree_hub] at hd hh
    rw [← hcard,hsum] at hd
    omega

theorem wins_bases_spaced (G : SimpleGraph V) (H : SimpleGraph W)
    (c : V → D) (d : W → D) (code : D → ℕ) (hcode : Function.Injective code)
    (hpos : ∀ b, 0 < code b) (e₀ : V ≃ W) (hc : ∀ v, c v = d (e₀ v))
    (q K B : ℕ) (hB : Fintype.card V ≤ B) (hN : 2 ≤ Fintype.card V) (hK : 2 ≤ K)
    (h : Pebble.Wins (graph G (fun v => code (c v)*(B+1)) q)
      (graph H (fun v => code (d v)*(B+1)) q) (fun _ _ => True)
      (fun _ : Fin K => none)) :
    Pebble.Wins G H (fun v w => c v = d w) (fun _ : Fin K => none) := by
  classical
  let J : Pebble.Invariant G H (fun v w => c v = d w) K := {
    safe := fun P => Pebble.Wins (graph G (fun v => code (c v)*(B+1)) q)
      (graph H (fun v => code (d v)*(B+1)) q) (fun _ _ => True) (basePosition P)
    forget := by
      intro P Q hQ hPQ
      refine hQ.forget (fun i => ?_)
      rcases hPQ i with hi | hi
      · exact Or.inl (by simp [basePosition,hi])
      · exact Or.inr (by simp [basePosition,hi])
    atomic := by
      intro P hP
      constructor
      · intro i x y hi
        have hdi := hP.degree_eq hK (i := i) (x := .base x) (y := .base y) (by simp [basePosition,hi])
        obtain ⟨z,hz,hcz⟩ := degree_detect_base_spaced G H c d code hcode hpos e₀ hc q B hB hN x (.base y) hdi
        cases Vertex.base.inj hz
        exact hcz
      · intro i j x y u v hi hj
        have hh := hP.atomic.2 i j (.base x) (.base y) (.base u) (.base v)
          (by simp [basePosition,hi]) (by simp [basePosition,hj])
        simpa only [Vertex.base.injEq,graph,Adj] using hh
    extend := by
      intro P hP i hi
      obtain ⟨e,he⟩ := hP.extend i (by simp [basePosition,hi])
      have hb (x : V) : ∃ y, e (.base x) = .base y ∧ c x = d y := by
        exact degree_detect_base_spaced G H c d code hcode hpos e₀ hc q B hB hN x (e (.base x))
          ((he (.base x)).degree_eq hK (Function.update_self _ _ _))
      choose f hf hcf using hb
      have hinj : Function.Injective f := by
        intro x y hxy
        exact Vertex.base.inj (e.injective (by rw [hf,hf,hxy]))
      let eb : V ≃ W := Equiv.ofBijective f
        ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj,Fintype.card_congr e₀⟩)
      refine ⟨eb,fun x => ?_⟩
      rw [basePosition_update]
      simpa only [hf,eb,Equiv.ofBijective_apply] using he (.base x) }
  refine ⟨J,?_⟩
  unfold J basePosition
  exact h

end WLTime.Marking

namespace WLTime.Marking

abbrev Slot (V : Type uV) (count : V → ℕ) := V ⊕ ((v : V) × Fin (count v))

variable {V : Type uV} {U : Type uU} {count : V → ℕ}

def slotAdj (G : SimpleGraph V) : Slot V count → Slot V count → Prop
  | .inl x,.inl y => G.Adj x y
  | .inl x,.inr y => x=y.1
  | .inr x,.inl y => x.1=y
  | .inr _,.inr _ => False

def rawAdj (G : SimpleGraph V) (decode : U → Option (Slot V count)) : Option U → Option U → Prop
  | none,none => False
  | none,some _ => True
  | some _,none => True
  | some x,some y => match decode x,decode y with
    | some a,some b => slotAdj G a b
    | _,_ => False

def rawGraph (G : SimpleGraph V) (decode : U → Option (Slot V count)) : SimpleGraph (Option U) where
  Adj := rawAdj G decode
  symm := ⟨by
    intro x y h; cases x <;> cases y <;> simp only [rawAdj] at h ⊢; try exact h
    split at h <;> try contradiction
    rename_i a b hx hy
    rw [hy,hx]
    cases a <;> cases b <;> simp only [slotAdj] at h ⊢ <;>
      first | exact G.symm h | exact h.symm⟩
  loopless := ⟨by
    intro x; cases x with
    | none => simp only [rawAdj,not_false_eq_true]
    | some x =>
      cases h : decode x with
      | none => simp only [rawAdj,h,not_false_eq_true]
      | some v => cases v <;> simp only [rawAdj,h,slotAdj,G.irrefl,not_false_eq_true]⟩

theorem raw_diameter (G : SimpleGraph V) (decode : U → Option (Slot V count)) (x y : Option U) :
    x=y ∨ (rawGraph G decode).Adj x y ∨
      ∃ z,(rawGraph G decode).Adj x z ∧ (rawGraph G decode).Adj z y := by
  cases x <;> cases y <;> simp only [rawGraph,rawAdj] <;> try tauto

noncomputable def rawEquiv [Fintype U] (decode : U → Option (Slot V count))
    (h : ∀ v, ∃!u,decode u=some v) :
    Option U ≃ Vertex V count (Fintype.card {u // decode u=none}) := by
  classical
  let pre : Slot V count → U := fun v => (h v).exists.choose
  have hp (v) : decode (pre v)=some v := (h v).exists.choose_spec
  have hi (v) (u) (hu : decode u=some v) : pre v=u := (h v).unique (hp v) hu
  let holes := Fintype.equivFin {u // decode u=none}
  let enc : Option U → Vertex V count (Fintype.card {u // decode u=none}) := fun x =>
    match x with
    | none => .hub
    | some u => if he : decode u=none then .pad (holes ⟨u,he⟩) else
        match decode u with
        | none => .hub
        | some (.inl v) => .base v
        | some (.inr v) => .mark v.1 v.2
  let dec : Vertex V count (Fintype.card {u // decode u=none}) → Option U := fun v =>
    match v with
    | .base v => some (pre (.inl v))
    | .mark v i => some (pre (.inr ⟨v,i⟩))
    | .hub => none
    | .pad i => some (holes.symm i).val
  exact {
    toFun := enc
    invFun := dec
    left_inv := by
      intro x; cases x with
      | none => rfl
      | some u =>
        cases he : decode u with
        | none => simp only [enc,he,↓reduceDIte,dec,Equiv.symm_apply_apply]
        | some v =>
          cases v with
          | inl v => simp only [enc,he,reduceCtorEq,↓reduceDIte,dec,hi _ _ he]
          | inr v => simp only [enc,he,reduceCtorEq,↓reduceDIte,dec,hi _ _ he]
    right_inv := by
      intro v; cases v with
      | hub => rfl
      | base v => simp only [dec,enc,hp,reduceCtorEq,↓reduceDIte]
      | mark v i => simp only [dec,enc,hp,reduceCtorEq,↓reduceDIte]
      | pad i =>
        have he := (holes.symm i).property
        simp only [dec,enc,he,↓reduceDIte]
        congr 1
        exact holes.apply_symm_apply i }

theorem rawEquiv_adj [Fintype U] (G : SimpleGraph V) (decode : U → Option (Slot V count))
    (h : ∀ v,∃!u,decode u=some v) (x y : Option U) :
    (graph G count _).Adj (rawEquiv decode h x) (rawEquiv decode h y) ↔
      (rawGraph G decode).Adj x y := by
  classical
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      cases hy : decode y with
      | none => simp only [rawEquiv,Equiv.coe_fn_mk,hy,↓reduceDIte,graph,rawGraph,rawAdj,Adj]
      | some v => cases v <;> simp only [rawEquiv,Equiv.coe_fn_mk,hy,reduceCtorEq,↓reduceDIte,graph,rawGraph,rawAdj,Adj]
  | some x =>
    cases y with
    | none =>
      cases hx : decode x with
      | none => simp only [rawEquiv,Equiv.coe_fn_mk,hx,↓reduceDIte,graph,rawGraph,rawAdj,Adj]
      | some v => cases v <;> simp only [rawEquiv,Equiv.coe_fn_mk,hx,reduceCtorEq,↓reduceDIte,graph,rawGraph,rawAdj,Adj]
    | some y =>
      cases hx : decode x with
      | none =>
        cases hy : decode y with
        | none => simp only [rawEquiv,Equiv.coe_fn_mk,hx,hy,↓reduceDIte,graph,rawGraph,rawAdj,Adj]
        | some v => cases v <;> simp only [rawEquiv,Equiv.coe_fn_mk,hx,hy,reduceCtorEq,↓reduceDIte,graph,rawGraph,rawAdj,Adj]
      | some v =>
        cases hy : decode y with
        | none => cases v <;> simp only [rawEquiv,Equiv.coe_fn_mk,hx,hy,reduceCtorEq,↓reduceDIte,graph,rawGraph,rawAdj,Adj]
        | some w => cases v <;> cases w <;> simp only [rawEquiv,Equiv.coe_fn_mk,hx,hy,reduceCtorEq,↓reduceDIte,graph,rawGraph,rawAdj,Adj,slotAdj]

end WLTime.Marking

namespace WLTime.Marking

variable {D : Type uD} {V : Type uV} {p : D → Prop} {count : V → ℕ}

noncomputable def decodeSlots (e : {d // p d} ≃ V) (L q : ℕ) :
    (D × Fin L) ⊕ Fin q → Option (Slot V count) := by
  classical
  exact fun u => match u with
    | .inr _ => none
    | .inl (d,j) => if hd : p d then
        if j.val=0 then some (.inl (e ⟨d,hd⟩)) else
        if hj : j.val-1<count (e ⟨d,hd⟩) then some (.inr ⟨e ⟨d,hd⟩,⟨j.val-1,hj⟩⟩)
        else none
      else none

 theorem decodeSlots_complete (e : {d // p d} ≃ V) (L q : ℕ)
    (hL : ∀ v,count v+1≤L) (v : Slot V count) :
    ∃! u,decodeSlots e L q u=some v := by
  classical
  cases v with
  | inl v =>
    let d := e.symm v
    let j : Fin L := ⟨0,by have := hL v; omega⟩
    refine ⟨.inl (d.val,j),?_,?_⟩
    · have hed : e ⟨d.val,d.property⟩=v := e.apply_symm_apply v
      simp only [decodeSlots,d.property,↓reduceDIte,j,↓reduceIte]
      exact congrArg (fun v => some (Sum.inl v)) hed
    · intro u hu
      cases u with
      | inr u => simp only [decodeSlots,reduceCtorEq] at hu
      | inl u =>
        rcases u with ⟨a,i⟩
        by_cases ha : p a
        · by_cases hi : i.val=0
          · simp only [decodeSlots,dite_eq_left ha,ite_eq_left hi,Option.some.injEq,Sum.inl.injEq] at hu
            have hd : (⟨a,ha⟩ : {d // p d})=d := e.injective (hu.trans (e.apply_symm_apply v).symm)
            have hj : i=j := Fin.ext hi
            rw [← congrArg Subtype.val hd,← hj]
          · simp only [decodeSlots,dite_eq_left ha,ite_eq_right hi] at hu
            split at hu <;> simp only [Option.some.injEq,reduceCtorEq] at hu
        · simp only [decodeSlots,dite_eq_right ha,reduceCtorEq] at hu
  | inr v =>
    rcases v with ⟨v,i⟩
    let d := e.symm v
    let j : Fin L := ⟨i.val+1,by have := hL v; omega⟩
    refine ⟨.inl (d.val,j),?_,?_⟩
    · have hed : e ⟨d.val,d.property⟩=v := e.apply_symm_apply v
      simp only [decodeSlots,d.property,↓reduceDIte,j,Nat.add_eq_zero_iff,
        Nat.one_ne_zero,and_false,↓reduceIte,Nat.add_sub_cancel]
      simp only [hed,i.isLt,↓reduceDIte]
      congr 2
      apply Sigma.ext hed
      exact (Fin.heq_ext_iff (congrArg count hed)).mpr rfl
    · intro u hu
      cases u with
      | inr u => simp only [decodeSlots,reduceCtorEq] at hu
      | inl u =>
        rcases u with ⟨a,t⟩
        by_cases ha : p a
        · by_cases ht : t.val=0
          · simp only [decodeSlots,dite_eq_left ha,ite_eq_left ht,Option.some.injEq,reduceCtorEq] at hu
          · simp only [decodeSlots,dite_eq_left ha,ite_eq_right ht] at hu
            split at hu
            · rename_i hh
              have he : e ⟨a,ha⟩=v := congrArg (fun z : Option (Slot V count) =>
                z.elim (e ⟨a,ha⟩) (Sum.elim id Sigma.fst)) hu
              have hd : (⟨a,ha⟩ : {d // p d})=d := e.injective (he.trans (e.apply_symm_apply v).symm)
              have hx : t.val-1=i.val := congrArg (fun z : Option (Slot V count) =>
                z.elim 0 (Sum.elim (fun _ => 0) (fun v => v.2.val))) hu
              have hj : t=j := Fin.ext (by dsimp [j]; omega)
              rw [← congrArg Subtype.val hd,← hj]
            · simp only [reduceCtorEq] at hu
        · simp only [decodeSlots,dite_eq_right ha,reduceCtorEq] at hu

 theorem raw_holes_eq {W : Type uW} {U : Type uU} [Fintype V] [Fintype W] [Fintype U]
    {count' : W → ℕ} (e : V ≃ W) (he : ∀ v,count v=count' (e v))
    (a : U → Option (Slot V count)) (b : U → Option (Slot W count'))
    (ha : ∀ v,∃!u,a u=some v) (hb : ∀ v,∃!u,b u=some v) :
    Fintype.card {u // a u=none}=Fintype.card {u // b u=none} := by
  classical
  have h1 := Fintype.card_congr (rawEquiv a ha)
  have h2 := Fintype.card_congr (rawEquiv b hb)
  rw [card_vertices] at h1 h2
  have hc := Fintype.card_congr e
  have hs : ∑ v,count v=∑ w,count' w := by
    rw [← e.sum_comp count']; simp_rw [he]
  omega

end WLTime.Marking

end OAI
