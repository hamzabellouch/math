import OAI.Computability.WeisfeilerLeman.Expressions

namespace OAI

universe uK uJ uT uL uP uE

namespace WLTime.NatCode
namespace Expr
variable {K : Type uK} {J : Type uJ}

def bind (f : K → Expr J) : Expr K → Expr J
  | .const n => .const n
  | .var k => f k
  | .binary op a b => .binary op (a.bind f) (b.bind f)
  | .bit a => .bit (a.bind f)

@[simp] theorem bind_eval (f : K → Expr J) (σ : J → ℕ) (w : List Bool) (e : Expr K) :
    (e.bind f).eval σ w=e.eval (fun k => (f k).eval σ w) w := by
  induction e with
  | const | var => rfl
  | binary op a b ha hb => simp only [bind,eval,ha,hb]
  | bit a ha => simp only [bind,eval,ha]

 theorem bounded_mono (e : Expr K) (σ : K → ℕ) (w : List Bool) {A B : ℕ}
    (h : e.Bounded σ w A) (hAB : A≤B) : e.Bounded σ w B := by
  induction e with
  | const | var => exact h.trans hAB
  | binary op a b ha hb => exact ⟨ha h.1,hb h.2.1,h.2.2.trans hAB⟩
  | bit a ha => exact ⟨ha h.1,h.2.trans hAB⟩
end Expr

inductive Predicate (K : Type uK) where
  | truth (b : Bool)
  | eq (a b : Expr K)
  | lt (a b : Expr K)
  | bit (a : Expr K)
  | conj (a b : Predicate K)
  | neg (a : Predicate K)

namespace Predicate
variable {K : Type uK}

def Holds (σ : K → ℕ) (w : List Bool) : Predicate K → Prop
  | .truth b => b=true
  | .eq a b => a.eval σ w=b.eval σ w
  | .lt a b => a.eval σ w<b.eval σ w
  | .bit a => w.getD (a.eval σ w) false=true
  | .conj a b => a.Holds σ w ∧ b.Holds σ w
  | .neg a => ¬a.Holds σ w

instance decidableHolds (σ : K → ℕ) (w : List Bool) : (p : Predicate K) → Decidable (p.Holds σ w)
  | .truth _ | .eq _ _ | .lt _ _ | .bit _ => by unfold Holds; infer_instance
  | .conj a b => @instDecidableAnd _ _ (decidableHolds σ w a) (decidableHolds σ w b)
  | .neg a => @instDecidableNot _ (decidableHolds σ w a)

def code : Predicate K → Expr K
  | .truth b => .const (if b then 1 else 0)
  | .eq a b => .binary .sub (.const 1) (.binary .add (.binary .sub a b) (.binary .sub b a))
  | .lt a b => .binary .sub (.const 1) (.binary .sub (.const 1) (.binary .sub b a))
  | .bit a => .bit a
  | .conj a b => .binary .mul a.code b.code
  | .neg a => .binary .sub (.const 1) a.code

 theorem code_eval (σ : K → ℕ) (w : List Bool) (p : Predicate K) :
    p.code.eval σ w=if p.Holds σ w then 1 else 0 := by
  induction p with
  | truth b => cases b <;> rfl
  | eq a b =>
    simp only [code,Expr.eval,Binary.eval,Holds]
    by_cases hab : a.eval σ w=b.eval σ w <;> simp only [hab,↓reduceIte] <;> omega
  | lt a b =>
    simp only [code,Expr.eval,Binary.eval,Holds]
    by_cases hab : a.eval σ w<b.eval σ w <;> simp only [hab,↓reduceIte] <;> omega
  | bit a => rfl
  | conj a b ha hb =>
    simp only [code,Expr.eval,Binary.eval,Holds,ha,hb]
    split_ifs <;> simp_all
  | neg a ha =>
    simp only [code,Expr.eval,Binary.eval,Holds,ha]
    split_ifs <;> simp_all

 theorem code_le_one (σ : K → ℕ) (w : List Bool) (p : Predicate K) :
    p.code.eval σ w≤1 := by rw [code_eval]; split_ifs <;> omega

def Bounded (σ : K → ℕ) (w : List Bool) (B : ℕ) : Predicate K → Prop
  | .truth _ => True
  | .eq a b | .lt a b => a.Bounded σ w B ∧ b.Bounded σ w B
  | .bit a => a.Bounded σ w B
  | .conj a b => a.Bounded σ w B ∧ b.Bounded σ w B
  | .neg a => a.Bounded σ w B

 theorem code_bounded (σ : K → ℕ) (w : List Bool) (B : ℕ) (p : Predicate K)
    (h : p.Bounded σ w B) : p.code.Bounded σ w (2*B+1) := by
  have hB : B≤2*B+1 := by omega
  have h1 : 1≤2*B+1 := by omega
  induction p with
  | truth b => change (if b then 1 else 0)≤2*B+1; split_ifs <;> omega
  | eq a b =>
    have ha := a.eval_le σ w B h.1
    have hb := b.eval_le σ w B h.2
    exact ⟨h1,⟨⟨a.bounded_mono σ w h.1 hB,b.bounded_mono σ w h.2 hB,by dsimp [Binary.eval]; omega⟩,
      ⟨b.bounded_mono σ w h.2 hB,a.bounded_mono σ w h.1 hB,by dsimp [Binary.eval]; omega⟩,
      by dsimp [Expr.eval,Binary.eval]; omega⟩,by dsimp [Expr.eval,Binary.eval]; omega⟩
  | lt a b =>
    have hb := b.eval_le σ w B h.2
    exact ⟨h1,⟨h1,⟨b.bounded_mono σ w h.2 hB,a.bounded_mono σ w h.1 hB,
      by dsimp [Binary.eval]; omega⟩,by dsimp [Expr.eval,Binary.eval]; omega⟩,
      by dsimp [Expr.eval,Binary.eval]; omega⟩
  | bit a => exact ⟨a.bounded_mono σ w h hB,h1⟩
  | conj a b ha hb =>
    refine ⟨ha h.1,hb h.2,(Nat.mul_le_mul (a.code_le_one σ w) (b.code_le_one σ w)).trans ?_⟩
    exact h1
  | neg a ha => exact ⟨h1,ha h,by dsimp [Expr.eval,Binary.eval]; omega⟩

def disj (a b : Predicate K) := (a.neg.conj b.neg).neg
@[simp] theorem holds_disj (σ : K → ℕ) (w : List Bool) (a b : Predicate K) :
    (a.disj b).Holds σ w ↔ a.Holds σ w ∨ b.Holds σ w := by
  simp only [disj,Holds,not_and_or,not_not]

def all (l : List (Predicate K)) := l.foldr Predicate.conj (.truth true)
def any (l : List (Predicate K)) := (all (l.map Predicate.neg)).neg

@[simp] theorem holds_all (σ : K → ℕ) (w : List Bool) (l : List (Predicate K)) :
    (all l).Holds σ w ↔ ∀ p∈l,p.Holds σ w := by
  induction l with
  | nil => simp [all,Holds]
  | cons p l ih =>
    change (p.Holds σ w ∧ (all l).Holds σ w) ↔ _
    simp only [ih,List.mem_cons,forall_eq_or_imp]

@[simp] theorem holds_any (σ : K → ℕ) (w : List Bool) (l : List (Predicate K)) :
    (any l).Holds σ w ↔ ∃ p∈l,p.Holds σ w := by
  classical
  simp only [any,Holds,holds_all,List.mem_map,forall_exists_index,and_imp,
    forall_apply_eq_imp_iff₂,not_forall]
  simp only [not_not]
  simp only [exists_prop]

end Predicate
end WLTime.NatCode

namespace WLTime.Compression
open NatCode

namespace ReadoutName
variable {r m : ℕ} {T : Type uT} {L : Type uL}

def encode : ReadoutName r T L (Fin m) → NameTag r T L × ℕ × ℕ
  | .horizontal i t a b => (.horizontal i t,a.val,b.val)
  | .vertical i l a => (.vertical i l,a.val,0)

 theorem encode_injective : Function.Injective (encode (r:=r) (m:=m) (T:=T) (L:=L)) := by
  intro x y h
  cases x <;> cases y <;> simp only [encode,Prod.mk.injEq,NameTag.horizontal.injEq,
    NameTag.vertical.injEq,reduceCtorEq,and_true,false_and] at h
  · rcases h with ⟨⟨rfl,rfl⟩,ha,hb⟩
    exact congrArg₂ _ (Fin.ext ha) (Fin.ext hb)
  · rcases h with ⟨⟨rfl,rfl⟩,ha⟩
    exact congrArg _ (Fin.ext ha)
end ReadoutName

structure FormalName (T : Type uT) (J : Type uJ) where
  tag : T
  first : Expr J
  second : Expr J

namespace FormalName
variable {T : Type uT} {J : Type uJ}
def eval (σ : J → ℕ) (w : List Bool) (n : FormalName T J) : T × ℕ × ℕ :=
  (n.tag,n.first.eval σ w,n.second.eval σ w)
noncomputable def equal (n u : FormalName T J) : Predicate J := by
  classical
  exact (Predicate.truth (decide (n.tag=u.tag))).conj
    ((Predicate.eq n.first u.first).conj (.eq n.second u.second))

 theorem equal_holds (σ : J → ℕ) (w : List Bool) (n u : FormalName T J) :
    (n.equal u).Holds σ w ↔ n.eval σ w=u.eval σ w := by
  simp only [equal,Predicate.Holds,decide_eq_true_eq,eval,Prod.mk.injEq]
end FormalName

namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} {J : Type uJ} (I : ConsistencyData (r+1) m P E)

abbrev BlockTag (K : ℕ) := Fin (r+1) × (TypeNode K P E ⊕ TypeLink K E)

def makeBlock (K : ℕ) : BlockTag (r:=r) (P:=P) (E:=E) K → Fin m → Fin m →
    RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K
  | (i,.inl t),a,b => .site i t a b
  | (i,.inr l),a,b => .square i l a b

def fixedTags (K : ℕ) : BlockTag (r:=r) (P:=P) (E:=E) K → List (Tag (r:=r) (P:=P) (E:=E) K)
  | (i,.inl t) => [.horizontal i t]
  | (i,.inr l) => [.horizontal i (linkLeft K I.src l),.horizontal i (linkRight K I.dst l),
      .vertical i l,.vertical (finRotate (r+1) i) l]

noncomputable def footprintList (K : ℕ) : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K →
    List (RawName (r:=r) (m:=m) (P:=P) (E:=E) K)
  | .site i t a b => [.horizontal i t a b]
  | .square i l a b => [.horizontal i (linkLeft K I.src l) a b,
      .horizontal i (linkRight K I.dst l)
        (linkMatch K (fun e => I.coordinatePerm e i) l a)
        (linkMatch K (fun e => I.coordinatePerm e (finRotate (r+1) i)) l b),
      .vertical i l a,.vertical (finRotate (r+1) i) l b]

 theorem mem_footprintList (K : ℕ) (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K)
    (n : RawName (r:=r) (m:=m) (P:=P) (E:=E) K) :
    n∈I.footprintList K b ↔ n∈I.footprint K b := by
  classical
  cases b <;> simp only [footprintList,footprint,List.mem_cons,List.not_mem_nil,or_false,
    Finset.mem_insert,Finset.mem_singleton]

 theorem footprintList_tags (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Fin m) :
    (I.footprintList K (makeBlock K t a b)).map ReadoutName.tag=I.fixedTags K t := by
  rcases t with ⟨i,t|l⟩ <;> rfl

 theorem tagSupported_iff_fixed (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K)
    (a b : Fin m) (v : I.TagValues K) :
    I.TagSupported K (makeBlock K t a b) v ↔ ∀s,s∉I.fixedTags K t → v s=0 := by
  classical
  rw [TagSupported]
  apply forall_congr'
  intro s
  rw [← I.footprintList_tags K t a b,List.mem_map]
  simp only [I.mem_footprintList,not_exists,not_and]

noncomputable def fixedForm (K : ℕ) : BlockTag (r:=r) (P:=P) (E:=E) K → I.TagValues K → F₂
  | (_,.inl _),_ => 0
  | (i,.inr l),v => I.leftForm K l (v (.horizontal i (linkLeft K I.src l))) +
      I.rightForm K l (v (.horizontal i (linkRight K I.dst l))) +
      v (.vertical i l) + v (.vertical (finRotate (r+1) i) l)

def fixedBias (K : ℕ) : BlockTag (r:=r) (P:=P) (E:=E) K → F₂
  | (_,.inl _) => 0
  | (i,.inr l) => seam i*I.linkBias K l

 theorem blockForm_fixed (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K)
    (a b : Fin m) (v : I.TagValues K) :
    I.blockForm K (makeBlock K t a b) (I.tagRead K v)=I.fixedForm K t v := by
  rcases t with ⟨i,t|l⟩ <;> rfl

 theorem blockBias_fixed (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Fin m) :
    I.blockBias K (makeBlock K t a b)=I.fixedBias K t := by
  rcases t with ⟨i,t|l⟩ <;> rfl

def FixedLegal (K : ℕ) (ε : F₂) (t : BlockTag (r:=r) (P:=P) (E:=E) K) (v : I.TagValues K) : Prop :=
  (∀s,s∉I.fixedTags K t → v s=0) ∧ I.fixedForm K t v=ε*I.fixedBias K t

 theorem descriptorValid_fixed (K : ℕ) (ε : F₂) (t : BlockTag (r:=r) (P:=P) (E:=E) K)
    (a b : Fin m) (v : I.TagValues K) :
    I.DescriptorValid K ε (makeBlock K t a b,v) ↔
      I.ValidBlock K (makeBlock K t a b) ∧ I.FixedLegal K ε t v := by
  simp only [DescriptorValid,I.tagSupported_iff_fixed,I.blockForm_fixed,I.blockBias_fixed,FixedLegal]

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression
open NatCode
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} {J : Type uJ} (I : ConsistencyData (r+1) m P E)

variable (D : E → Fin (r+1) → Expr J → Predicate J)
variable (Q : E → Fin (r+1) → Expr J → Expr J)

def labelPredicate (K : ℕ) : TypeNode K P E → Fin (r+1) → Expr J → Predicate J
  | .inl _,_,_ => .truth true
  | .inr (e,_),i,a => D e i a

def blockPredicate (K : ℕ) : BlockTag (r:=r) (P:=P) (E:=E) K → Expr J → Expr J → Predicate J
  | (i,.inl t),a,b => (labelPredicate D K t i a).conj
      (labelPredicate D K t (finRotate (r+1) i) b)
  | (i,.inr l),a,b => (D l.1 i a).conj (D l.1 (finRotate (r+1) i) b)

noncomputable def validPredicate (K : ℕ) (ε : F₂) (t : BlockTag (r:=r) (P:=P) (E:=E) K)
    (v : I.TagValues K) (a b : Expr J) : Predicate J := by
  classical
  exact (blockPredicate D K t a b).conj (.truth (decide (I.FixedLegal K ε t v)))

 theorem blockPredicate_holds (K : ℕ) (σ : J → ℕ) (w : List Bool)
    (hD : ∀ e i (c : Expr J) (x : Fin m),c.eval σ w=x.val →
      ((D e i c).Holds σ w ↔ x∈I.domain e i))
    (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Expr J) (x y : Fin m)
    (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val) :
    (blockPredicate D K t a b).Holds σ w ↔ I.ValidBlock K (makeBlock K t x y) := by
  rcases t with ⟨i,t|l⟩
  · cases t <;> simp only [blockPredicate,labelPredicate,Predicate.Holds,makeBlock,
      ValidBlock,LabelAllowed,true_and,hD _ _ a x ha,hD _ _ b y hb]
  · exact and_congr (hD _ _ a x ha) (hD _ _ b y hb)

 theorem validPredicate_holds (K : ℕ) (ε : F₂) (σ : J → ℕ) (w : List Bool)
    (hD : ∀ e i (c : Expr J) (x : Fin m),c.eval σ w=x.val →
      ((D e i c).Holds σ w ↔ x∈I.domain e i))
    (t : BlockTag (r:=r) (P:=P) (E:=E) K) (v : I.TagValues K) (a b : Expr J) (x y : Fin m)
    (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val) :
    (I.validPredicate D K ε t v a b).Holds σ w ↔ I.DescriptorValid K ε (makeBlock K t x y,v) := by
  simp only [validPredicate,Predicate.Holds,decide_eq_true_eq,
    I.blockPredicate_holds D K σ w hD t a b x y ha hb,I.descriptorValid_fixed]

def matchCode (K : ℕ) (l : TypeLink K E) (i : Fin (r+1)) (a : Expr J) : Expr J :=
  if l.2.val=4*K then Q l.1 i a else a

 theorem matchCode_eval (K : ℕ) (σ : J → ℕ) (w : List Bool)
    (hQ : ∀ e i (c : Expr J) (x : Fin m) (hx : x∈I.domain e i),c.eval σ w=x.val →
      (Q e i c).eval σ w=(I.coord e i ⟨x,hx⟩).val)
    (l : TypeLink K E) (i : Fin (r+1)) (a : Expr J) (x : Fin m)
    (hx : x∈I.domain l.1 i) (ha : a.eval σ w=x.val) :
    (matchCode Q K l i a).eval σ w=(linkMatch K (fun e => I.coordinatePerm e i) l x).val := by
  by_cases h : l.2.val=4*K
  · simp only [matchCode,ite_eq_left h,linkMatch]
    rw [I.coordinatePerm_apply l.1 i ⟨x,hx⟩]
    exact hQ _ _ a x hx ha
  · simpa only [matchCode,ite_eq_right h,linkMatch,Equiv.refl_apply] using ha

def formalFootprint (K : ℕ) : BlockTag (r:=r) (P:=P) (E:=E) K → Expr J → Expr J →
    List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J)
  | (i,.inl t),a,b => [⟨.horizontal i t,a,b⟩]
  | (i,.inr l),a,b => [⟨.horizontal i (linkLeft K I.src l),a,b⟩,
      ⟨.horizontal i (linkRight K I.dst l),matchCode Q K l i a,
        matchCode Q K l (finRotate (r+1) i) b⟩,
      ⟨.vertical i l,a,.const 0⟩,⟨.vertical (finRotate (r+1) i) l,b,.const 0⟩]

 theorem formalFootprint_correct (K : ℕ) (σ : J → ℕ) (w : List Bool)
    (hQ : ∀ e i (c : Expr J) (x : Fin m) (hx : x∈I.domain e i),c.eval σ w=x.val →
      (Q e i c).eval σ w=(I.coord e i ⟨x,hx⟩).val)
    (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Expr J) (x y : Fin m)
    (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val) (ht : I.ValidBlock K (makeBlock K t x y)) :
    (I.formalFootprint Q K t a b).map (FormalName.eval σ w)=
      (I.footprintList K (makeBlock K t x y)).map ReadoutName.encode := by
  rcases t with ⟨i,t|l⟩
  · simp only [formalFootprint,makeBlock,footprintList,List.map_cons,List.map_nil,
      FormalName.eval,ReadoutName.encode,ha,hb]
  · simp only [formalFootprint,makeBlock,footprintList,List.map_cons,List.map_nil,
      FormalName.eval,ReadoutName.encode,ha,hb,Expr.eval,
      I.matchCode_eval Q K σ w hQ l i a x ht.1 ha,
      I.matchCode_eval Q K σ w hQ l (finRotate (r+1) i) b y ht.2 hb]

noncomputable def valueCode (K : ℕ) (v : I.TagValues K) (t : Tag (r:=r) (P:=P) (E:=E) K) : ℕ :=
  (Fintype.equivFin (I.TagValue K t) (v t)).val

 theorem valueCode_eq_iff (K : ℕ) (v u : I.TagValues K)
    (n : RawName (r:=r) (m:=m) (P:=P) (E:=E) K) :
    I.valueCode K v n.tag=I.valueCode K u n.tag ↔ I.tagRead K v n=I.tagRead K u n := by
  rw [valueCode,valueCode,Fin.val_inj,(Fintype.equivFin _).injective.eq_iff]
  cases n <;> rfl

noncomputable def overlapPredicate (K : ℕ)
    (l s : List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J)) : Predicate J :=
  Predicate.any (l.flatMap fun n => s.map fun u => n.equal u)

noncomputable def agreePredicate (K : ℕ) (v u : I.TagValues K)
    (l s : List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J)) : Predicate J := by
  classical
  exact Predicate.all (l.flatMap fun n => s.map fun z =>
    (n.equal z).neg.disj (.truth (decide (I.valueCode K v n.tag=I.valueCode K u z.tag))))

 theorem overlapPredicate_holds (K : ℕ) (σ : J → ℕ) (w : List Bool)
    (l s : List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J)) :
    (overlapPredicate K l s).Holds σ w ↔ ∃ n∈l,∃u∈s,n.eval σ w=u.eval σ w := by
  rw [overlapPredicate,Predicate.holds_any]
  constructor
  · rintro ⟨p,hp,h⟩
    obtain ⟨a,ha,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
    exact ⟨a,ha,b,hb,(FormalName.equal_holds σ w a b).mp h⟩
  · rintro ⟨a,ha,b,hb,h⟩
    exact ⟨a.equal b,List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩,
      (FormalName.equal_holds σ w a b).mpr h⟩

 theorem agreePredicate_holds (K : ℕ) (σ : J → ℕ) (w : List Bool) (v u : I.TagValues K)
    (l s : List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J)) :
    (I.agreePredicate K v u l s).Holds σ w ↔
      ∀ n∈l,∀z∈s,n.eval σ w=z.eval σ w → I.valueCode K v n.tag=I.valueCode K u z.tag := by
  classical
  rw [agreePredicate,Predicate.holds_all]
  constructor
  · intro h n hn z hz
    have hh := h _ (List.mem_flatMap.mpr ⟨n,hn,List.mem_map.mpr ⟨z,hz,rfl⟩⟩)
    simpa only [Predicate.holds_disj,Predicate.Holds,FormalName.equal_holds,
      decide_eq_true_eq,or_iff_not_imp_left,not_not] using hh
  · intro h p hp
    obtain ⟨n,hn,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hp
    simpa only [Predicate.holds_disj,Predicate.Holds,FormalName.equal_holds,
      decide_eq_true_eq,or_iff_not_imp_left,not_not] using h n hn z hz

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression
open NatCode
namespace ReadoutName
variable {r m : ℕ} {T : Type uT} {L : Type uL}
@[simp] theorem encode_tag (n : ReadoutName r T L (Fin m)) : n.encode.1=n.tag := by cases n <;> rfl
end ReadoutName

namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} {J : Type uJ} (I : ConsistencyData (r+1) m P E)

 theorem overlapPredicate_correct (K : ℕ) (σ : J → ℕ) (w : List Bool)
    (l s : List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J))
    (L S : List (RawName (r:=r) (m:=m) (P:=P) (E:=E) K))
    (hL : l.map (FormalName.eval σ w)=L.map ReadoutName.encode)
    (hS : s.map (FormalName.eval σ w)=S.map ReadoutName.encode) :
    (overlapPredicate K l s).Holds σ w ↔ ∃n,n∈L ∧ n∈S := by
  rw [overlapPredicate_holds]
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    have hh : FormalName.eval σ w a ∈ l.map (FormalName.eval σ w) := List.mem_map.mpr ⟨a,ha,rfl⟩
    rw [hL] at hh
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hh
    have hh : FormalName.eval σ w b ∈ s.map (FormalName.eval σ w) := List.mem_map.mpr ⟨b,hb,rfl⟩
    rw [hS] at hh
    obtain ⟨y,hy,hf⟩ := List.mem_map.mp hh
    have hxy : x=y := ReadoutName.encode_injective (he.trans (hab.trans hf.symm))
    exact ⟨x,hx,hxy.symm ▸ hy⟩
  · rintro ⟨x,hx,hy⟩
    have hh : x.encode ∈ L.map ReadoutName.encode := List.mem_map.mpr ⟨x,hx,rfl⟩
    rw [← hL] at hh
    obtain ⟨a,ha,he⟩ := List.mem_map.mp hh
    have hh : x.encode ∈ S.map ReadoutName.encode := List.mem_map.mpr ⟨x,hy,rfl⟩
    rw [← hS] at hh
    obtain ⟨b,hb,hf⟩ := List.mem_map.mp hh
    exact ⟨a,ha,b,hb,he.trans hf.symm⟩

 theorem agreePredicate_correct (K : ℕ) (σ : J → ℕ) (w : List Bool) (v u : I.TagValues K)
    (l s : List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J))
    (L S : List (RawName (r:=r) (m:=m) (P:=P) (E:=E) K))
    (hL : l.map (FormalName.eval σ w)=L.map ReadoutName.encode)
    (hS : s.map (FormalName.eval σ w)=S.map ReadoutName.encode) :
    (I.agreePredicate K v u l s).Holds σ w ↔ ∀ n∈L,n∈S → I.tagRead K v n=I.tagRead K u n := by
  rw [I.agreePredicate_holds]
  constructor
  · intro h n hn hm
    have hh : n.encode ∈ L.map ReadoutName.encode := List.mem_map.mpr ⟨n,hn,rfl⟩
    rw [← hL] at hh
    obtain ⟨a,ha,he⟩ := List.mem_map.mp hh
    have hh : n.encode ∈ S.map ReadoutName.encode := List.mem_map.mpr ⟨n,hm,rfl⟩
    rw [← hS] at hh
    obtain ⟨b,hb,hf⟩ := List.mem_map.mp hh
    have hab := h a ha b hb (he.trans hf.symm)
    have het : a.tag=n.tag := by simpa only [FormalName.eval,ReadoutName.encode_tag] using congrArg Prod.fst he
    have hft : b.tag=n.tag := by simpa only [FormalName.eval,ReadoutName.encode_tag] using congrArg Prod.fst hf
    rw [het,hft] at hab
    exact (I.valueCode_eq_iff K v u n).mp hab
  · intro h a ha b hb hab
    have hh : FormalName.eval σ w a ∈ l.map (FormalName.eval σ w) := List.mem_map.mpr ⟨a,ha,rfl⟩
    rw [hL] at hh
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hh
    have hh : FormalName.eval σ w b ∈ s.map (FormalName.eval σ w) := List.mem_map.mpr ⟨b,hb,rfl⟩
    rw [hS] at hh
    obtain ⟨y,hy,hf⟩ := List.mem_map.mp hh
    have hxy : x=y := ReadoutName.encode_injective (he.trans (hab.trans hf.symm))
    subst y
    have het : a.tag=x.tag := by simpa only [FormalName.eval,ReadoutName.encode_tag] using (congrArg Prod.fst he).symm
    have hft : b.tag=x.tag := by simpa only [FormalName.eval,ReadoutName.encode_tag] using (congrArg Prod.fst hf).symm
    rw [het,hft]
    exact (I.valueCode_eq_iff K v u x).mpr (h x hx hy)

 theorem makeBlock_eq_iff (K : ℕ) (t u : BlockTag (r:=r) (P:=P) (E:=E) K)
    (a b c d : Fin m) : makeBlock K t a b=makeBlock K u c d ↔ t=u ∧ a=c ∧ b=d := by
  rcases t with ⟨i,t|l⟩ <;> rcases u with ⟨j,u|s⟩ <;>
    simp only [makeBlock,BlockName.site.injEq,BlockName.square.injEq,Prod.mk.injEq,
      Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq] <;> tauto

noncomputable def sameBlockPredicate (K : ℕ) (t u : BlockTag (r:=r) (P:=P) (E:=E) K)
    (a b c d : Expr J) : Predicate J := by
  classical
  exact (Predicate.truth (decide (t=u))).conj ((Predicate.eq a c).conj (.eq b d))

 theorem sameBlockPredicate_holds (K : ℕ) (σ : J → ℕ) (w : List Bool)
    (t u : BlockTag (r:=r) (P:=P) (E:=E) K) (a b c d : Expr J) (x y z v : Fin m)
    (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val)
    (hc : c.eval σ w=z.val) (hd : d.eval σ w=v.val) :
    (sameBlockPredicate K t u a b c d).Holds σ w ↔ makeBlock K t x y=makeBlock K u z v := by
  simp only [sameBlockPredicate,Predicate.Holds,decide_eq_true_eq,ha,hb,hc,hd,
    Fin.val_inj,makeBlock_eq_iff]

def RawAdjacent (K : ℕ) (v u : I.Descriptor K) : Prop :=
  v.1≠u.1 ∧ (∃n,n∈I.footprint K v.1 ∧ n∈I.footprint K u.1) ∧
    ∀n∈I.footprint K v.1,n∈I.footprint K u.1 → I.tagRead K v.2 n=I.tagRead K u.2 n

 theorem descriptor_adjacent (K : ℕ) (hK : 0<K) (hr : 1≤r) (ε : F₂)
    (v u : {v : I.Descriptor K // I.DescriptorValid K ε v}) :
    (I.valuationGraph K ε).Adj (I.descriptorEquiv K hK hr ε v) (I.descriptorEquiv K hK hr ε u) ↔
      I.RawAdjacent K v.val u.val := by
  classical
  change (_≠_ ∧ _ ∧ _) ↔ (_≠_ ∧ _ ∧ _)
  apply and_congr
  · apply not_congr
    change (⟨v.val.1,_⟩ : I.Block K) = ⟨u.val.1,_⟩ ↔ v.val.1=u.val.1
    simp only [Subtype.mk.injEq]
  · apply and_congr
    · change (I.footprint K v.val.1 ∩ I.footprint K u.val.1).Nonempty ↔ _
      simp only [Finset.Nonempty,Finset.mem_inter]
    · change (∀n∈I.footprint K v.val.1,n∈I.footprint K u.val.1 →
        (I.atBlock K v.val.1 (I.tagRead K v.val.2)).val n=
        (I.atBlock K u.val.1 (I.tagRead K u.val.2)).val n) ↔ _
      constructor
      · intro h n hn hm
        have he := h n hn hm
        rwa [I.atBlock_apply K _ _ n hn,I.atBlock_apply K _ _ n hm] at he
      · intro h n hn hm
        rw [I.atBlock_apply K _ _ n hn,I.atBlock_apply K _ _ n hm]
        exact h n hn hm

noncomputable def adjacencyPredicate (Q : E → Fin (r+1) → Expr J → Expr J) (K : ℕ)
    (t u : BlockTag (r:=r) (P:=P) (E:=E) K) (v z : I.TagValues K)
    (a b c d : Expr J) : Predicate J :=
  (sameBlockPredicate K t u a b c d).neg.conj
    ((overlapPredicate K (I.formalFootprint Q K t a b) (I.formalFootprint Q K u c d)).conj
      (I.agreePredicate K v z (I.formalFootprint Q K t a b) (I.formalFootprint Q K u c d)))

 theorem adjacencyPredicate_correct (Q : E → Fin (r+1) → Expr J → Expr J) (K : ℕ)
    (σ : J → ℕ) (w : List Bool)
    (hQ : ∀e i (a : Expr J) (x : Fin m) (hx : x∈I.domain e i),a.eval σ w=x.val →
      (Q e i a).eval σ w=(I.coord e i ⟨x,hx⟩).val)
    (t u : BlockTag (r:=r) (P:=P) (E:=E) K) (v z : I.TagValues K)
    (a b c d : Expr J) (x y p q : Fin m)
    (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val)
    (hc : c.eval σ w=p.val) (hd : d.eval σ w=q.val)
    (ht : I.ValidBlock K (makeBlock K t x y)) (hu : I.ValidBlock K (makeBlock K u p q)) :
    (I.adjacencyPredicate Q K t u v z a b c d).Holds σ w ↔
      I.RawAdjacent K (makeBlock K t x y,v) (makeBlock K u p q,z) := by
  have hl := I.formalFootprint_correct Q K σ w hQ t a b x y ha hb ht
  have hs := I.formalFootprint_correct Q K σ w hQ u c d p q hc hd hu
  simp only [adjacencyPredicate,Predicate.Holds,sameBlockPredicate_holds K σ w t u a b c d x y p q ha hb hc hd,
    overlapPredicate_correct K σ w _ _ _ _ hl hs,I.agreePredicate_correct K σ w v z _ _ _ _ hl hs,
    RawAdjacent,I.mem_footprintList]

end ConsistencyData
end WLTime.Compression

end OAI
