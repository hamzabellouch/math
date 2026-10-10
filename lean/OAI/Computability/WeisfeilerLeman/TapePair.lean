import OAI.Computability.WeisfeilerLeman.MatrixBounds

namespace OAI

universe uK uA uB uL uS uT

namespace WLTime.OneTape.Symbolic
open NatCode TypedStack UnaryPrograms
open scoped Classical
variable (M : OneTape) (d q : ℕ)
namespace FullWriter
inductive Reg where
  | word | len | order | output
  deriving DecidableEq
instance : Fintype Reg := ⟨{.word,.len,.order,.output},by intro r; cases r <;> simp⟩

def args (m n : ℕ) : Bool → ℕ := fun b => if b then n else m
def N : Expr Bool := .var false
noncomputable def R : Expr Bool := .binary .mul (.const (coefficient M d q (d+q+2))) (.binary .mul N N)
noncomputable def E : Expr Bool := .binary .add (R M d q) (.const 1)
noncomputable def L : Expr Bool := .binary .add (.binary .mul (E M d q) (E M d q)) (.const 1)
noncomputable def B : Expr Bool := .binary .add (.const 1) (.binary .mul (R M d q) (L M d q))
noncomputable def P : Expr Bool := .binary .sub (.var true) (B M d q)
noncomputable def body : Writer Bool := pairWriter M d q N (L M d q) (P M d q)
def rho : Bool → Reg := fun b => if b then .order else .len
noncomputable def program (n : ℕ) : Program Reg :=
  .seqShared (.countLength .word .len)
    (.seqShared (.loadNat .order n)
      (.seqShared (.pushes .output (encodeNat n).reverse)
        ((body M d q).compile rho .word .output)))

 theorem eval_N (m n : ℕ) (w : List Bool) : N.eval (args m n) w=m := rfl
 theorem eval_L (n : ℕ) (w : List Bool) : (L M d q).eval (args w.length n) w=
    (instanceData M d q w).slotLimit (d+q+2) := by
  simp only [L,E,R,N,Expr.eval,Binary.eval,args,Bool.false_eq_true,ite_false]
  change _=(coefficient M d q (d+q+2)*w.length^2+1)^2+1
  ring_nf
 theorem eval_B (m n : ℕ) (w : List Bool) : (B M d q).eval (args m n) w=baseOrder M d q m := by
  simp only [B,L,E,R,N,Expr.eval,Binary.eval,args,Bool.false_eq_true,ite_false,baseOrder]
  ring_nf
 theorem eval_P (m n : ℕ) (w : List Bool) : (P M d q).eval (args m n) w=n-baseOrder M d q m := by
  change n-(B M d q).eval (args m n) w=_
  rw [eval_B]

 theorem safe (n : ℕ) (w : List Bool) (hm : 1≤w.length) :
    (body M d q).Safe (args w.length n) w (6*(coefficient M d q (d+q+2)+n+w.length+2)^27) := by
  let Q := coefficient M d q (d+q+2)+n+w.length+2
  have hQ : 2≤Q := by dsimp [Q]; omega
  have hat : ∀e∈([N,L M d q,P M d q] : List (Expr Bool)),e.AtomsBounded (args w.length n) Q := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl <;>
      simp only [N,L,E,R,P,B,Expr.AtomsBounded,args,Bool.false_eq_true,ite_false,ite_true] <;>
      dsimp [Q] <;> omega
  have hB (e : Expr Bool) (he : e∈[N,L M d q,P M d q]) (hd : e.degree≤27) :
      e.Bounded (args w.length n) w (Q^27) :=
    e.bounded_mono _ _ (e.bounded_degree _ _ Q hQ (hat e he))
      (Nat.pow_le_pow_right (by omega) hd)
  apply pairWriter_safe M d q N (L M d q) (P M d q) (args w.length n) w (Q^27) hm
    (eval_N _ _ _) (eval_L M d q n w)
  · exact hB N (by simp) (by decide)
  · exact hB _ (by simp) (by simp only [L,E,R,N,Expr.degree]; decide)
  · exact hB _ (by simp) (by simp only [P,B,L,E,R,N,Expr.degree]; decide)
  · have hCQ : coefficient M d q (d+q+2)≤Q := by dsimp [Q]; omega
    exact hCQ.trans (Nat.le_self_pow (by omega) Q)

noncomputable def budget (n m : ℕ) : ℕ :=
  17*m+3+24*((Nat.digits 2 n).length+1)*(n+1)+(2*(encodeNat n).length+1)+
    (body M d q).charge*(6*(coefficient M d q (d+q+2)+n+m+2)^27+1)^8

 theorem correct (n : ℕ) (w : List Bool) (hm : 1≤w.length) (hr : 2≤d+q)
    (hn : baseOrder M d q w.length≤n) :
    ∃t≤budget M d q n w.length,∃out,
      (program M d q n).Exec (fun r => if r=Reg.word then w else []) t out ∧
      out .output=(encodePair
        (pairGraph M d q hr w (n-baseOrder M d q w.length) 0)
        (pairGraph M d q hr w (n-baseOrder M d q w.length) 1)).reverse := by
  let s : Stacks Reg Bool := fun r => if r=Reg.word then w else []
  let s1 := Function.update s Reg.len (numeral w.length)
  let s2 := Function.update s1 Reg.order (numeral n)
  let s3 := Function.update s2 Reg.output (encodeNat n).reverse
  have hcount : (Program.countLength Reg.word Reg.len).Exec s (17*w.length+3) s1 := by
    simpa [s,s1] using Program.countLength_exec Reg.word Reg.len s
  obtain ⟨t,ht,hload⟩ := Program.loadNat_exec Reg.order n s1 (by simp [s1,s])
  have hpush : (Program.pushes Reg.output (encodeNat n).reverse).Exec s2 (2*(encodeNat n).length+1) s3 := by
    simpa [s3,s2,s1,s] using Program.pushes_exec Reg.output (encodeNat n).reverse s2
  have hQ : w.length≤6*(coefficient M d q (d+q+2)+n+w.length+2)^27 := by
    have hmQ : w.length≤coefficient M d q (d+q+2)+n+w.length+2 := by omega
    have hp := Nat.le_self_pow (by decide : 27≠0) (coefficient M d q (d+q+2)+n+w.length+2)
    omega
  obtain ⟨v,hv,hbody⟩ := (body M d q).compile_exec rho Reg.word Reg.output (by decide)
    (by intro b; cases b <;> decide) (args w.length n) w _ (safe M d q n w hm) hQ s3
    (by intro b; cases b <;> simp [s3,s2,s1,s,rho,args]) (by simp [s3,s2,s1,s])
  have hd := pairWriter_depth M d q N (L M d q) (P M d q)
  have hv' : v≤(body M d q).charge*(6*(coefficient M d q (d+q+2)+n+w.length+2)^27+1)^8 :=
    hv.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by change (pairWriter M d q N (L M d q) (P M d q)).depth+2≤8; omega)))
  have he := Program.seqShared_exec hcount (Program.seqShared_exec hload (Program.seqShared_exec hpush hbody))
  refine ⟨_,?_,_,he,?_⟩
  · dsimp [budget]; omega
  · simp only [Function.update_self]
    have hlen : (listing M d q (d+q+2) w (n-baseOrder M d q w.length)).items.length=n := by
      rw [listing_length,Nat.add_sub_of_le hn]
    have hb := pairWriter_eval M d q N (L M d q) (P M d q) hr (args w.length n) w
      (n-baseOrder M d q w.length) (eval_N _ _ _) (eval_L M d q n w) (eval_P M d q _ _ _)
    change ((body M d q).eval (args w.length n) w).reverse++(s3 Reg.output) = _
    rw [show (body M d q).eval (args w.length n) w=_ from hb]
    simp only [s3,Function.update_self,encodePair,hlen,List.reverse_append,List.append_assoc]
end FullWriter
end WLTime.OneTape.Symbolic

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} {B : Type uB} [DecidableEq K]
def mapLetters (f : A → B) (g : B → A) : Code K A → Code K B
  | .skip => .skip
  | .push k x => .push k (f x)
  | .pushDyn k h => .pushDyn k (fun v => f (h (fun k => (v k).map g)))
  | .pop k => .pop k
  | .seq p q => .seq (p.mapLetters f g) (q.mapLetters f g)
  | .branch test p q => .branch (fun v => test (fun k => (v k).map g)) (p.mapLetters f g) (q.mapLetters f g)
  | .loop test p => .loop (fun v => test (fun k => (v k).map g)) (p.mapLetters f g)
 def listMap (f : A → B) (s : Stacks K A) : Stacks K B := fun k => (s k).map f
 theorem listMap_update (f : A → B) (s : Stacks K A) (k : K) (xs : List A) :
    listMap f (Function.update s k xs)=Function.update (listMap f s) k (xs.map f) := by
  funext j; by_cases h : j=k
  · subst j; simp only [listMap,Function.update_self]
  · simp only [listMap,Function.update_of_ne h]
 omit [DecidableEq K] in
 theorem unmap_tops (f : A → B) (g : B → A) (h : Function.LeftInverse g f) (s : Stacks K A) :
    (fun k => (tops (listMap f s) k).map g)=tops s := by
  funext k
  cases hs : s k with
  | nil => simp only [tops,listMap,hs,List.map_nil,List.head?_nil,Option.map_none]
  | cons x xs => simp only [tops,listMap,hs,List.map_cons,List.head?_cons,Option.map_some,h x]
 theorem mapLetters_exec (f : A → B) (g : B → A) (h : Function.LeftInverse g f)
    {c : Code K A} {s t out} (hc : c.Exec s t out) :
    (c.mapLetters f g).Exec (listMap f s) t (listMap f out) := by
  induction hc with
  | skip s => exact .skip _
  | push s k x => simpa only [mapLetters,listMap_update,List.map_cons,listMap] using Exec.push (listMap f s) k (f x)
  | pushDyn s k hh =>
    simpa only [mapLetters,listMap_update,List.map_cons,unmap_tops f g h,listMap] using
      Exec.pushDyn (listMap f s) k (fun v => f (hh (fun k => (v k).map g)))
  | pop s k => simpa only [mapLetters,listMap_update,List.map_tail,listMap] using Exec.pop (listMap f s) k
  | seq ha hb ia ib => exact .seq ia ib
  | branch_true ht he ih => exact .branch_true (by simpa only [unmap_tops f g h] using ht) ih
  | branch_false ht he ih => exact .branch_false (by simpa only [unmap_tops f g h] using ht) ih
  | loop_false ht => exact .loop_false (by simpa only [unmap_tops f g h] using ht)
  | loop_true ht he hr ie ir => exact .loop_true (by simpa only [unmap_tops f g h] using ht) ie ir
 omit [DecidableEq K] in
 @[simp] theorem mapLetters_size (p : Code K A) (f : A → B) (g : B → A) :
    (p.mapLetters f g).controlSize=p.controlSize := by induction p <;> simp_all [mapLetters,controlSize]
end WLTime.TypedStack.Code

namespace WLTime.TypedStack.Command
variable {K : Type uK} {L : Type uL} {A : Type uA} {S : Type uS} {T : Type uT}
def transport (f : K → L) (g : S → T) (answer : Bool → Bool) : Command K A S → Command L A T
  | .next q => .next (g q)
  | .push k x q => .push (f k) x (g q)
  | .pop k q => .pop (f k) (g q)
  | .halt b => .halt (answer b)
end WLTime.TypedStack.Command

namespace WLTime.TypedStack.Execution
variable {K : Type uK} {L : Type uL} {A : Type uA} {S : Type uS} {T : Type uT} [DecidableEq K] [DecidableEq L]
 theorem transport {tr : S → Tops K A → Command K A S} {tr' : T → Tops L A → Command L A T}
    (f : K → L) (hf : Function.Injective f) (g : S → T) (answer : Bool → Bool)
    (htr : ∀ q v,tr' (g q) v=Command.transport f g answer (tr q (v ∘ f)))
    {q s t b out} (h : Execution tr q s t b out) (frame : Stacks L A) :
    Execution tr' (g q) (Code.liftStacks f frame s) t (answer b) (Code.liftStacks f frame out) := by
  induction h with
  | halt h => exact .halt (by rw [htr,Code.liftStacks_tops f hf,h]; rfl)
  | next h ht ih => exact .next (by rw [htr,Code.liftStacks_tops f hf,h]; rfl) ih
  | @push q s k x q' t b out h ht ih =>
    rw [Code.liftStacks_update f hf] at ih
    exact .push (by rw [htr,Code.liftStacks_tops f hf,h]; rfl)
      (by simpa only [Code.liftStacks_apply f hf] using ih)
  | @pop q s k q' t b out h ht ih =>
    rw [Code.liftStacks_update f hf] at ih
    exact .pop (by rw [htr,Code.liftStacks_tops f hf,h]; rfl)
      (by simpa only [Code.liftStacks_apply f hf] using ih)
 theorem transport_inr {tr : S → Tops K A → Command K A S} {tr' : T → Tops (L ⊕ K) A → Command (L ⊕ K) A T}
    (g : S → T) (answer : Bool → Bool)
    (htr : ∀ q v,tr' (g q) v=Command.transport Sum.inr g answer (tr q (v ∘ Sum.inr)))
    {q s t b out} (h : Execution tr q s t b out) (frame : Stacks L A) :
    Execution tr' (g q) (Sum.elim frame s) t (answer b) (Sum.elim frame out) := by
  have hi (s : Stacks K A) : Code.liftStacks (Sum.inr : K → L ⊕ K) (Sum.elim frame s) s=Sum.elim frame s := by
    funext j; cases j with
    | inl l => simp only [Code.liftStacks,dite_eq_right (show ¬∃ k : K,(Sum.inr k : L ⊕ K)=Sum.inl l from by rintro ⟨k,hk⟩; cases hk),Sum.elim_inl]
    | inr k => exact Code.liftStacks_apply _ Sum.inr_injective _ _ k
  have ho : Code.liftStacks (Sum.inr : K → L ⊕ K) (Sum.elim frame s) out=Sum.elim frame out := by
    funext j; cases j with
    | inl l => simp only [Code.liftStacks,dite_eq_right (show ¬∃ k : K,(Sum.inr k : L ⊕ K)=Sum.inl l from by rintro ⟨k,hk⟩; cases hk),Sum.elim_inl]
    | inr k => exact Code.liftStacks_apply _ Sum.inr_injective _ _ k
  simpa only [hi,ho] using h.transport Sum.inr Sum.inr_injective g answer htr (Sum.elim frame s)
end WLTime.TypedStack.Execution

namespace WLTime.TypedStack.Code
variable {K : Type uK} {L : Type uL} {A : Type uA} [DecidableEq K] [DecidableEq L]
theorem relabel_inl_exec {c : Code K A} {s t out} (h : c.Exec s t out) (e : L → List A) :
    (c.relabel (Sum.inl : K → K ⊕ L)).Exec (Sum.elim s e) t (Sum.elim out e) := by
  apply relabel_exec_of_maps _ Sum.inl_injective h
  · intro k; rfl
  · intro k; rfl
  · intro k hk; cases k with
    | inl k => exact False.elim (hk k rfl)
    | inr k => rfl
end WLTime.TypedStack.Code

namespace WLTime.TapePair
variable {A : Type uA}
structure Tape (A : Type uA) where
  left : List A
  right : List A
  deriving DecidableEq

 def contents (blank : A) (s : Tape A) (z : ℤ) : A :=
  if z<0 then s.left.getD (-z-1).toNat blank else s.right.getD z.toNat blank

 def moveWrite (blank x : A) (d : Move) (s : Tape A) : Tape A := match d with
  | .stay => ⟨s.left,x::s.right.tail⟩
  | .right => ⟨x::s.left,s.right.tail⟩
  | .left => ⟨s.left.tail,s.left.headD blank::x::s.right.tail⟩

 theorem getD_tail (s : List A) (n : ℕ) (blank : A) :
    s.tail.getD n blank=s.getD (n+1) blank := by cases s <;> rfl

 theorem getD_nonneg (s : List A) (z : ℤ) (hz : 0 ≤ z) (blank : A) :
    s.getD z.toNat blank=if z=0 then s.headD blank else s.tail.getD (z-1).toNat blank := by
  by_cases h0 : z=0
  · subst z; cases s <;> rfl
  · rw [ite_eq_right h0,getD_tail]
    congr 1
    omega

theorem contents_moveWrite (blank x : A) (d : Move) (s : Tape A) (z : ℤ) :
    contents blank (moveWrite blank x d s) z =
      if z+d.displacement=0 then x else contents blank s (z+d.displacement) := by
  cases d with
  | stay =>
    simp only [Move.displacement,add_zero,moveWrite,contents]
    by_cases hz : z<0
    · have h0 : z≠0 := by omega
      simp only [hz,ite_true,h0,ite_false]
    · by_cases h0 : z=0
      · subst z; simp
      · have he : z.toNat=(z-1).toNat+1 := by omega
        simp only [hz,ite_false,h0,he,List.getD_cons_succ,getD_tail]
  | right =>
    simp only [Move.displacement,moveWrite,contents]
    by_cases hz : z<0
    · by_cases he : z+1=0
      · have hz' : (-z-1).toNat=0 := by omega
        simp only [hz,ite_true,he,hz',List.getD_cons_zero]
      · have hz' : z+1<0 := by omega
        have ht : (-z-1).toNat=(-(z+1)-1).toNat+1 := by omega
        simp only [hz,ite_true,he,ite_false,hz',ht,List.getD_cons_succ]
    · have hz' : ¬z+1<0 := by omega
      have he : z+1≠0 := by omega
      have ht : (z+1).toNat=z.toNat+1 := by omega
      simp only [hz,ite_false,he,hz',getD_tail,ht]
  | left =>
    simp only [Move.displacement,moveWrite,contents]
    by_cases hz : z<0
    · have hz' : z+ -1<0 := by omega
      have he : z+ -1≠0 := by omega
      have ht : (-(z+ -1)-1).toNat=(-z-1).toNat+1 := by omega
      simp only [hz,ite_true,he,ite_false,hz',getD_tail,ht]
    · by_cases h0 : z=0
      · subst z
        cases s.left <;> rfl
      · by_cases h1 : z=1
        · subst z
          simp
        · have hz' : ¬z+ -1<0 := by omega
          have he : z+ -1≠0 := by omega
          have ht : z.toNat=((z+ -1).toNat-1)+1+1 := by omega
          have hs : (z+ -1).toNat-1+1=(z+ -1).toNat := by omega
          simp only [hz,ite_false,he,hz']
          calc
            (s.left.headD blank::x::s.right.tail).getD z.toNat blank =
                s.right.tail.getD ((z+ -1).toNat-1) blank := by
              rw [ht,List.getD_cons_succ,List.getD_cons_succ]
            _ = s.right.getD (z+ -1).toNat blank := by rw [getD_tail,hs]

@[simp] theorem contents_zero (blank : A) (s : Tape A) : contents blank s 0=s.right.headD blank := by
  simp only [contents,show ¬(0:ℤ)<0 by omega,ite_false,Int.toNat_zero]
  cases s.right <;> rfl

end WLTime.TapePair

namespace WLTime.TMStack
open TypedStack
variable {K : Type uK} {A : Type uA} [DecidableEq K]

def store (s : K → TapePair.Tape A) : Stacks (K × Bool) A :=
  fun k => if k.2 then (s k.1).right else (s k.1).left

def single (blank : A) (k : K) (x : A) : Move → Code (K × Bool) A
  | .stay => .seq (.pop (k,true)) (.push (k,true) x)
  | .right => .seq (.pop (k,true)) (.push (k,false) x)
  | .left => .seq (.seq (.seq (.pop (k,true)) (.push (k,true) x))
      (.pushDyn (k,true) (fun v => (v (k,false)).getD blank))) (.pop (k,false))

def tapeCost : Move → ℕ
  | .left => 8
  | _ => 4

theorem single_exec (blank x : A) (k : K) (d : Move) (s : K → TapePair.Tape A) :
    (single blank k x d).Exec (store s) (tapeCost d)
      (store (Function.update s k (TapePair.moveWrite blank x d (s k)))) := by
  have hs : (k,false)≠(k,true) := by simp
  have ht (a : K) (b : Bool) (ha : a≠k) : (a,b)≠(k,true) ∧ (a,b)≠(k,false) := by
    constructor <;> intro h <;> apply ha <;> exact congrArg Prod.fst h
  cases d with
  | stay =>
    have hg := Code.Exec.seq (Code.Exec.pop (store s) (k,true))
      (Code.Exec.push _ (k,true) x)
    convert hg using 1 <;> try rfl
    funext ⟨a,b⟩
    by_cases ha : a=k
    · subst a; cases b <;> simp [store,TapePair.moveWrite,hs]
    · rcases ht a b ha with ⟨h1,h2⟩
      simp [store,TapePair.moveWrite,Function.update_of_ne ha,Function.update_of_ne h1]
  | right =>
    have hg := Code.Exec.seq (Code.Exec.pop (store s) (k,true))
      (Code.Exec.push _ (k,false) x)
    convert hg using 1 <;> try rfl
    funext ⟨a,b⟩
    by_cases ha : a=k
    · subst a; cases b <;> simp [store,TapePair.moveWrite,hs]
    · rcases ht a b ha with ⟨h1,h2⟩
      simp [store,TapePair.moveWrite,Function.update_of_ne ha,Function.update_of_ne h1,
        Function.update_of_ne h2]
  | left =>
    have hg := Code.Exec.seq (Code.Exec.seq (Code.Exec.seq (Code.Exec.pop (store s) (k,true))
      (Code.Exec.push _ (k,true) x))
      (Code.Exec.pushDyn _ (k,true) (fun v => (v (k,false)).getD blank)))
      (Code.Exec.pop _ (k,false))
    convert hg using 1 <;> try rfl
    funext ⟨a,b⟩
    by_cases ha : a=k
    · subst a; cases b <;> simp [store,TapePair.moveWrite,tops,hs,List.headD]
      cases (s k).left <;> rfl
    · rcases ht a b ha with ⟨h1,h2⟩
      simp [store,TapePair.moveWrite,Function.update_of_ne ha,Function.update_of_ne h1,
        Function.update_of_ne h2]

def body (blank : A) (w : K → A) (d : K → Move) : List K → Code (K × Bool) A
  | [] => .skip
  | k::ks => .seq (single blank k (w k) (d k)) (body blank w d ks)

def bodyCost (d : K → Move) (ks : List K) := (ks.map (tapeCost ∘ d)).sum+1

omit [DecidableEq K] in
theorem bodyCost_le (d : K → Move) (ks : List K) : bodyCost d ks ≤ 8*ks.length+1 := by
  have hh (k : K) : tapeCost (d k) ≤ 8 := by cases d k <;> decide
  induction ks with
  | nil => simp [bodyCost]
  | cons k ks ih =>
    simp only [bodyCost,List.map_cons,List.sum_cons,List.length_cons,Function.comp_apply] at *
    have := hh k
    omega

theorem body_exec (blank : A) (w : K → A) (d : K → Move) (ks : List K) (s : K → TapePair.Tape A)
    (hn : ks.Nodup) :
    (body blank w d ks).Exec (store s) (bodyCost d ks)
      (store (fun k => if k∈ks then TapePair.moveWrite blank (w k) (d k) (s k) else s k)) := by
  induction ks generalizing s with
  | nil => simpa [body,bodyCost] using Code.Exec.skip (store s)
  | cons k ks ih =>
    have he := Code.Exec.seq (single_exec blank (w k) k (d k) s)
      (ih (Function.update s k (TapePair.moveWrite blank (w k) (d k) (s k))) hn.of_cons)
    convert he using 1 <;> try rfl
    congr 1
    funext a
    by_cases ha : a=k
    · subst a
      have hm := List.nodup_cons.mp hn |>.1
      simp [hm]
    · simp [ha]

end WLTime.TMStack

namespace WLTime.TMStack
open TypedStack
variable (M : TM)

def blank : Fin M.symbols := ⟨0,by have := M.symbols_ge; omega⟩
instance moveFintype : Fintype Move := ⟨{.left,.stay,.right},by intro d; cases d <;> simp⟩

abbrev Payload := Fin M.states × (Fin M.tapes → Fin M.symbols) × (Fin M.tapes → Move)
def stepCode (p : Payload M) : Code (Fin M.tapes × Bool) (Fin M.symbols) :=
  body (blank M) p.2.1 p.2.2 (List.finRange M.tapes)
abbrev State := Fin M.states ⊕ (p : Payload M) × (stepCode M p).State
noncomputable instance : Fintype (State M) := inferInstanceAs
  (Fintype (Fin M.states ⊕ (p : Payload M) × (stepCode M p).State))

def transition : State M → Tops (Fin M.tapes × Bool) (Fin M.symbols) →
    Command (Fin M.tapes × Bool) (Fin M.symbols) (State M)
  | .inl q,v => if q.val=1 then .halt true else if q.val=2 then .halt false else
      let p := M.transition q (fun a => (v (a,true)).getD (blank M))
      .next (.inr ⟨p,(stepCode M p).entry⟩)
  | .inr ⟨p,q⟩,v => Command.redirect (fun r => .inr ⟨p,r⟩) (.inl p.1)
      ((stepCode M p).transition q v)

def machine : Machine (Fin M.tapes × Bool) (Fin M.symbols) (State M) where
  inputStack := (⟨0,M.tapes_pos⟩,true)
  inputLetter := M.symbol
  initial := .inl ⟨0,by have := M.states_ge; omega⟩
  transition := transition M

def Relative (C : M.Config) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) : Prop :=
  ∀ a z, TapePair.contents (blank M) (s a) z = C.tape a (C.head a+z)

def nextTapes (p : Payload M) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) :=
  fun a => TapePair.moveWrite (blank M) (p.2.1 a) (p.2.2 a) (s a)

theorem stepCode_exec (p : Payload M) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) :
    (stepCode M p).Exec (store s) (bodyCost p.2.2 (List.finRange M.tapes))
      (store (nextTapes M p s)) := by
  unfold stepCode nextTapes
  simpa only [List.mem_finRange,ite_true] using
    body_exec (blank M) p.2.1 p.2.2 (List.finRange M.tapes) s (List.nodup_finRange _)

theorem observed {C : M.Config} {s : Fin M.tapes → TapePair.Tape (Fin M.symbols)}
    (h : Relative M C s) :
    (fun a => ((tops (store s)) (a,true)).getD (blank M)) = fun a => C.tape a (C.head a) := by
  funext a
  have hh := h a 0
  simp only [TapePair.contents_zero,add_zero] at hh
  exact (show (s a).right.head?.getD (blank M)=(s a).right.headD (blank M) from by
      cases (s a).right <;> rfl) |>.trans hh

theorem next_relative {C : M.Config} {s : Fin M.tapes → TapePair.Tape (Fin M.symbols)}
    (h : Relative M C s) (hh : ¬M.halted C) :
    Relative M (M.step C) (nextTapes M (M.transition C.state (fun a => C.tape a (C.head a))) s) := by
  intro a z
  simp only [nextTapes,TapePair.contents_moveWrite]
  rw [h]
  simp only [TM.step,hh,ite_false]
  simp only [add_assoc,add_eq_left]
  rw [add_comm ((M.transition C.state (fun a => C.tape a (C.head a))).2.2 a).displacement z]

end WLTime.TMStack

end OAI
