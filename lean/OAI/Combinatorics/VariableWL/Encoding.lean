import OAI.Combinatorics.VariableWL.MachineReduction

namespace OAI

namespace VariableWL.Computation.Stack
open VariableWL.BoundedSimulation
abbrev Stores (k : ℕ) := Fin (k+1) → Word
abbrev Heads (k : ℕ) := Fin (k+1) → Option Bool
abbrev Actions (k : ℕ) := Fin (k+1) → Action

def heads {k : ℕ} (s : Stores k) : Heads k := fun j => (s j).head?
def execute {k : ℕ} (a : Actions k) (s : Stores k) : Stores k := fun j => (a j).apply (s j)
def nop {k : ℕ} : Actions k := fun _ => .keep
@[simp] theorem execute_nop {k : ℕ} (s : Stores k) : execute nop s=s := rfl

inductive Code (k : ℕ) where
  | skip
  | action (a : Heads k → Actions k)
  | seq (a b : Code k)
  | branch (p : Heads k → Bool) (a b : Code k)
  | loop (p : Heads k → Bool) (body : Code k)

namespace Code
variable {k : ℕ}
def Control : Code k → Type
  | .skip => Unit
  | .action _ => Bool
  | .seq a b => a.Control ⊕ b.Control
  | .branch _ a b => Unit ⊕ (a.Control ⊕ b.Control)
  | .loop _ a => Unit ⊕ a.Control

noncomputable instance controlFintype (C : Code k) : Fintype C.Control := by
  induction C with
  | skip => exact inferInstanceAs (Fintype Unit)
  | action => exact inferInstanceAs (Fintype Bool)
  | seq a b ha hb => exact inferInstanceAs (Fintype (a.Control ⊕ b.Control))
  | branch p a b ha hb => exact inferInstanceAs (Fintype (Unit ⊕ (a.Control ⊕ b.Control)))
  | loop p a ha => exact inferInstanceAs (Fintype (Unit ⊕ a.Control))

def start : (C : Code k) → C.Control
  | .skip => ()
  | .action _ => false
  | .seq a _ => .inl a.start
  | .branch _ _ _ => .inl ()
  | .loop _ _ => .inl ()

def transition : (C : Code k) → C.Control → Heads k → Option (C.Control × Actions k)
  | .skip,_,_ => none
  | .action a,false,h => some (true,a h)
  | .action _,true,_ => none
  | .seq a b,.inl q,h =>
      match a.transition q h with
      | some (q',u) => some (.inl q',u)
      | none => some (.inr b.start,nop)
  | .seq _ b,.inr q,h => (b.transition q h).map (fun (q',u) => (.inr q',u))
  | .branch p a b,.inl _,h => some (if p h then .inr (.inl a.start) else .inr (.inr b.start),nop)
  | .branch _ a _,.inr (.inl q),h => (a.transition q h).map (fun (q',u) => (.inr (.inl q'),u))
  | .branch _ _ b,.inr (.inr q),h => (b.transition q h).map (fun (q',u) => (.inr (.inr q'),u))
  | .loop p a,.inl _,h => if p h then some (.inr a.start,nop) else none
  | .loop _ a,.inr q,h =>
      match a.transition q h with
      | some (q',u) => some (.inr q',u)
      | none => some (.inl (),nop)

def machine (C : Code k) (output : Fin (k+1)) : Machine C.Control k where
  start := C.start
  output := output
  transition := C.transition

def step (C : Code k) (s : State C.Control k) : Option (State C.Control k) :=
  (C.transition s.control (heads s.tapes)).map fun (q,a) => ⟨q,execute a s.tapes⟩

theorem machine_step (C : Code k) (o : Fin (k+1)) : (C.machine o).step=C.step := rfl

def liftState {Q R : Type} (f : Q → R) (s : State Q k) : State R k := ⟨f s.control,s.tapes⟩

theorem lift_steps {A B : Code k} (f : A.Control → B.Control)
    (hf : ∀ q h q' u, A.transition q h=some (q',u) → B.transition (f q) h=some (f q',u))
    {s t : State A.Control k} {n : ℕ} (hst : Steps A.step n s t) :
    Steps B.step n (liftState f s) (liftState f t) := by
  induction hst with
  | zero => exact Steps.zero _
  | @succ n s t u hst htu ih =>
    apply Steps.succ ?_ ih
    unfold step at hst ⊢
    cases ht : A.transition s.control (heads s.tapes) with
    | none => simp [ht] at hst
    | some data =>
      rcases data with ⟨q,a⟩
      simp only [ht,Option.map_some,Option.some.injEq] at hst
      subst t
      change (B.transition (f s.control) (heads s.tapes)).map _ = _
      rw [hf _ _ _ _ ht]
      rfl

inductive Eval : Code k → Stores k → ℕ → Stores k → Prop where
  | skip (s) : Eval .skip s 0 s
  | action (a) (s) : Eval (.action a) s 1 (execute (a (heads s)) s)
  | seq {a b s t u n m} : Eval a s n t → Eval b t m u → Eval (.seq a b) s (n+1+m) u
  | branch_true {p a b s t n} : p (heads s)=true → Eval a s n t → Eval (.branch p a b) s (n+1) t
  | branch_false {p a b s t n} : p (heads s)=false → Eval b s n t → Eval (.branch p a b) s (n+1) t
  | loop_false {p a s} : p (heads s)=false → Eval (.loop p a) s 0 s
  | loop_true {p a s t u n m} : p (heads s)=true → Eval a s n t →
      Eval (.loop p a) t m u → Eval (.loop p a) s (n+2+m) u

 theorem eval_steps {C : Code k} {s t : Stores k} {n : ℕ} (h : Eval C s n t) :
    ∃ q, Steps C.step n ⟨C.start,s⟩ ⟨q,t⟩ ∧ C.transition q (heads t)=none := by
  induction h with
  | skip s => exact ⟨(),Steps.zero _,rfl⟩
  | action a s => exact ⟨true,Steps.single rfl,rfl⟩
  | @seq a b s t u n m ha hb ia ib =>
    obtain ⟨qa,hqa,hhalt⟩ := ia
    obtain ⟨qb,hqb,hhaltb⟩ := ib
    refine ⟨.inr qb,?_,?_⟩
    · have hleft := lift_steps (B := .seq a b) Sum.inl
        (by intro q h q' v hv; simp only [transition,hv]) hqa
      have hcross : (Code.seq a b).step ⟨.inl qa,t⟩=some ⟨.inr b.start,t⟩ := by
        simp only [step,transition,hhalt,Option.map_some,execute_nop]
      have hright := lift_steps (B := .seq a b) Sum.inr
        (by intro q h q' v hv; simp only [transition,hv,Option.map_some]) hqb
      exact (hleft.tail hcross).trans hright
    · simp only [transition,hhaltb,Option.map_none]
  | @branch_true p a b s t n hp ha ih =>
    obtain ⟨q,hq,hh⟩ := ih
    refine ⟨.inr (.inl q),?_,?_⟩
    · have hbody := lift_steps (B := .branch p a b) (fun q => Sum.inr (Sum.inl q))
        (by intro q h q' u hu; simp only [transition,hu,Option.map_some]) hq
      exact hbody.head (by simp [step,start,transition,hp,liftState])
    · simp only [transition,hh,Option.map_none]
  | @branch_false p a b s t n hp ha ih =>
    obtain ⟨q,hq,hh⟩ := ih
    refine ⟨.inr (.inr q),?_,?_⟩
    · have hbody := lift_steps (B := .branch p a b) (fun q => Sum.inr (Sum.inr q))
        (by intro q h q' u hu; simp only [transition,hu,Option.map_some]) hq
      exact hbody.head (by simp [step,start,transition,hp,liftState])
    · simp only [transition,hh,Option.map_none]
  | loop_false hp => exact ⟨.inl (),Steps.zero _,by simp [transition,hp]⟩
  | @loop_true p a s t u n m hp ha hb ia ib =>
    obtain ⟨qa,hqa,hhalta⟩ := ia
    obtain ⟨qb,hqb,hhaltb⟩ := ib
    refine ⟨qb,?_,hhaltb⟩
    have hbody := lift_steps (B := .loop p a) Sum.inr
      (by intro q h q' v hv; simp only [transition,hv]) hqa
    have hin : (Code.loop p a).step ⟨.inl (),s⟩=some ⟨.inr a.start,s⟩ := by
      simp [step,transition,hp]
    have hout : (Code.loop p a).step ⟨.inr qa,t⟩=some ⟨.inl (),t⟩ := by
      simp only [step,transition,hhalta,Option.map_some,execute_nop]
    exact ((hbody.head hin).tail hout).trans hqb

 theorem eval_outputs (C : Code k) (o : Fin (k+1)) (w : Word) {t : Stores k} {n : ℕ}
    (h : Eval C (fun j => if j=0 then w.reverse else []) n t) :
    VariableWL.OutputsWithin (C.machine o).compile w (t o) (4*(w.length+n+1)) := by
  obtain ⟨q,hq,hh⟩ := eval_steps h
  apply Machine.outputs_compile
  have hr : (C.machine o).run w n=⟨q,t⟩ := by
    have he := hq.evolve
    have hrun (i) : (C.machine o).run w i=BoundedSimulation.evolve C.step ⟨C.start,fun j => if j=0 then w.reverse else []⟩ i := by
      induction i with
      | zero => rfl
      | succ i ih => change ((C.machine o).step _).getD _=_; rw [machine_step,ih]; rfl
    rw [hrun]
    exact he
  refine ⟨n,le_rfl,?_,?_⟩
  · rw [hr,machine_step]
    simp only [step,hh,Option.map_none]
  · rw [hr]
    rfl

end Code
end VariableWL.Computation.Stack

namespace VariableWL.Encoding
attribute [local instance] Classical.propDecidable

def value : Word → ℕ := List.foldr Nat.bit 0
@[simp] theorem value_bits (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n hn ih => simp [Nat.bits_append_bit _ _ hn,value] at ih ⊢; exact congrArg (Nat.bit b) ih

def header : Word → Option (ℕ × Word)
  | [] => none
  | false::w => some (0,w)
  | true::w => (header w).map fun (n,v) => (n+1,v)

theorem header_code (n : ℕ) (v : Word) : header (List.replicate n true ++ false::v)=some (n,v) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,header,ih,Option.map_some]

 theorem header_sound {w v : Word} {n : ℕ} (h : header w=some (n,v)) :
    w=List.replicate n true ++ false::v := by
  induction w generalizing n with
  | nil => cases h
  | cons b w ih =>
    cases b with
    | false => simp only [header,Option.some.injEq,Prod.mk.injEq] at h; rcases h with ⟨rfl,rfl⟩; rfl
    | true =>
      simp only [header,Option.map_eq_some_iff] at h
      obtain ⟨⟨m,u⟩,hm,he⟩ := h
      cases he
      rw [ih hm,List.replicate_succ,List.cons_append]

def integer (w : Word) : Option (ℕ × Word) :=
  match header w with
  | none => none
  | some (n,v) =>
    if n ≤ v.length then
      let bits := v.take n
      let a := value bits
      if a.bits=bits then some (a,v.drop n) else none
    else none

 theorem integer_code (n : ℕ) (v : Word) : integer (integerCode n ++ v)=some (n,v) := by
  unfold integerCode
  simp only [List.append_assoc,List.singleton_append]
  change integer (List.replicate n.bits.length true ++ false::(n.bits++v))=_
  unfold integer
  rw [header_code]
  simp only [List.length_append,Nat.le_add_right,ite_true,
    List.take_left,value_bits,List.drop_left]

 theorem integer_sound {w v : Word} {n : ℕ} (h : integer w=some (n,v)) : w=integerCode n++v := by
  unfold integer at h
  cases hh : header w with
  | none => simp [hh] at h
  | some q =>
    rcases q with ⟨m,u⟩
    simp only [hh] at h
    split_ifs at h with hm hb
    · simp only [Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      rw [header_sound hh]
      have hlen : (u.take m).length=m := List.length_take_of_le hm
      simp only [integerCode,hb,hlen,List.append_assoc,List.cons_append]
      rw [List.take_append_drop,List.nil_append]

 theorem integer_prefix_injective {n m : ℕ} {u v : Word}
    (h : integerCode n++u=integerCode m++v) : n=m ∧ u=v := by
  have he := congrArg integer h
  rw [integer_code,integer_code] at he
  exact Prod.mk.inj (Option.some.inj he)

noncomputable def matrix (G : Graph) : Word := by
  classical
  exact List.ofFn fun p : Fin (G.order*G.order) => decide (G.graph.Adj p.divNat p.modNat)

 theorem matrix_flat (G : Graph) : matrix G =
    (List.ofFn fun i : Fin G.order => List.ofFn fun j : Fin G.order => decide (G.graph.Adj i j)).flatten := by
  classical
  unfold matrix
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hn : 0 < G.order := Nat.zero_lt_of_lt i.isLt
  have hd : (⟨i.val*G.order+j.val,by have := Nat.mul_le_mul_right G.order (Nat.succ_le_of_lt i.isLt); nlinarith [j.isLt]⟩ : Fin (G.order*G.order)).divNat=i := by
    apply Fin.ext
    simp [Fin.divNat,Nat.add_div,Nat.div_eq_of_lt j.isLt,hn,Nat.mod_lt _ hn]
  have hm : (⟨i.val*G.order+j.val,by have := Nat.mul_le_mul_right G.order (Nat.succ_le_of_lt i.isLt); nlinarith [j.isLt]⟩ : Fin (G.order*G.order)).modNat=j := by
    apply Fin.ext
    simp [Fin.modNat,Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  rw [hd,hm]

 theorem graphCode_eq (G : Graph) : graphCode G=integerCode G.order++matrix G := by
  rw [matrix_flat]
  rfl

@[simp] theorem matrix_length (G : Graph) : (matrix G).length=G.order*G.order := List.length_ofFn

 theorem graph_prefix_injective {G H : Graph} {u v : Word}
    (h : graphCode G++u=graphCode H++v) : G=H ∧ u=v := by
  classical
  rw [graphCode_eq,graphCode_eq,List.append_assoc,List.append_assoc] at h
  obtain ⟨hn,ht⟩ := integer_prefix_injective h
  rcases G with ⟨n,g⟩
  rcases H with ⟨m,hg⟩
  change n=m at hn
  subst m
  obtain ⟨hm,hu⟩ := List.append_inj ht (by simp)
  refine ⟨?_,hu⟩
  have hadj : g.Adj=hg.Adj := by
    funext i j
    have hf := List.ofFn_inj.mp hm
    let p : Fin (n*n) := ⟨i.val*n+j.val,by nlinarith [i.isLt,j.isLt]⟩
    have hp := congrFun hf p
    have hn : 0<n := Nat.zero_lt_of_lt i.isLt
    have hd : p.divNat=i := by apply Fin.ext; simp [p,Fin.divNat,Nat.add_div,Nat.div_eq_of_lt j.isLt,hn,Nat.mod_lt _ hn]
    have hmod : p.modNat=j := by apply Fin.ext; simp [p,Fin.modNat,Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
    change decide (g.Adj p.divNat p.modNat)=decide (hg.Adj p.divNat p.modNat) at hp
    rw [hd,hmod] at hp
    exact propext (by simpa only [decide_eq_decide] using hp)
  have hgEq := SimpleGraph.ext hadj
  subst hg
  rfl

 theorem pair_injective {G H G' H' : Graph} {k k' : ℕ}
    (h : pairCode G H k=pairCode G' H' k') : G=G' ∧ H=H' ∧ k=k' := by
  unfold pairCode at h
  rw [List.append_assoc,List.append_assoc] at h
  obtain ⟨hg,ht⟩ := graph_prefix_injective h
  obtain ⟨hh,hk⟩ := graph_prefix_injective ht
  have hi := integer_prefix_injective (u := []) (v := []) (by simpa using hk)
  exact ⟨hg,hh,hi.1⟩

 theorem pair_mem_WL (G H : Graph) (k : ℕ) : pairCode G H k ∈ WL ↔ 2≤k ∧ Equivalent G H k := by
  constructor
  · rintro ⟨G',H',k',he,hk,hh⟩
    obtain ⟨rfl,rfl,rfl⟩ := pair_injective he
    exact ⟨hk,hh⟩
  · rintro ⟨hk,hh⟩
    exact ⟨G,H,k,rfl,hk,hh⟩

 theorem pair_mem_SubWL (G H : Graph) (k : ℕ) : pairCode G H k ∈ SubWL ↔
    2≤k ∧ 0<G.order ∧ G.order=H.order ∧ G.graph.Connected ∧ H.graph.Connected ∧
      Subcubic G ∧ Subcubic H ∧ Equivalent G H k := by
  constructor
  · rintro ⟨G',H',k',he,hh⟩
    obtain ⟨rfl,rfl,rfl⟩ := pair_injective he
    exact hh
  · intro hh
    exact ⟨G,H,k,rfl,hh⟩

end VariableWL.Encoding

namespace VariableWL.Computation.Stack
namespace Code
variable {k : ℕ}

def one (j : Fin (k+1)) (a : Action) : Actions k := fun i => if i=j then a else .keep

theorem execute_one (j : Fin (k+1)) (a : Action) (s : Stores k) :
    execute (one j a) s=Function.update s j (a.apply (s j)) := by
  funext i
  by_cases hi : i=j
  · subst i; simp [execute,one]
  · simp [execute,one,hi,Action.apply]

def push (j : Fin (k+1)) (b : Bool) : Code k := .action (fun _ => one j (.push b))
def pop (j : Fin (k+1)) : Code k := .action (fun _ => one j .pop)
def clear (j : Fin (k+1)) : Code k := .loop (fun h => (h j).isSome) (pop j)

theorem eval_push (j : Fin (k+1)) (b : Bool) (s : Stores k) :
    Eval (push j b) s 1 (Function.update s j (b::s j)) := by
  simpa only [push,execute_one,Action.apply] using Eval.action (fun _ => one j (.push b)) s

theorem eval_pop (j : Fin (k+1)) (s : Stores k) :
    Eval (pop j) s 1 (Function.update s j (s j).tail) := by
  simpa only [pop,execute_one,Action.apply] using Eval.action (fun _ => one j .pop) s

 theorem eval_clear_update (j : Fin (k+1)) (s : Stores k) (w : Word) :
    Eval (clear j) (Function.update s j w) (3*w.length) (Function.update s j []) := by
  induction w with
  | nil => exact Eval.loop_false (by simp [heads])
  | cons b w ih =>
    have hb := eval_pop j (Function.update s j (b::w))
    simp only [Function.update_self,List.tail_cons,Function.update_idem] at hb
    have he := Eval.loop_true (p := fun h => (h j).isSome) (by simp [heads]) hb ih
    convert he using 1 <;> simp [clear,List.length_cons]; omega

 theorem eval_clear (j : Fin (k+1)) (s : Stores k) :
    Eval (clear j) s (3*(s j).length) (Function.update s j []) := by
  simpa only [Function.update_eq_self] using eval_clear_update j s (s j)

def transfer (j t : Fin (k+1)) (f : Bool → Bool) : Code k :=
  .loop (fun h => (h j).isSome) (.action fun h i =>
    if i=j then .pop else if i=t then .push (f ((h j).getD false)) else .keep)

def pairStore (s : Stores k) (j t : Fin (k+1)) (w u : Word) : Stores k :=
  Function.update (Function.update s j w) t u

 theorem transfer_action (j t : Fin (k+1)) (hjt : j≠t) (f : Bool → Bool)
    (s : Stores k) (b : Bool) (w u : Word) :
    execute (fun i => if i=j then .pop else if i=t then
      .push (f (((heads (pairStore s j t (b::w) u)) j).getD false)) else .keep)
      (pairStore s j t (b::w) u) = pairStore s j t w (f b::u) := by
  funext i
  by_cases hi : i=j
  · subst i
    simp [execute,pairStore,hjt,Action.apply]
  · by_cases ht : i=t
    · subst i
      simp [execute,pairStore,heads,hjt,Ne.symm hjt,Action.apply]
    · simp [execute,pairStore,hi,ht,Action.apply]

 theorem eval_transfer_pair (j t : Fin (k+1)) (hjt : j≠t) (f : Bool → Bool)
    (s : Stores k) (w u : Word) :
    Eval (transfer j t f) (pairStore s j t w u) (3*w.length)
      (pairStore s j t [] (w.reverse.map f++u)) := by
  induction w generalizing u with
  | nil => exact Eval.loop_false (by simp [heads,pairStore,hjt])
  | cons b w ih =>
    have ha := Eval.action (fun h i => if i=j then .pop else if i=t then
      .push (f ((h j).getD false)) else .keep) (pairStore s j t (b::w) u)
    rw [transfer_action j t hjt f] at ha
    have he := Eval.loop_true (p := fun h => (h j).isSome) (by simp [heads,pairStore,hjt]) ha (ih (f b::u))
    convert he using 1 <;> simp only [transfer,List.length_cons,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      List.append_assoc,List.singleton_append]; omega

 theorem eval_transfer (j t : Fin (k+1)) (hjt : j≠t) (f : Bool → Bool) (s : Stores k) :
    Eval (transfer j t f) s (3*(s j).length)
      (pairStore s j t [] ((s j).reverse.map f++s t)) := by
  have he := eval_transfer_pair j t hjt f s (s j) (s t)
  simpa only [pairStore,Function.update_eq_self] using he

end Code
end VariableWL.Computation.Stack

end OAI
