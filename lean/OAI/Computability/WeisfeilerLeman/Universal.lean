import OAI.Computability.WeisfeilerLeman.Consumer

namespace OAI

namespace WLTime.OneTape.Symbolic.FullWriter
open TypedStack
open scoped Classical
variable (U : OneTape) (d q : ℕ) (A : TM)
noncomputable def tapesBound : ℕ := scratchBound U d q+4+2*A.tapes
noncomputable def alphabetBound : ℕ := 3+2*(A.symbols+3)^(tapesBound U d q A)
noncomputable def statesBound : ℕ := 3+14*(tapesBound U d q A+1)*(A.symbols+3)*
  (syntaxBound U d q+6+Fintype.card (TMStack.State A))*(A.symbols+3)^(tapesBound U d q A)

 theorem consumer_alphabet (n : ℕ) : (consumer U d q A n).symbols ≤ alphabetBound U d q A := by
  unfold consumer TMConsumer.oneTape
  rw [StackMachine.Machine.compile_symbols]
  change 3+2*((2+Fintype.card (Fin A.symbols))+1)^
    Fintype.card (TMConsumer.Reg A (Fin (program U d q n).scratch ⊕ Reg)) ≤ _
  simp only [Fintype.card_fin,Fintype.card_sum,card_reg,TMConsumer.Reg,Fintype.card_prod,Fintype.card_bool]
  dsimp only [alphabetBound,tapesBound]
  have hs := scratch_le U d q n
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  rw [show 2+A.symbols+1=A.symbols+3 by omega]
  apply Nat.pow_le_pow_right (by omega)
  omega

 theorem consumer_states (n : ℕ) :
    (consumer U d q A n).states ≤ statesBound U d q A*((Nat.digits 2 n).length+1) := by
  have h := StackMachine.Machine.compile_states_bound
    (TMConsumer.machine A (program U d q n).code (.inr Reg.word) (.inr Reg.output) not).compile
  change (consumer U d q A n).states ≤ 3+14*(Fintype.card (TMConsumer.Reg A (Fin (program U d q n).scratch ⊕ Reg))+1)*
    (2+Fintype.card (Fin A.symbols)+1)*
      (Fintype.card (TMConsumer.State A (program U d q n).code (.inr Reg.output))+1)*
      (2+Fintype.card (Fin A.symbols)+1)^Fintype.card (TMConsumer.Reg A (Fin (program U d q n).scratch ⊕ Reg)) at h
  rw [TMConsumer.state_card] at h
  simp only [TMConsumer.Reg,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,card_reg,Fintype.card_bool] at h
  have hK : (program U d q n).scratch+4+A.tapes*2 ≤ tapesBound U d q A := by
    dsimp [tapesBound]; have hs := scratch_le U d q n; omega
  have hq : (program U d q n).code.controlSize+5+Fintype.card (TMStack.State A)+1 ≤
      (syntaxBound U d q+6+Fintype.card (TMStack.State A))*((Nat.digits 2 n).length+1) := by
    have hs := syntax_le U d q n
    nlinarith
  simp only [TMStack.State,Fintype.card_sum,Fintype.card_fin] at hq
  have hp : (2+A.symbols+1)^((program U d q n).scratch+4+A.tapes*2) ≤ (A.symbols+3)^tapesBound U d q A := by
    rw [show 2+A.symbols+1=A.symbols+3 by omega]
    exact Nat.pow_le_pow_right (by omega) hK
  calc
    _  ≤  _ := h
    _  ≤  3+14*(tapesBound U d q A+1)*(A.symbols+3)*
      ((syntaxBound U d q+6+Fintype.card (TMStack.State A))*((Nat.digits 2 n).length+1))*(A.symbols+3)^tapesBound U d q A := by
      have ht := Nat.mul_le_mul_right (A.symbols+3) (Nat.mul_le_mul_left 14 (Nat.add_le_add_right hK 1))
      rw [show 2+A.symbols+1=A.symbols+3 by omega] at hp ⊢
      simpa only [TMStack.State,Fintype.card_sum,Fintype.card_fin] using
        Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul ht hq) hp) 3
    _  ≤  statesBound U d q A*((Nat.digits 2 n).length+1) := by
      dsimp only [statesBound]
      nlinarith
end WLTime.OneTape.Symbolic.FullWriter

namespace WLTime.Diagonal

 def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]

 def parseUnary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false::w => some (0,w)
  | true::w => do
    let (n,tail) ← parseUnary w
    pure (n+1,tail)

 theorem parseUnary_encode (n : ℕ) (w : List Bool) :
    parseUnary (unary n++w)=some (n,w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (do let (k,t) ← parseUnary (unary n++w); pure (k+1,t))=some (n+1,w)
    rw [ih]
    rfl

 def moveCode : Move → ℕ
  | .left => 0 | .stay => 1 | .right => 2
 def decodeMove : ℕ → Move
  | 0 => .left | 1 => .stay | _ => .right

 @[simp] theorem decodeMove_code (d : Move) : decodeMove (moveCode d)=d := by cases d <;> rfl
 theorem moveCode_lt (d : Move) : moveCode d<3 := by cases d <;> decide

abbrev Entry := ℕ × ℕ × ℕ
structure Raw where
  states : ℕ
  symbols : ℕ
  table : List Entry
  deriving DecidableEq

 def Raw.Valid (R : Raw) : Prop :=
  3 ≤ R.states ∧ 3 ≤ R.symbols ∧ R.table.length=R.states*R.symbols ∧
    ∀ e ∈ R.table, e.1<R.states ∧ e.2.1<R.symbols ∧ e.2.2<3

instance (R : Raw) : Decidable R.Valid := by unfold Raw.Valid; infer_instance

 def raw (M : OneTape) : Raw where
  states := M.states
  symbols := M.symbols
  table := List.ofFn fun i : Fin (M.states*M.symbols) =>
    let p := finProdFinEquiv.symm i
    let a := M.transition p.1 p.2
    (a.1.val,a.2.1.val,moveCode a.2.2)

 theorem raw_valid (M : OneTape) : (raw M).Valid := by
  refine ⟨M.states_ge,M.symbols_ge,?_,?_⟩
  · simp [raw]
  · intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact ⟨(M.transition _ _).1.isLt,(M.transition _ _).2.1.isLt,moveCode_lt _⟩

 def Raw.machine (R : Raw) (h : R.Valid) : OneTape where
  states := R.states
  symbols := R.symbols
  states_ge := h.1
  symbols_ge := h.2.1
  transition q s :=
    let i := finProdFinEquiv (q,s)
    have hi : i.val<R.table.length := by rw [h.2.2.1]; exact i.isLt
    let e := R.table[i.val]
    have he := h.2.2.2 e (List.getElem_mem hi)
    (⟨e.1,he.1⟩,⟨e.2.1,he.2.1⟩,decodeMove e.2.2)

 theorem machine_raw (M : OneTape) : (raw M).machine (raw_valid M)=M := by
  cases M with
  | mk q g hq hg tr =>
    simp only [Raw.machine,raw]
    congr 1
    funext x y
    simp only [List.getElem_ofFn,Fin.eta,decodeMove_code]
    exact congrArg (fun p : Fin q × Fin g => tr p.1 p.2)
      (finProdFinEquiv.symm_apply_apply (x,y))

 def entryBits (e : Entry) : List Bool := unary e.1++unary e.2.1++unary e.2.2
 def tableBits (es : List Entry) : List Bool := (es.map entryBits).flatten
 def Raw.bits (R : Raw) : List Bool := unary R.states++unary R.symbols++tableBits R.table

 def parseEntry (w : List Bool) : Option (Entry × List Bool) := do
  let (q,w₁) ← parseUnary w
  let (g,w₂) ← parseUnary w₁
  let (d,w₃) ← parseUnary w₂
  pure ((q,g,d),w₃)

 theorem parseEntry_encode (e : Entry) (w : List Bool) :
    parseEntry (entryBits e++w)=some (e,w) := by
  simp only [entryBits,List.append_assoc,parseEntry,parseUnary_encode,Option.bind_eq_bind,Option.bind_some,Option.pure_def]

 def parseTable : ℕ → List Bool → Option (List Entry × List Bool)
  | 0,w => some ([],w)
  | n+1,w => do
    let (e,w₁) ← parseEntry w
    let (es,w₂) ← parseTable n w₁
    pure (e::es,w₂)

 theorem parseTable_encode (es : List Entry) (w : List Bool) :
    parseTable es.length (tableBits es++w)=some (es,w) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [show tableBits (e::es)=entryBits e++tableBits es from rfl,List.append_assoc]
    change (do let (x,t) ← parseEntry (entryBits e++ (tableBits es++w))
               let (xs,r) ← parseTable es.length t
               pure (x::xs,r))=some (e::es,w)
    rw [parseEntry_encode]
    simp only [Option.pure_def,Option.bind_eq_bind,Option.bind_some]
    rw [ih]
    rfl

 def parseRaw (w : List Bool) : Option Raw := do
  let (q,w₁) ← parseUnary w
  let (g,w₂) ← parseUnary w₁
  let (tab,w₃) ← parseTable (q*g) w₂
  if w₃=[] then pure ⟨q,g,tab⟩ else none

 theorem parseRaw_bits (R : Raw) (h : R.table.length=R.states*R.symbols) :
    parseRaw R.bits=some R := by
  unfold Raw.bits
  rw [List.append_assoc]
  simp only [parseRaw,parseUnary_encode,Option.pure_def,Option.bind_eq_bind,Option.bind_some]
  rw [← h,show tableBits R.table=tableBits R.table++[] by simp,parseTable_encode]
  simp

 def decode (w : List Bool) : Option OneTape := do
  let R ← parseRaw w
  if h : R.Valid then pure (R.machine h) else none

 def description (M : OneTape) : List Bool := (raw M).bits

 theorem decode_description (M : OneTape) : decode (description M)=some M := by
  simp only [decode,description,parseRaw_bits _ (raw_valid M).2.2.1,Option.bind_eq_bind,Option.bind_some]
  rw [dite_eq_left (raw_valid M),machine_raw]
  rfl

 def designation (M : OneTape) : List Bool := unary (description M).length++description M

 def designated (w : List Bool) : Option OneTape := do
  let (n,tail) ← parseUnary w
  if n ≤ tail.length then decode (tail.take n) else none

 theorem designated_prefix (M : OneTape) (z : List Bool) :
    designated (designation M++z)=some M := by
  simp only [designated,designation,List.append_assoc,parseUnary_encode,Option.bind_eq_bind,Option.bind_some]
  rw [ite_eq_left (by simp),List.take_left,decode_description M]

 def Language (s : ℕ) (w : List Bool) : Prop :=
  ∃ M, designated w=some M ∧ ¬∃ t ≤ w.length^s,(M.toTM.run w t).state.val=1

 def Decides (D : OneTape) (s : ℕ) : Prop :=
  ∀ w, D.toTM.halts w ∧ (D.toTM.accepts w ↔ Language s w)

 theorem language_prefix (D : OneTape) (s : ℕ) (z : List Bool) :
    Language s (designation D++z) ↔
      ¬∃ t ≤ (designation D++z).length^s,
        (D.toTM.run (designation D++z) t).state.val=1 := by
  simp only [Language,designated_prefix,Option.some.injEq]
  constructor
  · rintro ⟨M,rfl,h⟩; exact h
  · intro h; exact ⟨D,rfl,h⟩

 theorem bounded_accepts_iff (D : OneTape) (w : List Bool) (B : ℕ)
    (hh : D.toTM.halts w) (ht : D.toTM.time w ≤ B) :
    (∃ t ≤ B,(D.toTM.run w t).state.val=1) ↔ D.toTM.accepts w := by
  constructor
  · rintro ⟨t,_,h⟩; exact ⟨t,h⟩
  · intro ha
    exact ⟨D.toTM.time w,ht,(D.toTM.accepts_iff_at_halt w (D.toTM.time_halted w hh)).mp ha⟩

 theorem prefix_time_lower (D : OneTape) (s : ℕ) (hD : Decides D s) (z : List Bool) :
    (designation D++z).length^s<D.toTM.time (designation D++z) := by
  by_contra hf
  have hc := (hD (designation D++z)).2.trans (language_prefix D s z)
  rw [bounded_accepts_iff D _ _ (hD _).1 (by omega)] at hc
  exact not_iff_self hc.symm

 theorem every_length (D : OneTape) (s : ℕ) (hD : Decides D s) (m : ℕ)
    (hm : (designation D).length ≤ m) :
    ∃ w : List Bool,w.length=m ∧ m^s<D.toTM.time w := by
  let z := List.replicate (m-(designation D).length) false
  have hl : (designation D++z).length=m := by
    simp only [List.length_append,List.length_replicate,z]
    omega
  exact ⟨designation D++z,hl,hl ▸ prefix_time_lower D s hD z⟩

end WLTime.Diagonal

namespace WLTime.Universal
open UnaryPrograms

def fields : List ℕ → List Bool := List.flatMap (fun n => numeral n++[false])

@[simp] theorem fields_nil : fields []=[] := rfl
@[simp] theorem fields_cons (n : ℕ) (ns : List ℕ) :
    fields (n::ns)=numeral n++false::fields ns := by
  simp only [fields,List.flatMap_cons,List.cons_append,List.nil_append,List.append_assoc]

@[simp] theorem scan_fields_cons (n : ℕ) (ns : List ℕ) :
    scan (fields (n::ns))=(n,fields ns) := by rw [fields_cons,scan_numeral]

theorem unary_tile (n : ℕ) : Diagonal.unary n=numeral n++[false] := rfl

@[simp] theorem tailField_entry (e : Diagonal.Entry) (xs : List Bool) :
    tailField^[3] (Diagonal.entryBits e++xs)=xs := by
  simp only [Function.iterate_succ_apply,Function.iterate_zero,Function.id_def,
    Diagonal.entryBits,unary_tile,List.append_assoc,List.cons_append,List.nil_append,
    tailField,scan_numeral]

theorem tailField_table_drop (es : List Diagonal.Entry) (n : ℕ) (hn : n≤es.length)
    (xs : List Bool) :
    tailField^[3*n] (Diagonal.tableBits es++xs)=Diagonal.tableBits (es.drop n)++xs := by
  induction n generalizing es with
  | zero => simp
  | succ n ih =>
    cases es with
    | nil => simp at hn
    | cons e es =>
      have hn' : n≤es.length := by simpa using hn
      rw [Nat.mul_succ,Function.iterate_add_apply]
      change tailField^[3*n] (tailField^[3] ((Diagonal.entryBits e++Diagonal.tableBits es)++xs))=_
      rw [List.append_assoc,tailField_entry,ih es hn']
      rfl

def tile (n : ℕ) : List Bool := numeral n++[false]

@[simp] theorem fields_head (ns : List ℕ) : (scan (fields ns)).1=ns.headD 0 := by
  cases ns <;> simp [scan]
@[simp] theorem fields_tail (ns : List ℕ) : (scan (fields ns)).2=fields ns.tail := by
  cases ns <;> simp [scan]

theorem fields_length_le (ns : List ℕ) (B : ℕ) (h : ∀ n∈ns,n≤B) :
    (fields ns).length≤(B+1)*ns.length := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    rw [fields_cons,List.length_append,List.length_cons,numeral_length,List.length_cons]
    have hn := h n (by simp)
    have hs := ih (fun x hx => h x (by simp [hx]))
    nlinarith

end WLTime.Universal

namespace WLTime.Universal
open TypedStack UnaryPrograms

inductive Reg
  | tab | alpha | state | left | right | base | halt | search | index | cur | write | dir | input | temp
  deriving DecidableEq

open Reg

instance : Fintype Reg := ⟨{tab,alpha,state,left,right,base,halt,search,index,cur,write,dir,input,temp},
  by intro r; cases r <;> simp⟩

def lookup : Program Reg :=
  Program.seq (Program.copy tab search) <|
  Program.seq (mulAdd state alpha index) <|
  Program.seq (Program.copy cur index) <|
  Program.seq (seek search index) <|
  Program.seq (Program.clear state) <|
  Program.seq (Program.read search state) <|
  Program.seq (Program.read search write) <|
  Program.seq (Program.read search dir) <|
  Program.seq (Program.clear search) (Program.clear index)

@[simp] theorem scan_entry (e : Diagonal.Entry) (xs : List Bool) :
    scan (Diagonal.entryBits e++xs)=(e.1,Diagonal.unary e.2.1++Diagonal.unary e.2.2++xs) := by
  simp only [Diagonal.entryBits,List.append_assoc,unary_tile,List.cons_append,List.nil_append,
    scan_numeral]

@[simp] theorem scan_unary (n : ℕ) (xs : List Bool) : scan (Diagonal.unary n++xs)=(n,xs) := by
  simp only [unary_tile,List.append_assoc,List.cons_append,List.nil_append,scan_numeral]

theorem table_at (es : List Diagonal.Entry) (i : ℕ) (hi : i<es.length) :
    tailField^[3*i] (Diagonal.tableBits es)=
      Diagonal.entryBits es[i]++Diagonal.tableBits (es.drop (i+1)) := by
  have he := tailField_table_drop es i (by omega) []
  simp only [List.append_nil] at he
  rw [he,List.drop_eq_getElem_cons hi]
  rfl

theorem lookup_exec (es : List Diagonal.Entry) (q g x : ℕ)
    (hi : q*g+x<es.length) (s : Stacks Reg Bool)
    (ht : s tab=Diagonal.tableBits es) (hg : s alpha=numeral g)
    (hq : s state=numeral q) (hx : s cur=numeral x)
    (hs : s search=[]) (hn : s index=[]) (hw : s write=[]) (hd : s dir=[]) :
    ∃ t≤(q*g+x+1)*(30*(Diagonal.tableBits es).length+30*q+30*g+30*x+100),
      lookup.Exec s t
        (Function.update (Function.update (Function.update s state (numeral es[q*g+x].1))
          write (numeral es[q*g+x].2.1)) dir (numeral es[q*g+x].2.2)) := by
  let e := es[q*g+x]
  let tail := Diagonal.tableBits (es.drop (q*g+x+1))
  let a := Function.update s search (Diagonal.tableBits es)
  let b := Function.update a index (numeral (q*g))
  let c := Function.update a index (numeral (q*g+x))
  let d := Function.update c search (Diagonal.entryBits e++tail)
  let f := Function.update d state []
  let j := Function.update (Function.update f search (Diagonal.unary e.2.1++Diagonal.unary e.2.2++tail))
    state (numeral e.1)
  let k := Function.update (Function.update j search (Diagonal.unary e.2.2++tail)) write (numeral e.2.1)
  let l := Function.update (Function.update k search tail) dir (numeral e.2.2)
  have h1 : (Program.copy tab search).Exec s (12*(Diagonal.tableBits es).length+2) a := by
    simpa [a,ht,hs] using Program.copy_exec tab search (by decide) s
  obtain ⟨t2,ht2,h2⟩ := mulAdd_exec state alpha index (by decide) a q g
    (by simp [a,hq]) (by simp [a,hg])
  replace h2 : (mulAdd state alpha index).Exec a t2 b := by simpa [b,a,hn] using h2
  have h3 : (Program.copy cur index).Exec b (12*x+2) c := by
    have hh := Program.copy_exec cur index (by decide) b
    simpa [b,c,a,hx,hn,←numeral_add,Nat.add_comm x] using hh
  obtain ⟨t4,ht4,h4⟩ := seek_exec search index (q*g+x) c (by simp [c])
  have hc : c search=Diagonal.tableBits es := by simp [c,a]
  rw [hc,table_at es _ hi] at h4
  change (seek search index).Exec c t4 d at h4
  have h5 : (Program.clear state).Exec d (3*q+1) f := by
    simpa [d,c,a,hq] using Program.clear_exec state d
  have h6 : (Program.read search state).Exec f (5*e.1+3) j := by
    simpa [f,d,j] using Program.read_exec search state (by decide) f
  have h7 : (Program.read search write).Exec j (5*e.2.1+3) k := by
    simpa [k,j,f,d,c,a,hw] using Program.read_exec search write (by decide) j
  have h8 : (Program.read search dir).Exec k (5*e.2.2+3) l := by
    simpa [l,k,j,f,d,c,a,hd] using Program.read_exec search dir (by decide) k
  have h9 := Program.clear_exec search l
  have h10 := Program.clear_exec index (Function.update l search [])
  have he := Program.seq_exec h1 (Program.seq_exec h2 (Program.seq_exec h3
    (Program.seq_exec h4 (Program.seq_exec h5 (Program.seq_exec h6 (Program.seq_exec h7
      (Program.seq_exec h8 (Program.seq_exec h9 h10))))))))
  have hout : Function.update (Function.update l search []) index []=
        Function.update (Function.update (Function.update s state (numeral e.1))
          write (numeral e.2.1)) dir (numeral e.2.2) := by
    funext r; cases r <;> simp [l,k,j,f,d,c,a,hs,hn]
  rw [hout] at he
  refine ⟨_,?_,he⟩
  have hlen := tailField_iterate_le (3*(q*g+x)) (Diagonal.tableBits es)
  rw [table_at es _ hi] at hlen
  have he_len : (Diagonal.entryBits e).length=e.1+e.2.1+e.2.2+3 := by
    simp [Diagonal.entryBits,unary_tile]; omega
  change (Diagonal.entryBits e++tail).length≤(Diagonal.tableBits es).length at hlen
  rw [List.length_append,he_len] at hlen
  rw [hc] at ht4
  simp only [l,k,j,f,d,c,a]
  simp only [Function.update_of_ne (by decide : search≠dir),Function.update_self,
    Function.update_of_ne (by decide : index≠search),
    Function.update_of_ne (by decide : index≠dir),
    Function.update_of_ne (by decide : index≠write),
    Function.update_of_ne (by decide : index≠state),numeral_length]
  nlinarith

end WLTime.Universal

end OAI
