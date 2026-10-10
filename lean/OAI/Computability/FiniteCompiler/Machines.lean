import OAI.Computability.FiniteCompiler.Effectivity

namespace OAI

/-!
Stack, binary, TM2, and TM0 realizations of partial recursive programs.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.StackLift
open Turing Relation
open Turing.PartrecToTM2

 def swap : K' → K'
  | .main => .rev | .rev => .main | .aux => .aux | .stack => .stack
 @[simp] theorem swap_swap (k : K') : swap (swap k) = k := by cases k <;> rfl
 theorem swap_injective : Function.Injective swap := Function.LeftInverse.injective swap_swap

 variable {S Λ : Type*}
 abbrev Symbol (S : Type*) := Γ' ⊕ S
 abbrev Store (S : Type*) := Option (Symbol S)
 inductive Label (S Λ : Type*)
  | pre | emit : S → Label S Λ
  | run : Λ → Label S Λ
  | post | reject
  deriving DecidableEq, Fintype

 def proj : Store S → Option Γ'
  | some (.inl a) => some a | _ => none
 def store (v : Option Γ') : Store S := v.map Sum.inl
 @[simp] theorem proj_store (v : Option Γ') : proj (store (S := S) v) = v := by cases v <;> rfl

 def embedStacks (t : K' → List Γ') : K' → List (Symbol S) := fun k => (t (swap k)).map Sum.inl
 @[simp] theorem embedStacks_swap (t : K' → List Γ') (k : K') :
    embedStacks (S := S) t (swap k) = (t k).map Sum.inl := by simp [embedStacks]
 theorem embedStacks_update (t : K' → List Γ') (k : K') (w : List Γ') :
    embedStacks (S := S) (Function.update t k w) =
      Function.update (embedStacks t) (swap k) (w.map Sum.inl) := by
  funext j
  by_cases h : j = swap k
  · subst j; simp
  · have hh : swap j ≠ k := fun e => h (by rw [←e,swap_swap])
    simp [embedStacks,Function.update_of_ne h,Function.update_of_ne hh]

 def stmt : TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ') →
    TM2.Stmt (fun _ : K' => Symbol S) (Label S Λ) (Store S)
  | .push k f q => .push (swap k) (fun v => .inl (f (proj v))) (stmt q)
  | .peek k f q => .peek (swap k) (fun v a => store (f (proj v) (proj a))) (stmt q)
  | .pop k f q => .pop (swap k) (fun v a => store (f (proj v) (proj a))) (stmt q)
  | .load f q => .load (fun v => store (f (proj v))) (stmt q)
  | .branch f p q => .branch (fun v => f (proj v)) (stmt p) (stmt q)
  | .goto f => .goto (fun v => .run (f (proj v)))
  | .halt => .goto (fun _ => .post)

 def cfg (c : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')) :
    TM2.Cfg (fun _ : K' => Symbol S) (Label S Λ) (Store S) :=
  ⟨some (c.l.elim .post .run),store c.var,embedStacks c.stk⟩

 theorem stmt_correct (q : TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ'))
    (v : Option Γ') (t : K' → List Γ') :
    TM2.stepAux (stmt (S := S) q) (store v) (embedStacks t) = cfg (TM2.stepAux q v t) := by
  induction q generalizing v t with
  | push k f q ih =>
      simp only [stmt,TM2.stepAux,proj_store,embedStacks_swap]
      rw [←List.map_cons,←embedStacks_update]
      exact ih _ _
  | peek k f q ih =>
      simp only [stmt,TM2.stepAux,proj_store,embedStacks_swap]
      have he : proj (((t k).map Sum.inl).head? : Store S) = (t k).head? := by
        cases t k <;> rfl
      rw [he]; exact ih _ _
  | pop k f q ih =>
      simp only [stmt,TM2.stepAux,proj_store,embedStacks_swap]
      have he : proj (((t k).map Sum.inl).head? : Store S) = (t k).head? := by
        cases t k <;> rfl
      rw [he,←List.map_tail,←embedStacks_update]
      exact ih _ _
  | load f q ih => simpa only [stmt,TM2.stepAux,proj_store] using ih (f v) t
  | branch f p q ihp ihq =>
      cases h : f v <;> simp only [stmt,TM2.stepAux,proj_store,h,Bool.cond_false,Bool.cond_true]
      · exact ihq _ _
      · exact ihp _ _
  | goto f => simp [stmt,TM2.stepAux,cfg]
  | halt => rfl

 variable (M : Λ → TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ'))
  (W : Label S Λ → TM2.Stmt (fun _ : K' => Symbol S) (Label S Λ) (Store S))
  (hW : ∀ l, W (.run l) = stmt (M l))

 include hW
 theorem step_correct (c : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ'))
    (d : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')) (h : d ∈ TM2.step M c) :
    cfg (S := S) d ∈ TM2.step W (cfg c) := by
  rcases c with ⟨l,v,t⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      simp only [TM2.step,Option.mem_some_iff] at h
      subst d
      simpa only [cfg,Option.elim_some,TM2.step,hW,Option.mem_some_iff] using stmt_correct (M l) v t

 theorem reaches_correct {c d : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')}
    (h : TM2.Reaches M c d) : TM2.Reaches W (cfg (S := S) c) (cfg d) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (step_correct M W hW _ _ h)

 /-- Until the original interpreter halts, the wrapper cannot escape its run
     sector. This is the divergence/soundness half, not only a terminating test. -/
 theorem path_cases {c : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')}
    {z : TM2.Cfg (fun _ : K' => Symbol S) (Label S Λ) (Store S)}
    (h : TM2.Reaches W (cfg c) z) :
    (∃ d, TM2.Reaches M c d ∧ z = cfg d) ∨
    (∃ d, TM2.Reaches M c d ∧ d.l = none ∧ TM2.Reaches W (cfg d) z) := by
  induction h with
  | refl => exact Or.inl ⟨c,.refl,rfl⟩
  | @tail z z' _ hs ih =>
      rcases ih with ⟨d,hd,rfl⟩ | ⟨d,hd,hh,hr⟩
      · cases hl : d.l with
        | none => exact Or.inr ⟨d,hd,hl,ReflTransGen.single hs⟩
        | some l =>
            let e := TM2.stepAux (M l) d.var d.stk
            have he : e ∈ TM2.step M d := by
              rcases d with ⟨ld,vd,td⟩
              simp only at hl
              simp [TM2.step,hl,e]
            have hh := step_correct M W hW d e he
            have hz : z' = cfg e := Option.mem_unique hs hh
            exact Or.inl ⟨e,hd.tail he,hz⟩
      · exact Or.inr ⟨d,hd,hh,hr.tail hs⟩

end FiniteAlgebraicEnvelopes.MachineRealization.StackLift

namespace FiniteAlgebraicEnvelopes.MachineRealization.BinaryCode
open Turing Turing.PartrecToTM2

def value : List Γ' → ℕ
  | [] => 0
  | .bit0 :: l => 2 * value l
  | .bit1 :: l => 2 * value l + 1
  | _ :: l => value l

@[simp] theorem value_pos (n : PosNum) : value (trPosNum n) = (n : ℕ) := by
  induction n with
  | one => rfl
  | bit0 n ih => simpa [trPosNum,value,ih] using (show 2 * (n : ℕ) = (n : ℕ) + (n : ℕ) by omega)
  | bit1 n ih => simpa [trPosNum,value,ih] using (show 2 * (n : ℕ) + 1 = (n : ℕ) + (n : ℕ) + 1 by omega)

@[simp] theorem value_num (n : Num) : value (trNum n) = (n : ℕ) := by cases n <;> simp [trNum,value]
@[simp] theorem value_nat (n : ℕ) : value (trNat n) = n := by simp [trNat]
 theorem trNat_injective : Function.Injective trNat := by
  intro a b h
  simpa using congrArg value h

def block (n : ℕ) : List Γ' := trNat n ++ [.cons]

theorem delimiter_cancel {x y u v : List Γ'}
    (hx : ∀ a ∈ x, natEnd a = false) (hy : ∀ a ∈ y, natEnd a = false)
    (h : x ++ .cons :: u = y ++ .cons :: v) : x = y ∧ u = v := by
  induction x generalizing y with
  | nil =>
      cases y with
      | nil => simpa using h
      | cons a y =>
          have ha : a = Γ'.cons := (List.cons.inj h).1.symm
          have hh := hy a (List.mem_cons_self)
          subst a
          cases hh
  | cons a x ih =>
      cases y with
      | nil =>
          have ha : a = Γ'.cons := (List.cons.inj h).1
          have hh := hx a List.mem_cons_self
          subst a
          cases hh
      | cons b y =>
          obtain ⟨rfl,hh⟩ := List.cons.inj h
          obtain ⟨rfl,hu⟩ := ih (fun c hc => hx c (List.mem_cons_of_mem _ hc))
            (fun c hc => hy c (List.mem_cons_of_mem _ hc)) hh
          exact ⟨rfl,hu⟩

theorem block_cancel {a b : ℕ} {u v : List Γ'}
    (h : block a ++ u = block b ++ v) : a = b ∧ u = v := by
  simp only [block,List.append_assoc,List.singleton_append] at h
  obtain ⟨hab,huv⟩ := delimiter_cancel (trNat_natEnd a) (trNat_natEnd b) h
  exact ⟨trNat_injective hab,huv⟩

end FiniteAlgebraicEnvelopes.MachineRealization.BinaryCode

namespace FiniteAlgebraicEnvelopes.MachineRealization.RawTM
open Turing Turing.PartrecToTM2 Relation
open StackLift BinaryCode
variable {S Λ : Type*} [DecidableEq S] [Encodable S]

abbrev Stmt (S Λ : Type*) := TM2.Stmt (fun _ : K' => Symbol S) (Label S Λ) (Store S)
abbrev Config (S Λ : Type*) := TM2.Cfg (fun _ : K' => Symbol S) (Label S Λ) (Store S)

def tracks (out : List S) (binary : List Γ') : K' → List (Symbol S)
  | .main => out.map Sum.inr
  | .rev => binary.map Sum.inl
  | .aux | .stack => []

omit [DecidableEq S] [Encodable S] in
@[simp] theorem tracks_main (out : List S) (binary : List Γ') : tracks out binary .main = out.map Sum.inr := rfl
omit [DecidableEq S] [Encodable S] in
@[simp] theorem tracks_rev (out : List S) (binary : List Γ') : tracks out binary .rev = binary.map Sum.inl := rfl
omit [DecidableEq S] [Encodable S] in
 theorem tracks_update_main (out : List S) (binary : List Γ') (out' : List S) :
    Function.update (tracks out binary) .main (out'.map Sum.inr) = tracks out' binary := by
  funext k; cases k <;> simp [tracks]
omit [DecidableEq S] [Encodable S] in
 theorem tracks_update_rev (out : List S) (binary binary' : List Γ') :
    Function.update (tracks out binary) .rev (binary'.map Sum.inl) = tracks out binary' := by
  funext k; cases k <;> simp [tracks]

def postCfg (out : List S) (binary : List Γ') : Config S Λ := ⟨some .post,none,tracks out binary⟩
def reject : Stmt S Λ := .goto (fun _ => .reject)
def finish (pre : List Γ') : Stmt S Λ :=
  match Encodable.decode (α := S) (value pre.reverse - 1) with
  | some s => .push .main (fun _ => .inr s) (.load (fun _ => none) (.goto (fun _ => .post)))
  | none => reject

def decoder : ℕ → List Γ' → Stmt S Λ
  | n, pre => .pop .rev (fun _ a => a)
      (.branch (fun v => decide (StackLift.proj v = some .cons)) (finish pre)
        (match n with
        | 0 => reject
        | n+1 => .branch (fun v => decide (StackLift.proj v = some .bit0)) (decoder n (.bit0::pre))
            (.branch (fun v => decide (StackLift.proj v = some .bit1)) (decoder n (.bit1::pre)) reject)))

omit [DecidableEq S] in
theorem decoder_correct (fuel : ℕ) (pre l : List Γ') (tail : List Γ')
    (out : List S) (s : S) (v : Store S)
    (hlen : l.length ≤ fuel) (hbits : ∀ a ∈ l, natEnd a = false)
    (hdec : Encodable.decode (α := S) (value (pre.reverse ++ l) - 1) = some s) :
    TM2.stepAux (decoder (Λ := Λ) fuel pre) v (tracks out (l ++ .cons :: tail)) =
      postCfg (s::out) tail := by
  induction l generalizing fuel pre v with
  | nil =>
      simp only [List.append_nil] at hdec
      cases fuel <;> simp only [decoder,TM2.stepAux,tracks_rev,List.nil_append,List.map_cons,
        List.head?_cons,StackLift.proj,List.tail_cons,decide_true,Bool.cond_true,finish,hdec]
      all_goals
        rw [tracks_update_rev]
        simp only [tracks_main]
        rw [← List.map_cons,tracks_update_main]
        rfl
  | cons a l ih =>
      cases fuel with
      | zero => simp at hlen
      | succ fuel =>
          have hb := hbits a List.mem_cons_self
          have hb' : ∀ a ∈ l, natEnd a = false := fun a ha => hbits a (List.mem_cons_of_mem _ ha)
          have hl : l.length ≤ fuel := by simpa using hlen
          cases a <;> try cases hb
          · simp only [decoder,TM2.stepAux,tracks_rev,List.cons_append,List.map_cons,
              List.head?_cons,StackLift.proj,List.tail_cons,decide_true,Bool.cond_true]
            rw [tracks_update_rev]
            apply ih fuel (.bit0::pre) _ hl hb'
            simpa [List.reverse_cons,List.append_assoc] using hdec
          · simp only [decoder,TM2.stepAux,tracks_rev,List.cons_append,List.map_cons,
              List.head?_cons,StackLift.proj,List.tail_cons,decide_true,Bool.cond_true]
            rw [tracks_update_rev]
            apply ih fuel (.bit1::pre) _ hl hb'
            simpa [List.reverse_cons,List.append_assoc] using hdec

omit [DecidableEq S] in
theorem decoder_block (fuel : ℕ) (tail : List Γ') (out : List S) (s : S) (v : Store S)
    (h : (trNat (Encodable.encode s + 1)).length ≤ fuel) :
    TM2.stepAux (decoder (Λ := Λ) fuel []) v
      (tracks out (block (Encodable.encode s + 1) ++ tail)) = postCfg (s::out) tail := by
  simp only [block,List.append_assoc,List.singleton_append]
  apply decoder_correct fuel [] _ tail out s v h (trNat_natEnd _)
  simp

def pushList : List Γ' → Stmt S Λ → Stmt S Λ
  | [], q => q
  | a::l,q => pushList l (.push .rev (fun _ => .inl a) q)

omit [DecidableEq S] [Encodable S] in
theorem pushList_correct (l : List Γ') (q : Stmt S Λ) (v : Store S)
    (out : List S) (binary : List Γ') :
    TM2.stepAux (pushList l q) v (tracks out binary) =
      TM2.stepAux q v (tracks out (l ++ binary)) := by
  induction l generalizing q binary with
  | nil => rfl
  | cons a l ih =>
      rw [pushList,ih]
      simp only [TM2.stepAux,tracks_rev]
      rw [←List.map_cons,tracks_update_rev]
      rfl

def machine (B : ℕ) (M : Λ → TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ')) (start : Λ) :
    Label S Λ → Stmt S Λ
  | .pre => .pop .main (fun _ a => a) (.goto (fun v =>
      match v with
      | some (.inr s) => .emit s
      | none => .run start
      | _ => .reject))
  | .emit s => pushList (block (Encodable.encode s + 1))
      (.load (fun _ => none) (.goto (fun _ => .pre)))
  | .run l => StackLift.stmt (M l)
  | .post => .peek .rev (fun _ a => a)
      (.branch (fun v => v.isNone) (.load (fun _ => none) .halt) (decoder B []))
  | .reject => reject

def preCfg (out : List S) (binary : List Γ') : Config S Λ := ⟨some .pre,none,tracks out binary⟩
def haltCfg (out : List S) : Config S Λ := ⟨none,none,tracks out []⟩
def runCfg (start : Λ) (binary : List Γ') : Config S Λ := ⟨some (.run start),none,tracks [] binary⟩

variable (B : ℕ) (M : Λ → TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ')) (start : Λ)

omit [DecidableEq S] in
theorem pre_cons (s : S) (out : List S) (binary : List Γ') :
    TM2.Reaches (machine B M start) (preCfg (s::out) binary)
      (preCfg out (block (Encodable.encode s + 1) ++ binary)) := by
  let mid : Config S Λ := ⟨some (.emit s),some (.inr s),tracks out binary⟩
  apply ReflTransGen.trans (b := mid) (ReflTransGen.single ?_) (ReflTransGen.single ?_)
  · simp only [preCfg,TM2.step,machine,TM2.stepAux,tracks_main,List.map_cons,
      List.head?_cons,List.tail_cons]
    rw [tracks_update_main]
    rfl
  · simp only [mid,TM2.step,machine]
    rw [pushList_correct]
    rfl

omit [DecidableEq S] in
theorem pre_nil (binary : List Γ') :
    TM2.Reaches (machine (S := S) B M start) (preCfg [] binary) (runCfg start binary) := by
  apply ReflTransGen.single
  simp only [preCfg,TM2.step,machine,TM2.stepAux,tracks_main,List.map_nil,
    List.head?_nil,List.tail_nil]
  rw [show ([] : List (Symbol S)) = [].map Sum.inr from rfl,tracks_update_main]
  rfl

def numbers (w : List S) : List ℕ := w.map (fun s => Encodable.encode s + 1)

omit [DecidableEq S] [Encodable S] in
@[simp] theorem trList_append (u v : List ℕ) : trList (u ++ v) = trList u ++ trList v := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [trList,ih,List.append_assoc]

omit [DecidableEq S] in
theorem pre_complete (w : List S) (binary : List Γ') :
    TM2.Reaches (machine B M start) (preCfg w binary)
      (runCfg start (trList (numbers w.reverse) ++ binary)) := by
  induction w generalizing binary with
  | nil => simpa [numbers] using pre_nil (S := S) B M start binary
  | cons s w ih =>
      apply (pre_cons B M start s w binary).trans
      simpa [TM2.Reaches,List.reverse_cons,numbers,List.map_append,trList,block,List.append_assoc] using
        ih (block (Encodable.encode s + 1) ++ binary)

omit [DecidableEq S] in
theorem post_cons (s : S) (w out : List S)
    (hB : (trNat (Encodable.encode s + 1)).length ≤ B) :
    TM2.Reaches (machine B M start) (postCfg out (trList (numbers (s::w))))
      (postCfg (s::out) (trList (numbers w))) := by
  apply ReflTransGen.single
  simp only [postCfg,TM2.step,machine,TM2.stepAux,tracks_rev]
  have hn : (trList (numbers (s::w))).map (Sum.inl : Γ' → Symbol S) ≠ [] := by
    simp [numbers,trList]
  rw [show ((trList (numbers (s::w))).map (Sum.inl : Γ' → Symbol S)).head?.isNone = false from by
    simpa using hn]
  simp only [Bool.cond_false,numbers,List.map_cons,trList]
  have hh := decoder_block (Λ := Λ) B (trList (numbers w)) out s
      (((trList (numbers (s::w))).map Sum.inl).head?) hB
  simpa only [Option.mem_some_iff,block,List.append_assoc,List.singleton_append,numbers,
      List.map_cons,trList,postCfg] using hh

omit [DecidableEq S] in
theorem post_nil (out : List S) :
    TM2.Reaches (machine B M start) (postCfg out []) (haltCfg out) := by
  apply ReflTransGen.single
  rfl

omit [DecidableEq S] in
theorem post_complete (w out : List S)
    (hB : ∀ s ∈ w, (trNat (Encodable.encode s + 1)).length ≤ B) :
    TM2.Reaches (machine B M start) (postCfg out (trList (numbers w))) (haltCfg (w.reverse ++ out)) := by
  induction w generalizing out with
  | nil => simpa [numbers] using post_nil B M start out
  | cons s w ih =>
      apply (post_cons B M start s w out (hB s List.mem_cons_self)).trans
      simpa [TM2.Reaches,List.reverse_cons,List.append_assoc] using
        ih (s::out) (fun a ha => hB a (List.mem_cons_of_mem _ ha))

def baseCfg (l : Option Λ) (binary : List Γ') : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ') :=
  ⟨l,none,K'.elim binary [] [] []⟩

omit [DecidableEq S] [Encodable S] in
@[simp] theorem lift_base_some (l : Λ) (binary : List Γ') :
    StackLift.cfg (S := S) (baseCfg (some l) binary) = runCfg l binary := by
  simp only [StackLift.cfg,baseCfg,runCfg,Option.elim_some]
  congr 1
  funext k; cases k <;> rfl
omit [DecidableEq S] [Encodable S] in
@[simp] theorem lift_base_none (binary : List Γ') :
    StackLift.cfg (S := S) (baseCfg (Λ := Λ) none binary) = postCfg [] binary := by
  simp only [StackLift.cfg,baseCfg,postCfg,Option.elim_none]
  congr 1
  funext k; cases k <;> rfl

omit [DecidableEq S] in
 theorem eval_run {w : List S} {f : List S →. List S}
    (hB : ∀ s : S, (trNat (Encodable.encode s + 1)).length ≤ B)
    (hM : StateTransition.eval (TM2.step M) (baseCfg (some start) (trList (numbers w))) =
      (f w).map (fun out => baseCfg none (trList (numbers out)))) :
    StateTransition.eval (TM2.step (machine B M start)) (runCfg start (trList (numbers w))) =
      (f w).map (fun out => haltCfg out.reverse) := by
  have complete : ∀ out ∈ f w, haltCfg out.reverse ∈
      StateTransition.eval (TM2.step (machine B M start)) (runCfg start (trList (numbers w))) := by
    intro out hout
    have ht : baseCfg (Λ := Λ) none (trList (numbers out)) ∈
        StateTransition.eval (TM2.step M) (baseCfg (some start) (trList (numbers w))) := by
      rw [hM]; exact Part.mem_map _ hout
    have hh := StackLift.reaches_correct (S := S) M (machine B M start) (fun _ => rfl)
      (StateTransition.mem_eval.mp ht).1
    simp only [lift_base_some,lift_base_none] at hh
    apply StateTransition.mem_eval.mpr
    refine ⟨hh.trans ?_,rfl⟩
    simpa only [TM2.Reaches,List.append_nil] using post_complete B M start out [] (fun s _ => hB s)
  apply Part.ext
  intro z
  rw [Part.mem_map_iff]
  constructor
  · intro hz
    obtain ⟨hr,ht⟩ := StateTransition.mem_eval.mp hz
    rw [←lift_base_some] at hr
    rcases StackLift.path_cases M (machine B M start) (fun _ => rfl) hr with
        ⟨d,hd,rfl⟩ | ⟨d,hd,hhalt,hdz⟩
    · simp [StackLift.cfg,TM2.step] at ht
    · have hmem : d ∈ StateTransition.eval (TM2.step M)
          (baseCfg (some start) (trList (numbers w))) := by
        apply StateTransition.mem_eval.mpr
        refine ⟨hd,?_⟩
        rcases d with ⟨l,v,t⟩
        simp only at hhalt
        simp [TM2.step,hhalt]
      rw [hM] at hmem
      obtain ⟨out,hout,he⟩ := (Part.mem_map_iff _).mp hmem
      exact ⟨out,hout,Part.mem_unique (complete out hout) hz⟩
  · rintro ⟨out,hout,rfl⟩
    exact complete out hout

omit [DecidableEq S] in
 theorem eval_pre {w : List S} {f : List S →. List S}
    (hB : ∀ s : S, (trNat (Encodable.encode s + 1)).length ≤ B)
    (hM : StateTransition.eval (TM2.step M) (baseCfg (some start) (trList (numbers w))) =
      (f w).map (fun out => baseCfg none (trList (numbers out)))) :
    StateTransition.eval (TM2.step (machine B M start)) (preCfg w.reverse []) =
      (f w).map (fun out => haltCfg out.reverse) := by
  have hp := pre_complete B M start w.reverse []
  simp only [List.reverse_reverse,List.append_nil] at hp
  rw [StateTransition.reaches_eval hp]
  exact eval_run B M start hB hM

end FiniteAlgebraicEnvelopes.MachineRealization.RawTM

/- Actual finite-state extraction from the Mathlib evaluator.  This is a
   dependency of the compiler realization, not a realization assumption. -/
namespace FiniteAlgebraicEnvelopes.MachineRealization
open Turing Relation

namespace FiniteTM2
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq Λ]

 def restrictStmt (S : Finset Λ) (q : TM2.Stmt Γ Λ σ) (h : TM2.SupportsStmt S q) :
    TM2.Stmt Γ {l // l ∈ S} σ :=
  match q with
  | .push k f q => .push k f (restrictStmt S q h)
  | .peek k f q => .peek k f (restrictStmt S q h)
  | .pop k f q => .pop k f (restrictStmt S q h)
  | .load f q => .load f (restrictStmt S q h)
  | .branch f p q => .branch f (restrictStmt S p h.1) (restrictStmt S q h.2)
  | .goto f => .goto (fun v => ⟨f v,h v⟩)
  | .halt => .halt

 def embedCfg (S : Finset Λ) (c : TM2.Cfg Γ {l // l ∈ S} σ) : TM2.Cfg Γ Λ σ :=
  ⟨c.l.map Subtype.val,c.var,c.stk⟩

 variable [DecidableEq K]
omit [DecidableEq Λ] in
 theorem embed_stepAux (S : Finset Λ) (q : TM2.Stmt Γ Λ σ) (h : TM2.SupportsStmt S q)
    (v : σ) (t : ∀ k, List (Γ k)) :
    embedCfg S (TM2.stepAux (restrictStmt S q h) v t) = TM2.stepAux q v t := by
  induction q generalizing v t with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih =>
      exact ih h _ _
  | branch f p q ihp ihq =>
      cases hv : f v <;> simp only [restrictStmt,TM2.stepAux,hv,Bool.cond_false,Bool.cond_true]
      · exact ihq h.2 _ _
      · exact ihp h.1 _ _
  | goto f => rfl
  | halt => rfl

 variable [Inhabited Λ] (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ) (h : TM2.Supports M S)
 def machine (l : {l // l ∈ S}) : TM2.Stmt Γ {l // l ∈ S} σ :=
  restrictStmt S (M l.val) (h.2 _ l.property)

omit [DecidableEq Λ] in
 theorem embed_step (c : TM2.Cfg Γ {l // l ∈ S} σ) :
    (TM2.step (machine M S h) c).map (embedCfg S) = TM2.step M (embedCfg S c) := by
  rcases c with ⟨l,v,t⟩
  cases l with
  | none => rfl
  | some l => simpa only [TM2.step,embedCfg,Option.map_some,machine] using
      congrArg some (embed_stepAux S (M l.val) (h.2 _ l.property) v t)

omit [DecidableEq Λ] in
 theorem respects : StateTransition.Respects (TM2.step (machine M S h)) (TM2.step M)
    (fun a b => embedCfg S a = b) := by
  apply StateTransition.fun_respects.mpr
  intro a
  have hh := embed_step M S h a
  cases hc : TM2.step (machine M S h) a with
  | none =>
      change TM2.step M (embedCfg S a) = none
      simpa only [hc,Option.map_none] using hh.symm
  | some b =>
      apply TransGen.single
      change TM2.step M (embedCfg S a) = some (embedCfg S b)
      simpa only [hc,Option.map_some] using hh.symm

omit [DecidableEq Λ] in
 theorem eval_embed (c : TM2.Cfg Γ {l // l ∈ S} σ) :
    StateTransition.eval (TM2.step M) (embedCfg S c) =
      (StateTransition.eval (TM2.step (machine M S h)) c).map (embedCfg S) :=
  StateTransition.tr_eval' _ _ _ (respects M S h) c

 variable [Inhabited σ]
 def initial (k : K) (w : List (Γ k)) : TM2.Cfg Γ {l // l ∈ S} σ :=
  ⟨some ⟨default,h.1⟩,default,Function.update (fun _ => []) k w⟩

omit [DecidableEq Λ] in
 @[simp] theorem embed_initial (k : K) (w : List (Γ k)) :
    embedCfg S (initial M S h k w) = TM2.init k w := rfl

omit [DecidableEq Λ] in
 theorem eval_initial (k : K) (w : List (Γ k)) :
    TM2.eval M k w =
      (StateTransition.eval (TM2.step (machine M S h)) (initial M S h k w)).map
        (fun c => c.stk k) := by
  unfold TM2.eval
  rw [←embed_initial M S h k w,eval_embed]
  simp only [Part.map_map]
  rfl

end FiniteTM2

namespace Numerical
open Turing.ToPartrec Turing.PartrecToTM2

 theorem exists_evaluator {f : ℕ →. ℕ} (hf : Partrec f) :
    ∃ c : Code, ∀ n, StateTransition.eval (TM2.step tr) (init c [n]) =
      (f n).map (fun out => halt [out]) := by
  obtain ⟨c,hc⟩ := Turing.ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf)
  refine ⟨c,fun n => ?_⟩
  rw [tr_eval,hc ⟨[n],rfl⟩]
  rfl

 theorem exists_finite_evaluator {f : ℕ →. ℕ} (hf : Partrec f) :
    ∃ c : Code, ∃ S : Finset Λ',
      @TM2.Supports K' (fun _ => Γ') Λ' (Option Γ') ⟨trNormal c Cont'.halt⟩ tr S ∧
      ∀ n, StateTransition.eval (TM2.step tr) (init c [n]) =
        (f n).map (fun out => halt [out]) := by
  obtain ⟨c,hc⟩ := exists_evaluator hf
  exact ⟨c,codeSupp c Cont'.halt,tr_supports c Cont'.halt,hc⟩

end Numerical
end FiniteAlgebraicEnvelopes.MachineRealization

namespace FiniteAlgebraicEnvelopes.MachineRealization.ListCode
open Turing.ToPartrec Encodable

private theorem eval_comp (f g : Code) (v : List ℕ) :
    (Code.comp f g).eval v = (g.eval v).bind (fun w => f.eval w) := rfl

attribute [local simp] eval_comp

private theorem fix_eval_fwd (c : Code) (w w' : List ℕ)
    (h : Sum.inr w' ∈ Part.map
      (fun v : List ℕ => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) (c.eval w)) :
    (Code.fix c).eval w = (Code.fix c).eval w' :=
  PFun.fix_fwd_eq (α := List ℕ) (β := List ℕ)
    (f := fun v : List ℕ => Part.map
      (fun v : List ℕ => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) (c.eval v))
    (a := w) (a' := w') h

 def prefix₂ : Code := .cons .head (.cons (.comp .head .tail) .nil)
 @[simp] theorem prefix₂_eval (a b : ℕ) (l : List ℕ) :
    prefix₂.eval (a::b::l) = Part.some [a,b] := by simp [prefix₂]

 theorem binary_code {f : ℕ → ℕ → ℕ} (hf : Computable₂ f) :
    ∃ c : Code, ∀ a b l, c.eval (a::b::l) = Part.some [f a b] := by
  obtain ⟨c,hc⟩ := Code.exists_code (Nat.Partrec'.part_iff₂.mpr hf.partrec₂)
  refine ⟨.comp c prefix₂,fun a b l => ?_⟩
  simp only [eval_comp,prefix₂_eval,Part.bind_some]
  have he := hc ⟨[a,b],rfl⟩
  exact he

 def test (t p q : Code) : Code := .comp (.case p (.comp q .tail)) (.cons t .id)
 theorem test_eval (t p q : Code) (w : List ℕ) {n : ℕ}
    (ht : t.eval w = Part.some [n]) :
    (test t p q).eval w = if n = 0 then p.eval w else q.eval w := by
  simp only [test,eval_comp,Code.cons_eval,Code.id_eval,ht]
  cases n <;> simp [List.headI]

 def one : Code := .comp .succ .zero
 @[simp] theorem one_eval (w : List ℕ) : one.eval w = Part.some [1] := by simp [one]

 def encodeStep (c : Code) : Code :=
  test (.comp .head .tail) (.cons .zero .head)
    (.cons one (.cons c (.comp .tail .tail)))
 def encoder (c : Code) : Code := .comp (.fix (encodeStep c)) .zero'

 theorem encodeStep_nil (c : Code) (a : ℕ) :
    (encodeStep c).eval [a] = Part.some [0,a] := by
  rw [encodeStep,test_eval _ _ _ _ (n := 0) (by simp)]
  simp
 theorem encodeStep_cons (c : Code)
    (hc : ∀ a b l, c.eval (a::b::l) = Part.some [Nat.pair (b-1) a + 1])
    (a b : ℕ) (l : List ℕ) :
    (encodeStep c).eval (a::(b+1)::l) = Part.some (1::(Nat.pair b a + 1)::l) := by
  rw [encodeStep,test_eval _ _ _ _ (n := b+1) (by simp)]
  simp [hc]

 theorem encode_loop (c : Code)
    (hc : ∀ a b l, c.eval (a::b::l) = Part.some [Nat.pair (b-1) a + 1])
    (w acc : List ℕ) :
    (Code.fix (encodeStep c)).eval (encode acc :: w.map Nat.succ) =
      Part.some [encode (w.reverse ++ acc)] := by
  induction w generalizing acc with
  | nil =>
      apply Part.eq_some_iff.mpr
      rw [Code.fix_eval]
      apply PFun.fix_stop
      simp [encodeStep_nil]
  | cons b l ih =>
      rw [List.map_cons]
      have hs : Sum.inr (encode (b::acc)::l.map Nat.succ) ∈
          ((encodeStep c).eval (encode acc::(b+1)::l.map Nat.succ)).map
            (fun v => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) := by
        rw [encodeStep_cons c hc]
        simp [encode_list_cons]
      rw [fix_eval_fwd _ _ _ hs,ih]
      simp [List.reverse_cons,List.append_assoc]

 theorem encoder_eval (c : Code)
    (hc : ∀ a b l, c.eval (a::b::l) = Part.some [Nat.pair (b-1) a + 1]) (w : List ℕ) :
    (encoder c).eval (w.map Nat.succ) = Part.some [encode w.reverse] := by
  simp only [encoder,eval_comp,Code.zero'_eval]
  simpa using encode_loop c hc w []

 def decodeStep (h t : Code) : Code :=
  test .head (.cons .zero .tail)
    (.cons one (.cons t (.cons h .tail)))
 def decoder (h t : Code) : Code := .fix (decodeStep h t)
 theorem decodeStep_zero (h t : Code) (l : List ℕ) :
    (decodeStep h t).eval (0::l) = Part.some (0::l) := by
  rw [decodeStep,test_eval _ _ _ _ (n := 0) (by simp)]
  simp
 theorem decodeStep_cons (h t : Code)
    (hh : ∀ n l, h.eval (n::l) = Part.some [(n-1).unpair.1+1])
    (ht : ∀ n l, t.eval (n::l) = Part.some [(n-1).unpair.2])
    (b : ℕ) (w l : List ℕ) :
    (decodeStep h t).eval (encode (b::w)::l) = Part.some (1::encode w::(b+1)::l) := by
  rw [decodeStep,test_eval _ _ _ _ (n := encode (b::w)) (by simp)]
  simp [encode_list_cons,hh,ht]

 theorem decoder_eval (h t : Code)
    (hh : ∀ n l, h.eval (n::l) = Part.some [(n-1).unpair.1+1])
    (ht : ∀ n l, t.eval (n::l) = Part.some [(n-1).unpair.2])
    (w acc : List ℕ) :
    (decoder h t).eval (encode w::acc) = Part.some (w.reverse.map Nat.succ ++ acc) := by
  induction w generalizing acc with
  | nil =>
      apply Part.eq_some_iff.mpr
      rw [decoder,Code.fix_eval]
      apply PFun.fix_stop
      simp [decodeStep_zero]
  | cons b w ih =>
      rw [decoder]
      have hs : Sum.inr (encode w::(b+1)::acc) ∈
          ((decodeStep h t).eval (encode (b::w)::acc)).map
            (fun v => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) := by
        rw [decodeStep_cons h t hh ht]
        simp
      rw [fix_eval_fwd _ _ _ hs]
      change (decoder h t).eval _ = _
      rw [ih]
      simp [List.reverse_cons,List.map_append,List.append_assoc]

 theorem unary_code {f : ℕ → ℕ} (hf : Computable f) :
    ∃ c : Code, ∀ n l, c.eval (n::l) = Part.some [f n] := by
  obtain ⟨c,hc⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf.partrec)
  refine ⟨.comp c .head,fun n l => ?_⟩
  simp only [eval_comp,Code.head_eval,List.headI_cons]
  rw [show (pure [n] : Part (List ℕ)) = Part.some [n] from rfl,Part.bind_some]
  have he := hc ⟨[n],rfl⟩
  exact he

 theorem exists_wordCode {f : List ℕ →. List ℕ} (hf : Partrec f) :
    ∃ c : Code, ∀ w, c.eval (w.map Nat.succ) = (f w).map (List.map Nat.succ) := by
  obtain ⟨ce,hce⟩ := binary_code
    ((Computable.succ.comp (Primrec₂.natPair.to_comp.comp
      (Primrec.nat_sub.to_comp.comp Computable.snd (Computable.const 1)) Computable.fst)).to₂)
  obtain ⟨ch,hch⟩ := unary_code
    (Computable.succ.comp (Computable.fst.comp (Primrec.unpair.to_comp.comp
      (Primrec.nat_sub.to_comp.comp Computable.id (Computable.const 1)))))
  obtain ⟨ct,hct⟩ := unary_code
    (Computable.snd.comp (Primrec.unpair.to_comp.comp
      (Primrec.nat_sub.to_comp.comp Computable.id (Computable.const 1))))
  let g : ℕ →. ℕ := fun n => (f (Denumerable.ofNat (List ℕ) n).reverse).map
    (fun l => encode l.reverse)
  have hg : Partrec g :=
    (hf.comp (Computable.list_reverse.comp (Computable.ofNat (List ℕ)))).map
      ((Computable.encode.comp Computable.list_reverse).comp Computable.snd).to₂
  obtain ⟨cf,hcf⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.mpr hg)
  refine ⟨.comp (decoder ch ct) (.comp cf (encoder ce)),fun w => ?_⟩
  simp only [eval_comp,encoder_eval ce hce,Part.bind_some]
  rw [hcf ⟨[encode w.reverse],rfl⟩]
  change ((g (encode w.reverse)).map (fun n => [n])).bind (fun v => (decoder ch ct).eval v) = _
  simp only [g,Denumerable.ofNat_encode,List.reverse_reverse]
  apply Part.ext
  intro out
  simp only [Part.mem_bind_iff,Part.mem_map_iff]
  constructor
  · rintro ⟨_,⟨n,⟨l,hl,rfl⟩,rfl⟩,hd⟩
    have he := decoder_eval ch ct hch hct l.reverse []
    simp only [List.reverse_reverse,List.append_nil] at he
    rw [he,Part.mem_some_iff] at hd
    exact ⟨l,hl,hd.symm⟩
  · rintro ⟨l,hl,rfl⟩
    refine ⟨[encode l.reverse],⟨encode l.reverse,⟨l,hl,rfl⟩,rfl⟩,?_⟩
    rw [decoder_eval ch ct hch hct l.reverse []]
    simp

end FiniteAlgebraicEnvelopes.MachineRealization.ListCode

namespace FiniteAlgebraicEnvelopes.MachineRealization

section
open Turing Turing.ToPartrec Turing.PartrecToTM2
open RawTM

namespace FiniteTM2
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq Λ]
omit [DecidableEq Λ] in
 theorem embedCfg_injective (A : Finset Λ) : Function.Injective (embedCfg (Γ := Γ) (σ := σ) A) := by
  rintro ⟨l,v,t⟩ ⟨l',v',t'⟩ h
  have hl := congrArg TM2.Cfg.l h
  have hv := congrArg TM2.Cfg.var h
  have ht := congrArg TM2.Cfg.stk h
  dsimp only [embedCfg] at hl hv ht
  have he := Option.map_injective Subtype.val_injective hl
  cases he
  cases hv
  cases ht
  rfl
end FiniteTM2

 theorem part_map_injective {A B : Type*} {g : A → B} (hg : Function.Injective g) :
    Function.Injective (Part.map g) := by
  intro p q h
  apply Part.ext
  intro a
  constructor <;> intro ha
  · have hh : g a ∈ p.map g := Part.mem_map _ ha
    rw [h] at hh
    obtain ⟨b,hb,he⟩ := (Part.mem_map_iff _).mp hh
    exact (hg he) ▸ hb
  · have hh : g a ∈ q.map g := Part.mem_map _ ha
    rw [←h] at hh
    obtain ⟨b,hb,he⟩ := (Part.mem_map_iff _).mp hh
    exact (hg he) ▸ hb

namespace WordEvaluator
variable {S : Type} [Primcodable S]

 theorem exists_code {f : List S →. List S} (hf : Partrec f) :
    ∃ c : Code, ∀ w, c.eval (numbers w) = (f w).map numbers := by
  let g : List ℕ →. List ℕ := fun ns =>
    (f (ns.filterMap Encodable.decode)).map (List.map Encodable.encode)
  have hg : Partrec g :=
    (hf.comp (Primrec.listFilterMap Primrec.id (Primrec.decode.comp Primrec.snd).to₂).to_comp).map
      ((Primrec.list_map Primrec.id (Primrec.encode.comp Primrec.snd).to₂).to_comp.comp Computable.snd).to₂
  obtain ⟨c,hc⟩ := ListCode.exists_wordCode hg
  refine ⟨c,fun w => ?_⟩
  have hcc := hc (w.map Encodable.encode)
  have hlist : (w.map Encodable.encode).filterMap Encodable.decode = w := by
    induction w <;> simp_all
  change c.eval (w.map (fun s => Encodable.encode s + 1)) =
    (f w).map (fun out => out.map (fun s => Encodable.encode s + 1))
  simpa only [g,hlist,Part.map_map,List.map_map,Function.comp_def,Nat.succ_eq_add_one] using hcc

 theorem exists_finite {f : List S →. List S} (hf : Partrec f) :
    ∃ (Λ : Type) (_ : Fintype Λ) (start : Λ)
      (M : Λ → TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ')),
      ∀ w, StateTransition.eval (TM2.step M) (baseCfg (some start) (trList (numbers w))) =
        (f w).map (fun out => baseCfg none (trList (numbers out))) := by
  obtain ⟨c,hc⟩ := exists_code hf
  let A := codeSupp c Cont'.halt
  let : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  have hs : TM2.Supports tr A := tr_supports c Cont'.halt
  let start : {l // l ∈ A} := ⟨trNormal c Cont'.halt,hs.1⟩
  let M := FiniteTM2.machine tr A hs
  refine ⟨{l // l ∈ A},inferInstance,start,M,fun w => ?_⟩
  apply part_map_injective (FiniteTM2.embedCfg_injective A)
  rw [←FiniteTM2.eval_embed tr A hs]
  change StateTransition.eval (TM2.step tr) (init c (numbers w)) = _
  rw [tr_eval,hc]
  simp only [Part.map_eq_map,Part.map_map]
  rfl

variable [Fintype S]
 noncomputable def bound : ℕ := Finset.univ.sup fun s : S => (trNat (Encodable.encode s + 1)).length
 theorem le_bound (s : S) : (trNat (Encodable.encode s + 1)).length ≤ bound (S := S) :=
  Finset.le_sup (f := fun s : S => (trNat (Encodable.encode s + 1)).length) (Finset.mem_univ s)

 theorem exists_raw {f : List S →. List S} (hf : Partrec f) :
    ∃ (Λ : Type) (_ : Fintype Λ) (M : Λ → TM2.Stmt (fun _ : K' => StackLift.Symbol S) Λ (StackLift.Store S))
      (start : Λ), ∀ w,
      StateTransition.eval (TM2.step M)
        ⟨some start,none,tracks w.reverse []⟩ =
          (f w).map (fun out => ⟨none,none,tracks out.reverse []⟩) := by
  classical
  obtain ⟨Λ,hΛ,start,M,hM⟩ := exists_finite hf
  let : Fintype Λ := hΛ
  refine ⟨StackLift.Label S Λ,inferInstance,machine (bound (S := S)) M start,.pre,fun w => ?_⟩
  exact eval_pre (bound (S := S)) M start le_bound (hM w)

end WordEvaluator
end

open Turing Relation
namespace FiniteTM0
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ]
variable (M : TM0.Machine Γ Λ) (A : Finset Λ) (h : TM0.Supports M (A : Set Λ))
variable [Inhabited {l // l ∈ A}]

def machine : TM0.Machine Γ {l // l ∈ A} := fun q a =>
  (M q.val a).pmap (fun p hp => (⟨p.1,h.2 hp q.property⟩,p.2)) (fun _ hp => hp)

def embed (c : TM0.Cfg Γ {l // l ∈ A}) : TM0.Cfg Γ Λ := ⟨c.q.val,c.Tape⟩

omit [Inhabited Λ] [DecidableEq Λ] [Inhabited {l // l ∈ A}] in
theorem embed_injective : Function.Injective (embed (Γ := Γ) A) := by
  rintro ⟨q,t⟩ ⟨q',t'⟩ he
  have hq : q = q' := Subtype.ext (congrArg TM0.Cfg.q he)
  have ht := congrArg TM0.Cfg.Tape he
  cases hq
  cases ht
  rfl

omit [DecidableEq Λ] in
theorem embed_step (c : TM0.Cfg Γ {l // l ∈ A}) :
    (TM0.step (machine M A h) c).map (embed A) = TM0.step M (embed A c) := by
  rcases c with ⟨q,t⟩
  cases hc : M q.val t.head with
  | none => simp [TM0.step,machine,embed,hc]
  | some p => rcases p with ⟨q',s⟩; cases s <;> simp [TM0.step,machine,embed,hc]

omit [DecidableEq Λ] in
theorem respects : StateTransition.Respects (TM0.step (machine M A h)) (TM0.step M)
    (fun a b => embed A a = b) := by
  apply StateTransition.fun_respects.mpr
  intro a
  have hh := embed_step M A h a
  cases hc : TM0.step (machine M A h) a with
  | none =>
      change TM0.step M (embed A a) = none
      simpa only [hc,Option.map_none] using hh.symm
  | some b =>
      apply TransGen.single
      change TM0.step M (embed A a) = some (embed A b)
      simpa only [hc,Option.map_some] using hh.symm

omit [DecidableEq Λ] in
theorem eval_embed (c : TM0.Cfg Γ {l // l ∈ A}) :
    StateTransition.eval (TM0.step M) (embed A c) =
      (StateTransition.eval (TM0.step (machine M A h)) c).map (embed A) :=
  StateTransition.tr_eval' _ _ _ (respects M A h) c
end FiniteTM0

namespace StackTape
open Turing.PartrecToTM2 StackLift RawTM
variable {S Λ : Type} [Fintype S] [Fintype Λ] [Inhabited Λ]

 def slice (a : S) : ∀ _ : K', Option (Symbol S) := Function.update (fun _ => none) .main (some (.inr a))
 def stackList (w : List S) : ListBlank (∀ _ : K', Option (Symbol S)) := ListBlank.mk (w.map slice)
 def tape (w : List S) : Turing.Tape (TM2to1.Γ' K' (fun _ => Symbol S)) :=
   Turing.Tape.mk' ∅ (TM2to1.addBottom (stackList w))

omit [Fintype S] in
 theorem tracks_proj (w : List S) (k : K') :
   (stackList w).map (Turing.proj k) = ListBlank.mk (((tracks w.reverse [] k).map some).reverse) := by
  cases k <;> simp [stackList,slice,tracks,Turing.proj,ListBlank.map_mk,List.map_reverse,List.map_map,
    Function.comp_def] <;> exact Quotient.sound (Or.inr ⟨w.length,rfl⟩)

omit [Fintype S] [Fintype Λ] [Inhabited Λ] in
 theorem trCfg (w : List S) (l : Option Λ) (v : Store S) :
   TM2to1.TrCfg (⟨l,v,tracks w.reverse []⟩ : TM2.Cfg (fun _ : K' => Symbol S) Λ (Store S))
     ⟨l.map .normal,v,tape w⟩ := .mk (stackList w) (tracks_proj w)

omit [Fintype S] in
 theorem stackList_unique (w : List S) (L : ListBlank (∀ _ : K', Option (Symbol S)))
    (hL : ∀ k, L.map (Turing.proj k) = ListBlank.mk (((tracks w.reverse [] k).map some).reverse)) :
    L = stackList w := by
  apply ListBlank.ext
  intro n
  funext k
  have he := congrArg (fun l => ListBlank.nth l n) ((hL k).trans (tracks_proj w k).symm)
  simpa only [ListBlank.nth_map,Turing.proj,PointedMap.mk_val] using he

omit [Fintype S] [Fintype Λ] [Inhabited Λ] in
 theorem trCfg_unique (w : List S) (l : Option Λ) (v : Store S)
    {c : TM1.Cfg (TM2to1.Γ' K' (fun _ => Symbol S)) (TM2to1.Λ' K' (fun _ => Symbol S) Λ (Store S)) (Store S)}
    (hc : TM2to1.TrCfg (⟨l,v,tracks w.reverse []⟩ : TM2.Cfg (fun _ : K' => Symbol S) Λ (Store S)) c) :
    c = ⟨l.map .normal,v,tape w⟩ := by
  cases hc with
  | mk L hL => rw [stackList_unique w L hL]; rfl

 variable (M : Λ → TM2.Stmt (fun _ : K' => Symbol S) Λ (Store S))
omit [Fintype S] [Fintype Λ] [Inhabited Λ] in
 theorem eval_tape {f : List S →. List S} (start : Λ)
   (hM : ∀ w, StateTransition.eval (TM2.step M) ⟨some start,none,tracks w.reverse []⟩ =
      (f w).map (fun out => ⟨none,none,tracks out.reverse []⟩)) (w : List S) :
   StateTransition.eval (TM1.step (TM2to1.tr M)) ⟨some (.normal start),none,tape w⟩ =
     (f w).map (fun out => ⟨none,none,tape out⟩) := by
  apply Part.ext
  intro c
  constructor
  · intro hc
    obtain ⟨b,hbc,hb⟩ := StateTransition.tr_eval_rev (TM2to1.tr_respects M) (trCfg w (some start) none) hc
    rw [hM] at hb
    obtain ⟨out,hout,rfl⟩ := (Part.mem_map_iff _).mp hb
    rw [trCfg_unique out none none hbc]
    exact Part.mem_map _ hout
  · intro hc
    obtain ⟨out,hout,rfl⟩ := (Part.mem_map_iff _).mp hc
    have hb : (⟨none,none,tracks out.reverse []⟩ : TM2.Cfg (fun _ : K' => Symbol S) Λ (Store S)) ∈
       StateTransition.eval (TM2.step M) ⟨some start,none,tracks w.reverse []⟩ := by
      rw [hM]; exact Part.mem_map _ hout
    obtain ⟨b,hb,hbe⟩ := StateTransition.tr_eval (TM2to1.tr_respects M) (trCfg w (some start) none) hb
    simpa only [trCfg_unique out none none hb,Option.map_none,Option.map_some] using hbe

omit [Fintype S] [Fintype Λ] in
 theorem eval_post {f : List S →. List S} (start : Λ)
   (hM : ∀ w, StateTransition.eval (TM2.step M) ⟨some start,none,tracks w.reverse []⟩ =
      (f w).map (fun out => ⟨none,none,tracks out.reverse []⟩)) (w : List S) :
   StateTransition.eval (TM0.step (TM1to0.tr (TM2to1.tr M)))
     (TM1to0.trCfg (TM2to1.tr M) ⟨some (.normal start),none,tape w⟩) =
     (f w).map (fun out => (⟨(none,none),tape out⟩ : TM0.Cfg _ _)) := by
   rw [StateTransition.tr_eval' _ _ _ (TM1to0.tr_respects (TM2to1.tr M)),eval_tape M start hM]
   simp only [Part.map_eq_map,Part.map_map]
   rfl

end StackTape

namespace WordEvaluator
open Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S : Type} [Fintype S] [Primcodable S]
 theorem exists_tape {f : List S →. List S} (hf : Partrec f) :
   ∃ (Λ : Type) (_ : Fintype Λ) (_ : Inhabited Λ)
     (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start stop : Λ),
     ∀ w, StateTransition.eval (TM0.step M) ⟨start,tape w⟩ =
       (f w).map (fun out => ⟨stop,tape out⟩) := by
  classical
  obtain ⟨Λ,hΛ,M,start,hM⟩ := exists_raw hf
  let : Fintype Λ := hΛ
  let : Inhabited Λ := ⟨start⟩
  let N := TM2to1.tr M
  let P := TM1to0.tr N
  let B := TM2to1.trSupp M Finset.univ
  have hU : TM2.Supports M Finset.univ := by
    refine ⟨Finset.mem_univ _,fun q _ => ?_⟩
    induction M q <;> simp_all [TM2.SupportsStmt]
  have hB : TM1.Supports N B := TM2to1.tr_supports M hU
  let C := TM1to0.trStmts N B
  have hC : TM0.Supports P (C : Set _) := TM1to0.tr_supports N hB
  let : Inhabited {l // l ∈ C} := ⟨⟨default,hC.1⟩⟩
  have hs : (none,none) ∈ C := by
    change (none,none) ∈ (TM1.stmts N B) ×ˢ (Finset.univ : Finset (Store S))
    exact Finset.mem_product.mpr ⟨Finset.none_mem_insertNone,Finset.mem_univ _⟩
  refine ⟨{l // l ∈ C},inferInstance,inferInstance,FiniteTM0.machine P C hC,default,⟨(none,none),hs⟩,fun w => ?_⟩
  apply part_map_injective (FiniteTM0.embed_injective C)
  rw [←FiniteTM0.eval_embed P C hC]
  change StateTransition.eval (TM0.step P) (TM1to0.trCfg N ⟨some (.normal start),none,tape w⟩) = _
  rw [eval_post M start hM]
  simp only [Part.map_map]
  rfl

end WordEvaluator
end FiniteAlgebraicEnvelopes.MachineRealization

end OAI
