import Mathlib
import OAI.Combinatorics.MatchingCount.Probability.Variance
import OAI.Combinatorics.MatchingCount.Arithmetic.PostAddition
import OAI.Combinatorics.MatchingCount.Arithmetic.PostComparison

namespace OAI

namespace MatchingFPRAS.StackWords
open Turing

lemma encoded_length {K : Type*} {Γ : K → Type*} {w : ℕ}
    (enc : TM2to1.Γ' K Γ → List.Vector Bool w) (S : ∀ k,List (Γ k)) (H : ℕ) :
    (encoded enc S H).length=w*(H-1+1) := by
  unfold encoded FixedAlphabetCompiler.word
  rw [List.length_map,FixedEncoding.bitsWord_length]
  congr 1
  change ((rows S H).tail.map (fun a=>(false,a))).length+1=H-1+1
  rw [List.length_map,List.length_tail]
  simp only [rows,List.length_ofFn]
end MatchingFPRAS.StackWords
namespace MatchingFPRAS.PostAddition
lemma input_length (A B : List Bool) :
    (input A B).length=Fintype.card Alphabet*(A.length+B.length-1+1) :=
  StackWords.encoded_length _ _ _
lemma input_length_bounds (A B : List Bool) :
    A.length+B.length≤(input A B).length ∧ 1≤(input A B).length := by
  have hw : 1≤Fintype.card Alphabet := Fintype.card_pos
  have h := Nat.mul_le_mul_right (A.length+B.length-1+1) hw
  rw [one_mul,←input_length A B] at h
  omega
lemma bit_time_bound (A B : List Bool) :
    steps A B ≤ (100*overhead+2)*(input A B).length^2 := by
  obtain ⟨hs,hp⟩:=input_length_bounds A B
  have hc : 1+6*(A.length+B.length+3*(A.length+B.length+1)+1)≤25*(A.length+B.length+1) := by omega
  have ht : steps A B≤25*overhead*(A.length+B.length+1)^2+2 := by
    unfold steps
    calc
      _ ≤ overhead*((A.length+B.length+1)*(25*(A.length+B.length+1)))+2 := by gcongr
      _ = _ := by ring
  have hsq : (A.length+B.length+1)^2≤4*(input A B).length^2 := by nlinarith
  have hh:=Nat.mul_le_mul_left (25*overhead) hsq
  have hh' : 1≤(input A B).length^2 := by nlinarith
  nlinarith
end MatchingFPRAS.PostAddition
namespace MatchingFPRAS.PostComparison
lemma input_length (A B : List Bool) :
    (input A B).length=Fintype.card Alphabet*(A.length+B.length-1+1) :=
  StackWords.encoded_length _ _ _
lemma input_length_bounds (A B : List Bool) :
    A.length+B.length≤(input A B).length ∧ 1≤(input A B).length := by
  have hw : 1≤Fintype.card Alphabet := Fintype.card_pos
  have h := Nat.mul_le_mul_right (A.length+B.length-1+1) hw
  rw [one_mul,←input_length A B] at h
  omega
lemma bit_time_bound (A B : List Bool) :
    steps A B ≤ (164*overhead+2)*(input A B).length^2 := by
  obtain ⟨hs,hp⟩:=input_length_bounds A B
  have hc : 1+8*(A.length+B.length+4*(A.length+B.length+1)+1)≤41*(A.length+B.length+1) := by omega
  have ht : steps A B≤41*overhead*(A.length+B.length+1)^2+2 := by
    unfold steps
    calc
      _ ≤ overhead*((A.length+B.length+1)*(41*(A.length+B.length+1)))+2 := by gcongr
      _ = _ := by ring
  have hsq : (A.length+B.length+1)^2≤4*(input A B).length^2 := by nlinarith
  have hh:=Nat.mul_le_mul_left (41*overhead) hsq
  have hh' : 1≤(input A B).length^2 := by nlinarith
  nlinarith
end MatchingFPRAS.PostComparison

namespace MatchingFPRAS.StackComposition
open Turing MachineCost

variable {K Λ P σ : Type*} {Γ : K → Type*} [DecidableEq K]
def relabel (f : Λ → P) (h : Option P) : TM2.Stmt Γ Λ σ → TM2.Stmt Γ P σ
  | .push k a q => .push k a (relabel f h q)
  | .peek k a q => .peek k a (relabel f h q)
  | .pop k a q => .pop k a (relabel f h q)
  | .load a q => .load a (relabel f h q)
  | .branch p q r => .branch p (relabel f h q) (relabel f h r)
  | .goto l => .goto (fun a=>f (l a))
  | .halt => match h with | none=>.halt | some k=>.goto (fun _=>k)
def mapCfg (f : Λ → P) (h : Option P) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ P σ :=
  ⟨c.l.bind (fun l=>some (f l)) |>.or h,c.var,c.stk⟩
omit [DecidableEq K] in
lemma mapCfg_some (f : Λ → P) (h : Option P) (l : Λ) (v : σ) (S : ∀ k,List (Γ k)) :
    mapCfg f h ⟨some l,v,S⟩=⟨some (f l),v,S⟩ := rfl
omit [DecidableEq K] in
lemma mapCfg_none (f : Λ → P) (h : Option P) (v : σ) (S : ∀ k,List (Γ k)) :
    mapCfg f h ⟨none,v,S⟩=⟨h,v,S⟩ := rfl
lemma relabel_eval (f : Λ → P) (h : Option P) (q : TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k,List (Γ k)) :
    TM2.stepAux (relabel f h q) v S=mapCfg f h (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k a q ih => exact ih v _
  | peek k a q ih => exact ih _ S
  | pop k a q ih => exact ih _ _
  | load a q ih => exact ih (a v) S
  | branch p q r ihq ihr =>
    cases hp:p v <;> simp only [relabel,TM2.stepAux,hp,Bool.cond_false,Bool.cond_true] <;>
      first | apply ihr | apply ihq
  | goto l => rfl
  | halt => cases h <;> rfl
omit [DecidableEq K] in
lemma relabel_accesses (f : Λ → P) (h : Option P) (q : TM2.Stmt Γ Λ σ) :
    StackCost.accesses (relabel f h q)=StackCost.accesses q := by
  induction q with
  | push k a q ih | peek k a q ih | pop k a q ih | load a q ih =>
    simp only [relabel,StackCost.accesses,ih]
  | branch p q r ihq ihr => simp only [relabel,StackCost.accesses,ihq,ihr]
  | goto l => rfl
  | halt => cases h <;> rfl
lemma run_halted (M : Λ → TM2.Stmt Γ Λ σ) (n : ℕ)
    (v : σ) (S : ∀ k,List (Γ k)) :
    MachineCost.run (TM2.step M) n ⟨none,v,S⟩=⟨none,v,S⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [MachineCost.run,advance,TM2.step,Option.getD_none] using ih
lemma run_relabel_to_halt (M : Λ → TM2.Stmt Γ Λ σ) (N : P → TM2.Stmt Γ P σ)
    (f : Λ → P) (h : Option P) (hN : ∀ l,N (f l)=relabel f h (M l))
    (n : ℕ) (c : TM2.Cfg Γ Λ σ) (v : σ) (S : ∀ k,List (Γ k))
    (he : MachineCost.run (TM2.step M) n c=⟨none,v,S⟩) :
    ∃ k≤n,MachineCost.run (TM2.step N) k (mapCfg f h c)=⟨h,v,S⟩ := by
  induction n generalizing c with
  | zero =>
    have hc : c=⟨none,v,S⟩:=he
    subst c
    exact ⟨0,le_rfl,rfl⟩
  | succ n ih =>
    rcases c with ⟨l,v',S'⟩
    cases l with
    | none =>
      rw [run_halted] at he
      cases he
      exact ⟨0,Nat.zero_le _,rfl⟩
    | some l =>
      have he' : MachineCost.run (TM2.step M) n (TM2.stepAux (M l) v' S')=⟨none,v,S⟩ := he
      obtain ⟨k,hk,hh⟩:=ih _ he'
      refine ⟨k+1,by omega,?_⟩
      rw [MachineCost.run,mapCfg_some]
      have hs : advance (TM2.step N) ⟨some (f l),v',S'⟩=
          mapCfg f h (TM2.stepAux (M l) v' S') := by
        simp only [advance,TM2.step,Option.getD_some,hN,relabel_eval]
      rw [hs,hh]
variable [Inhabited Λ] [Inhabited P]
def sequence (M : Λ → TM2.Stmt Γ Λ σ) (N : P → TM2.Stmt Γ P σ) :
    Λ⊕P → TM2.Stmt Γ (Λ⊕P) σ
  | .inl l => relabel Sum.inl (some (Sum.inr default)) (M l)
  | .inr k => relabel Sum.inr none (N k)
omit [Inhabited Λ] in
lemma sequence_run (M : Λ → TM2.Stmt Γ Λ σ) (N : P → TM2.Stmt Γ P σ)
    (c : TM2.Cfg Γ Λ σ) (m n : ℕ) (v v' : σ) (S S' : ∀ k,List (Γ k))
    (hM : MachineCost.run (TM2.step M) m c=⟨none,v,S⟩)
    (hN : MachineCost.run (TM2.step N) n ⟨some default,v,S⟩=⟨none,v',S'⟩) :
    ∃ k ≤ m+n,MachineCost.run (TM2.step (sequence M N)) k
      (mapCfg Sum.inl (some (Sum.inr default)) c)=⟨none,v',S'⟩ := by
  obtain ⟨i,hi,hei⟩:=run_relabel_to_halt M (sequence M N) Sum.inl
    (some (Sum.inr default)) (fun _=>rfl) m c v S hM
  obtain ⟨j,hj,hej⟩:=run_relabel_to_halt N (sequence M N) Sum.inr
    none (fun _=>rfl) n ⟨some default,v,S⟩ v' S' hN
  refine ⟨i+j,by omega,?_⟩
  rw [run_add,hei]
  exact hej
omit [DecidableEq K] [Inhabited Λ] in
lemma sequence_accesses (M : Λ → TM2.Stmt Γ Λ σ) (N : P → TM2.Stmt Γ P σ)
    (A B : ℕ) (hM : ∀ l,StackCost.accesses (M l)≤A) (hN : ∀ l,StackCost.accesses (N l)≤B)
    (l : Λ⊕P) : StackCost.accesses (sequence M N l) ≤ max A B := by
  cases l with
  | inl l => exact (by rw [sequence,relabel_accesses]; exact (hM l).trans (le_max_left _ _))
  | inr l => exact (by rw [sequence,relabel_accesses]; exact (hN l).trans (le_max_right _ _))
omit [DecidableEq K] in
lemma supports_univ [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ) : TM2.Supports M Finset.univ := by
  constructor
  · simp
  · intro l _
    induction M l with
    | push k a q ih | peek k a q ih | pop k a q ih | load a q ih => exact ih
    | branch p q r ihq ihr => exact ⟨ihq,ihr⟩
    | goto l => simp [TM2.SupportsStmt]
    | halt => trivial

open Turing MachineCost

variable {K Λ σ : Type*} {Γ : K → Type*} [DecidableEq K] [Inhabited Λ]
def loop (M : Λ → TM2.Stmt Γ Λ σ) (p : σ → Bool) :
    Unit ⊕ Λ → TM2.Stmt Γ (Unit ⊕ Λ) σ
  | .inl _ => .branch p (.goto (fun _ => .inr default)) .halt
  | .inr l => relabel Sum.inr (some (Sum.inl ())) (M l)
lemma loop_stop (M : Λ → TM2.Stmt Γ Λ σ) (p : σ → Bool)
    (v : σ) (S : ∀ k,List (Γ k)) (hp : p v=false) :
    MachineCost.run (TM2.step (loop M p)) 1 ⟨some (.inl ()),v,S⟩=⟨none,v,S⟩ := by
  simp [MachineCost.run,advance,TM2.step,loop,TM2.stepAux,hp]
lemma loop_once (M : Λ → TM2.Stmt Γ Λ σ) (p : σ → Bool)
    (m : ℕ) (v v' : σ) (S S' : ∀ k,List (Γ k)) (hp : p v=true)
    (hM : MachineCost.run (TM2.step M) m ⟨some default,v,S⟩=⟨none,v',S'⟩) :
    ∃ k ≤ m+1,MachineCost.run (TM2.step (loop M p)) k
      ⟨some (.inl ()),v,S⟩=⟨some (.inl ()),v',S'⟩ := by
  obtain ⟨k,hk,he⟩:=run_relabel_to_halt M (loop M p) Sum.inr
    (some (Sum.inl ())) (fun _=>rfl) m ⟨some default,v,S⟩ v' S' hM
  refine ⟨k+1,by omega,?_⟩
  simpa [MachineCost.run,advance,TM2.step,loop,TM2.stepAux,hp,mapCfg] using he
omit [DecidableEq K] in
lemma loop_accesses (M : Λ → TM2.Stmt Γ Λ σ) (p : σ → Bool) (a : ℕ)
    (hM : ∀ l,StackCost.accesses (M l)≤a) (l : Unit⊕Λ) :
    StackCost.accesses (loop M p l)≤a := by
  cases l with
  | inl l => simp [loop,StackCost.accesses]
  | inr l => simpa [loop,relabel_accesses] using hM l

lemma loop_bounded (M : Λ → TM2.Stmt Γ Λ σ) (p : σ → Bool)
    (I : ℕ → σ → (∀ k,List (Γ k)) → Prop) (b : ℕ)
    (hz : ∀ v S,I 0 v S → p v=false)
    (hn : ∀ n v S,I (n+1) v S → p v=true ∧
      ∃ m≤b,∃ v' S',I n v' S' ∧
        MachineCost.run (TM2.step M) m ⟨some default,v,S⟩=⟨none,v',S'⟩)
    (n : ℕ) (v : σ) (S : ∀ k,List (Γ k)) (hI : I n v S) :
    ∃ k≤n*(b+1)+1,∃ v' S',I 0 v' S' ∧
      MachineCost.run (TM2.step (loop M p)) k ⟨some (.inl ()),v,S⟩=⟨none,v',S'⟩ := by
  induction n generalizing v S with
  | zero => exact ⟨1,by simp,v,S,hI,loop_stop M p v S (hz _ _ hI)⟩
  | succ n ih =>
    obtain ⟨hp,m,hm,w,T,hT,he⟩:=hn n v S hI
    obtain ⟨j,hj,hjrun⟩:=loop_once M p m v w S T hp he
    obtain ⟨k,hk,w',T',hT',hkrun⟩:=ih w T hT
    refine ⟨j+k,?_,w',T',hT',?_⟩
    · calc
        j+k ≤ (b+1)+(n*(b+1)+1) := by omega
        _ = (n+1)*(b+1)+1 := by ring
    · rw [run_add,hjrun,hkrun]
end MatchingFPRAS.StackComposition

namespace MatchingFPRAS.StackReverse
open Turing MachineCost StackAddition

abbrev S := Option Bool
abbrev Γ := fun _ : Fin 3 => Bool
def program : Unit → TM2.Stmt Γ Unit S := fun _ =>
  .pop 0 (fun _ a=>a)
    (.branch Option.isNone (.load (fun _=>none) .halt)
      (.push 1 (fun v=>v.getD false) (.goto (fun _=>()))))
def cfg (l : Option Unit) (A B C : List Bool) (v : S) : TM2.Cfg Γ Unit S :=
  ⟨l,v,stackData A B C⟩
lemma next_empty (B C : List Bool) (v : S) :
    advance (TM2.step program) (cfg (some ()) [] B C v)=cfg none [] B C none := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg,update_zero]
lemma next_cons (a : Bool) (A B C : List Bool) (v : S) :
    advance (TM2.step program) (cfg (some ()) (a::A) B C v)=
      cfg (some ()) A (a::B) C (some a) := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg,update_zero,update_one]
theorem run_reverse (A B C : List Bool) (v : S) :
    MachineCost.run (TM2.step program) (A.length+1) (cfg (some ()) A B C v)=
      cfg none [] (A.reverse++B) C none := by
  induction A generalizing B v with
  | nil => simpa only [List.length_nil,List.reverse_nil,List.nil_append,MachineCost.run] using next_empty B C v
  | cons a A ih =>
    rw [List.length_cons,show A.length+1+1=(A.length+1)+1 by rfl,MachineCost.run,next_cons,ih]
    simp [List.reverse_cons,List.append_assoc]
lemma accesses_bound (l : Unit) : StackCost.accesses (program l)≤2 := by
  simp [program,StackCost.accesses]
lemma finite_support : TM2.Supports program Finset.univ := by
  constructor
  · simp
  · intro l _
    simp [program,TM2.SupportsStmt]
lemma reverse_addition_numerals (m n : ℕ) :
    value ((addDigits false m.bits n.bits).reverse.reverse++[]) = m+n := by
  simpa only [List.reverse_reverse,List.append_nil] using addition_numerals m n
end MatchingFPRAS.StackReverse

namespace MatchingFPRAS.PostReverse
open Turing StackReverse StackAddition

abbrev Alphabet := TM2to1.Γ' (Fin 3) (fun _=>Bool)
noncomputable def machine : RandomMachine :=
  StackWords.compiled (FixedEncoding.enc Alphabet) (FixedEncoding.dec Alphabet)
    StackReverse.program Finset.univ StackReverse.finite_support
noncomputable def overhead : ℕ :=
  StackWords.cost (FixedEncoding.enc Alphabet) (FixedEncoding.dec Alphabet)
    StackReverse.program Finset.univ
noncomputable def input (A B : List Bool) : List Symbol :=
  StackWords.encoded (FixedEncoding.enc Alphabet) (stackData A B []) (A.length+B.length)
noncomputable def output (A B : List Bool) : List Symbol :=
  StackWords.encoded (FixedEncoding.enc Alphabet) (stackData [] (A.reverse++B) []) (A.length+B.length)
noncomputable def steps (A B : List Bool) : ℕ :=
  overhead*((A.length+B.length+1)*(12*(A.length+B.length)+13))+2
theorem computes (A B : List Bool) (t : ℕ) (ht : steps A B≤t) (bits : Fin t → Bool) :
    (run machine (input A B) bits).state=none ∧
    (run machine (input A B) bits).tape.right₀=ListBlank.mk (output A B) := by
  have h₀ : StackCost.StackBound (stackData A B []) (A.length+B.length) := by
    intro i
    fin_cases i <;> simp [stackData]
  have he : MachineCost.run (TM2.step StackReverse.program) (A.length+1)
      ⟨some (default : Unit),(default : StackReverse.S),stackData A B []⟩=
        StackReverse.cfg none [] (A.reverse++B) [] none := run_reverse A B [] none
  have hh : (MachineCost.run (TM2.step StackReverse.program) (A.length+1)
      ⟨some (default : Unit),(default : StackReverse.S),stackData A B []⟩).l=none := by rw [he]; rfl
  have ho : StackCost.StackBound (MachineCost.run (TM2.step StackReverse.program) (A.length+1)
      ⟨some (default : Unit),(default : StackReverse.S),stackData A B []⟩).stk (A.length+B.length) := by
    rw [he]
    intro i
    fin_cases i <;> simp [StackReverse.cfg,stackData]
  have htime : StackWords.cost (FixedEncoding.enc Alphabet) (FixedEncoding.dec Alphabet)
      StackReverse.program Finset.univ*((A.length+1)*(1+2*2*(A.length+B.length+(A.length+1)*2+1)))+2≤t := by
    apply le_trans _ ht
    unfold steps overhead
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.mul_le_mul <;> omega
  have hc:=StackWords.compiled_execution (FixedEncoding.enc Alphabet)
    (FixedEncoding.dec Alphabet) (FixedEncoding.blank Alphabet) (FixedEncoding.left_inverse Alphabet)
    StackReverse.program Finset.univ StackReverse.finite_support 2 StackReverse.accesses_bound
    (stackData A B []) (A.length+B.length) h₀ (A.length+1) (A.length+B.length) hh ho t htime bits
  change (run machine (input A B) bits).state=none ∧
    (run machine (input A B) bits).tape.right₀=ListBlank.mk
      (StackWords.encoded (FixedEncoding.enc Alphabet)
        (MachineCost.run (TM2.step StackReverse.program) (A.length+1)
          ⟨some (default : Unit),(default : StackReverse.S),stackData A B []⟩).stk
          (A.length+B.length)) at hc
  rw [he] at hc
  exact hc
lemma time_quadratic (A B : List Bool) :
    steps A B=overhead*(12*(A.length+B.length)^2+25*(A.length+B.length)+13)+2 := by
  unfold steps
  congr 2
  ring
end MatchingFPRAS.PostReverse

namespace MatchingFPRAS.ForwardAddition
open Turing MachineCost StackAddition

local instance initialControl : Inhabited (Bool⊕Unit) := ⟨.inl false⟩
abbrev Γ := fun _ : Fin 3 => Bool
def reverseProgram : Unit → TM2.Stmt Γ Unit Store := fun _ =>
  .pop 2 (fun v a=>(a,v.2))
    (.branch (fun v=>v.1.isNone) (.load (fun _=>default) .halt)
      (.push 0 (fun v=>v.1.getD false) (.goto (fun _=>()))))
def rcfg (l : Option Unit) (A B C : List Bool) (v : Store) : TM2.Cfg Γ Unit Store :=
  ⟨l,v,stackData A B C⟩
lemma next_empty (A B : List Bool) (v : Store) :
    advance (TM2.step reverseProgram) (rcfg (some ()) A B [] v)=rcfg none A B [] default := by
  simp [advance,TM2.step,reverseProgram,TM2.stepAux,rcfg,update_two]
lemma next_cons (a : Bool) (A B C : List Bool) (v : Store) :
    advance (TM2.step reverseProgram) (rcfg (some ()) A B (a::C) v)=
      rcfg (some ()) (a::A) B C (some a,v.2) := by
  simp [advance,TM2.step,reverseProgram,TM2.stepAux,rcfg,update_zero,update_two]
lemma run_reverse (A B C : List Bool) (v : Store) :
    MachineCost.run (TM2.step reverseProgram) (C.length+1) (rcfg (some ()) A B C v)=
      rcfg none (C.reverse++A) B [] default := by
  induction C generalizing A v with
  | nil => simpa only [List.length_nil,List.reverse_nil,List.nil_append,MachineCost.run] using next_empty A B v
  | cons c C ih =>
    rw [List.length_cons,MachineCost.run,next_cons,ih]
    simp [List.reverse_cons,List.append_assoc]
def program : Bool⊕Unit → TM2.Stmt Γ (Bool⊕Unit) Store :=
  StackComposition.sequence StackAddition.program reverseProgram
lemma run_add (A B : List Bool) :
    ∃ k≤2*(A.length+B.length)+3,
      MachineCost.run (TM2.step program) k ⟨some default,default,stackData A B []⟩=
        ⟨none,default,stackData (addDigits false A B) [] []⟩ := by
  obtain ⟨n,hn,he⟩:=run_addition A B [] false default
  have he' : MachineCost.run (TM2.step StackAddition.program) n
      (cfg (some false) A B [] default)=cfg none [] [] (addDigits false A B).reverse default := by
    simpa only [List.append_nil] using he
  have hr := run_reverse [] [] (addDigits false A B).reverse default
  have hr' : MachineCost.run (TM2.step reverseProgram) ((addDigits false A B).length+1)
      ⟨some default,default,stackData [] [] (addDigits false A B).reverse⟩=
      ⟨none,default,stackData (addDigits false A B) [] []⟩ := by
    simpa only [rcfg,List.length_reverse,List.reverse_reverse,List.append_nil] using hr
  obtain ⟨k,hk,hkrun⟩:=StackComposition.sequence_run StackAddition.program reverseProgram
    (cfg (some false) A B [] default) n ((addDigits false A B).length+1)
    (default : Store) (default : Store) (stackData [] [] (addDigits false A B).reverse)
      (stackData (addDigits false A B) [] []) he' hr'
  refine ⟨k,?_,?_⟩
  · have hl:=addDigits_length A B false
    omega
  · exact hkrun
lemma accesses_bound (l : Bool⊕Unit) : StackCost.accesses (program l)≤3 := by
  apply StackComposition.sequence_accesses StackAddition.program reverseProgram 3 3 StackAddition.accesses_bound
  intro k
  simp [reverseProgram,StackCost.accesses]
lemma support : TM2.Supports program Finset.univ := StackComposition.supports_univ program
lemma result_value (m n : ℕ) : value (addDigits false m.bits n.bits)=m+n := addition_numerals m n
end MatchingFPRAS.ForwardAddition

namespace MatchingFPRAS.PostForwardAddition
open Turing StackAddition ForwardAddition

local instance initialControl : Inhabited (Bool⊕Unit) := ⟨.inl false⟩
abbrev Alphabet := TM2to1.Γ' (Fin 3) (fun _=>Bool)
lemma support : TM2.Supports ForwardAddition.program Finset.univ :=
  StackComposition.supports_univ ForwardAddition.program
noncomputable def machine : RandomMachine :=
  StackWords.compiled (FixedEncoding.enc Alphabet) (FixedEncoding.dec Alphabet)
    ForwardAddition.program Finset.univ support
noncomputable def overhead : ℕ :=
  StackWords.cost (FixedEncoding.enc Alphabet) (FixedEncoding.dec Alphabet)
    ForwardAddition.program Finset.univ
noncomputable def input (A B : List Bool) : List Symbol :=
  StackWords.encoded (FixedEncoding.enc Alphabet) (stackData A B []) (A.length+B.length)
noncomputable def output (A B : List Bool) : List Symbol :=
  StackWords.encoded (FixedEncoding.enc Alphabet)
    (stackData (addDigits false A B) [] []) (A.length+B.length+1)
noncomputable def steps (A B : List Bool) : ℕ :=
  overhead*((2*(A.length+B.length)+3)*(42*(A.length+B.length)+61))+2
theorem computes (A B : List Bool) (t : ℕ) (ht : steps A B≤t) (bits : Fin t → Bool) :
    (run machine (input A B) bits).state=none ∧
    (run machine (input A B) bits).tape.right₀=ListBlank.mk (output A B) := by
  obtain ⟨n,hn,he⟩:=ForwardAddition.run_add A B
  have h₀ : StackCost.StackBound (stackData A B []) (A.length+B.length) := by
    intro i
    fin_cases i <;> simp [stackData]
  have hh : (MachineCost.run (TM2.step ForwardAddition.program) n
      ⟨some (default : Bool⊕Unit),(default : Store),stackData A B []⟩).l=none := by rw [he]
  have ho : StackCost.StackBound (MachineCost.run (TM2.step ForwardAddition.program) n
      ⟨some (default : Bool⊕Unit),(default : Store),stackData A B []⟩).stk (A.length+B.length+1) := by
    rw [he]
    intro i
    have hl:=addDigits_length A B false
    fin_cases i <;> simp [stackData]
    omega
  have htime : StackWords.cost (FixedEncoding.enc Alphabet) (FixedEncoding.dec Alphabet)
      ForwardAddition.program Finset.univ*(n*(1+2*3*(A.length+B.length+n*3+1)))+2≤t := by
    apply le_trans _ ht
    unfold steps overhead
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.mul_le_mul hn
    omega
  have hc:=StackWords.compiled_execution (FixedEncoding.enc Alphabet)
    (FixedEncoding.dec Alphabet) (FixedEncoding.blank Alphabet) (FixedEncoding.left_inverse Alphabet)
    ForwardAddition.program Finset.univ support 3 ForwardAddition.accesses_bound
    (stackData A B []) (A.length+B.length) h₀ n (A.length+B.length+1) hh ho t htime bits
  change (run machine (input A B) bits).state=none ∧
    (run machine (input A B) bits).tape.right₀=ListBlank.mk
      (StackWords.encoded (FixedEncoding.enc Alphabet)
        (MachineCost.run (TM2.step ForwardAddition.program) n
          ⟨some (default : Bool⊕Unit),(default : Store),stackData A B []⟩).stk
          (A.length+B.length+1)) at hc
  rw [he] at hc
  exact hc
lemma time_quadratic (A B : List Bool) :
    steps A B=overhead*(84*(A.length+B.length)^2+248*(A.length+B.length)+183)+2 := by
  unfold steps
  congr 2
  ring
end MatchingFPRAS.PostForwardAddition

namespace MatchingFPRAS.PostReverse
lemma input_length (A B : List Bool) :
    (input A B).length=Fintype.card Alphabet*(A.length+B.length-1+1) :=
  StackWords.encoded_length _ _ _
lemma input_length_bounds (A B : List Bool) :
    A.length+B.length≤(input A B).length ∧ 1≤(input A B).length := by
  have hw : 1≤Fintype.card Alphabet := Fintype.card_pos
  have h := Nat.mul_le_mul_right (A.length+B.length-1+1) hw
  rw [one_mul,←input_length A B] at h
  omega
lemma bit_time_bound (A B : List Bool) :
    steps A B≤(52*overhead+2)*(input A B).length^2 := by
  obtain ⟨hs,hp⟩:=input_length_bounds A B
  have ht : steps A B≤13*overhead*(A.length+B.length+1)^2+2 := by
    unfold steps
    calc
      _ ≤ overhead*((A.length+B.length+1)*(13*(A.length+B.length+1)))+2 := by gcongr; omega
      _ = _ := by ring
  have hsq : (A.length+B.length+1)^2≤4*(input A B).length^2 := by nlinarith
  have hh:=Nat.mul_le_mul_left (13*overhead) hsq
  have hh' : 1≤(input A B).length^2 := by nlinarith
  nlinarith
end MatchingFPRAS.PostReverse
namespace MatchingFPRAS.PostForwardAddition
lemma input_length (A B : List Bool) :
    (input A B).length=Fintype.card Alphabet*(A.length+B.length-1+1) :=
  StackWords.encoded_length _ _ _
lemma input_length_bounds (A B : List Bool) :
    A.length+B.length≤(input A B).length ∧ 1≤(input A B).length := by
  have hw : 1≤Fintype.card Alphabet := Fintype.card_pos
  have h := Nat.mul_le_mul_right (A.length+B.length-1+1) hw
  rw [one_mul,←input_length A B] at h
  omega
lemma bit_time_bound (A B : List Bool) :
    steps A B≤(732*overhead+2)*(input A B).length^2 := by
  obtain ⟨hs,hp⟩:=input_length_bounds A B
  have ht : steps A B≤183*overhead*(A.length+B.length+1)^2+2 := by
    unfold steps
    calc
      _ ≤ overhead*((3*(A.length+B.length+1))*(61*(A.length+B.length+1)))+2 := by gcongr <;> omega
      _ = _ := by ring
  have hsq : (A.length+B.length+1)^2≤4*(input A B).length^2 := by nlinarith
  have hh:=Nat.mul_le_mul_left (183*overhead) hsq
  have hh' : 1≤(input A B).length^2 := by nlinarith
  nlinarith
end MatchingFPRAS.PostForwardAddition

end OAI
