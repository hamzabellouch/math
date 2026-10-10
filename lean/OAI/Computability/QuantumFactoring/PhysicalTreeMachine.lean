import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalNodeKernel

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork RecordedHistory

/-- A bit-level finite-state controller. Both transition functions are literal
Boolean networks; this structure does not grant any classical computation oracle. -/
structure NodeMachine (n c : ℕ) where
  query : BooleanNetwork c n
  update : BooleanNetwork (c+NodeKernel.width n) c

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

abbrev initWork := M.query.net.count+(NodeKernel.initialNet n).net.count
abbrev updateWork := M.update.net.count

abbrev width : ℕ→ℕ
  | 0=>c
  | t+1=>(width t+NodeKernel.width n+M.initWork)+c+M.updateWork

def current : (t : ℕ)→Register c (M.width t)
  | 0=>⟨id,Function.injective_id⟩
  | t+1=>targetRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork

def currentNet (t : ℕ) : BooleanNetwork (M.width t) c := select (M.current t)
def initNet (t : ℕ) : BooleanNetwork (M.width t) (NodeKernel.width n) :=
  ((M.currentNet t).comp M.query).comp (NodeKernel.initialNet n)
lemma initNet_count (t : ℕ) : (M.initNet t).net.count=M.initWork := by
  simp only [initNet,count_comp,currentNet,count_select,zero_add]

def updateNet (t : ℕ) : BooleanNetwork (M.width t+NodeKernel.width n+M.initWork) c :=
  (((select (firstRegister (M.width t) (NodeKernel.width n) M.initWork)).comp
    (M.currentNet t)).pair (select (targetRegister (M.width t) (NodeKernel.width n) M.initWork))).comp M.update
lemma updateNet_count (t : ℕ) : (M.updateNet t).net.count=M.updateWork := by
  simp only [updateNet,count_comp,count_pair,count_select,currentNet,zero_add]

def program : (t : ℕ)→List (Instruction (M.width t))
  | 0=>[]
  | t+1=>firstProgram c M.updateWork
      (appendPrepared (program t) (M.initNet t) (M.initNet_count t).le (NodeKernel.program n))++
      oracleOn (M.updateNet t) (M.updateNet_count t).le

def initial : (t : ℕ)→Basis c→Basis (M.width t)
  | 0,x=>x
  | t+1,x=>packed M.updateWork (packed M.initWork (initial t x) (fun _=>false)) (fun _=>false)

abbrev Trace (n : ℕ) : ℕ→Type
  | 0=>Unit
  | t+1=>Trace n t×NodeKernel.Raw n
noncomputable instance traceFintype (n t : ℕ) : Fintype (Trace n t) := by
  induction t with
  | zero=>exact inferInstanceAs (Fintype Unit)
  | succ t ih=>letI:=ih;exact inferInstanceAs (Fintype (Trace n t×NodeKernel.Raw n))

def next (x : Basis c) (r : NodeKernel.Raw n) : Basis c :=
  M.update.eval (Fin.append x (NodeKernel.encoding (M.query.eval x) r))
def config (x : Basis c) : (t : ℕ)→Trace n t→Basis c
  | 0,_=>x
  | t+1,h=>M.next (config x t h.1) h.2

def encoded (x : Basis c) : (t : ℕ)→Trace n t→Basis (M.width t)
  | 0,_=>x
  | t+1,h=>packed M.updateWork
      (packed M.initWork (encoded x t h.1)
        (NodeKernel.encoding (M.query.eval (M.config x t h.1)) h.2)) (M.config x (t+1) h)
noncomputable def state (x : Basis c) : (t : ℕ)→Trace n t→ℂ
  | 0,_=>1
  | t+1,h=>state x t h.1*NodeKernel.fresh (M.query.eval (M.config x t h.1)) h.2

lemma current_encoded (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.currentNet t).eval (M.encoded x t h)=M.config x t h := by
  cases t with
  | zero=>rfl
  | succ t=>exact packed_targetRegister _ _
lemma initNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.initNet t).eval (M.encoded x t h)=NodeKernel.zero (M.query.eval (M.config x t h)) := by
  rw [initNet,eval_comp,NodeKernel.initialNet_eval,eval_comp,M.current_encoded]
lemma updateNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.updateNet t).eval (packed M.initWork (M.encoded x t h)
      (NodeKernel.encoding (M.query.eval (M.config x t h)) r))=M.next (M.config x t h) r := by
  rw [updateNet,eval_comp,eval_pair,eval_comp,eval_select,packed_first,
    M.current_encoded,eval_select,packed_targetRegister]
  rfl

/-- The actual adaptive quantum history, not a table of independent
counterfactual branches. Every update and next modulus comes from this run. -/
theorem program_state (x : Basis c) (t : ℕ) :
    (programMatrix (M.program t)).mulVec (basisVector (M.initial t x))=
      encodeState (M.encoded x t) (M.state x t) := by
  induction t with
  | zero=>
    simp only [program,initial,programMatrix,state,encoded,encodeState]
    simp [Trace]
  | succ t ih=>
    have hp := appendPrepared_state_dependent (M.encoded x t)
      (fun h r=>NodeKernel.encoding (M.query.eval (M.config x t h)) r) (M.state x t)
      (fun h=>NodeKernel.fresh (M.query.eval (M.config x t h)))
      (M.program t) (M.initial t x) ih (M.initNet t) (M.initNet_count t).le
      (NodeKernel.program n) (by
        intro h
        rw [M.initNet_encoded,NodeKernel.program_state])
    dsimp only [program,initial,width]
    rw [programMatrix_append,←Matrix.mulVec_mulVec,firstProgram_basis,hp,encodeState_comp]
    simp only [Function.comp_def]
    rw [oracleOn_encode (fun ab : Trace n t×NodeKernel.Raw n=>
      packed M.initWork (M.encoded x t ab.1) (NodeKernel.encoding
        (M.query.eval (M.config x t ab.1)) ab.2))
      (appendState (M.state x t) (fun h=>NodeKernel.fresh (M.query.eval (M.config x t h))))
      (M.updateNet t) (M.updateNet_count t).le]
    congr 1
    funext h
    rw [M.updateNet_encoded]
    rfl

lemma encoded_injective (x : Basis c) (t : ℕ) : Function.Injective (M.encoded x t) := by
  induction t with
  | zero=>intro a b _;exact @Subsingleton.elim Unit inferInstance a b
  | succ t ih=>
    rintro ⟨a,r⟩ ⟨b,s⟩ he
    dsimp only [encoded] at he
    have hinner := congrArg (fun z=>z ∘ firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork) he
    simp only [packed_first] at hinner
    have he' := congrArg (fun z=>z ∘ firstRegister (M.width t) (NodeKernel.width n) M.initWork) hinner
    simp only [packed_first] at he'
    have hab : a=b := ih he' 
    subst b
    have hr := congrArg (fun z=>z ∘ targetRegister (M.width t) (NodeKernel.width n) M.initWork) hinner
    simp only [packed_targetRegister] at hr
    have hrs : r=s := NodeKernel.encoding_injective _ hr
    subst s
    rfl

lemma width_eq (t : ℕ) : M.width t=c+t*(NodeKernel.width n+M.initWork+c+M.updateWork) := by
  induction t with
  | zero=>simp [width]
  | succ t ih=>simp only [width,ih];ring

lemma program_length (t : ℕ) : (M.program t).length≤
    t*(4*M.initWork+2*NodeKernel.width n+(NodeKernel.program n).length+4*M.updateWork+2*c) := by
  induction t with
  | zero=>simp [program]
  | succ t ih=>
    have hp := appendPrepared_length (M.program t) (M.initNet t) (M.initNet_count t).le (NodeKernel.program n)
    have hu := oracleOn_length (M.updateNet t) (M.updateNet_count t).le
    simp only [M.initNet_count] at hp
    simp only [M.updateNet_count] at hu
    simp only [program,List.length_append,firstProgram_length]
    rw [Nat.succ_mul]
    omega

end NodeMachine
end ExactQuantumFactoring


end

end OAI
