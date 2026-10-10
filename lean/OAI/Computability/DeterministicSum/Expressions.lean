import Mathlib
import OAI.Computability.DeterministicSum.WordArithmetic

namespace OAI

/-! Finite arithmetic expressions and their costed compilation. -/

namespace DeterministicThreeSum.Structured.Indexed
open Command

inductive Arithmetic where
  | add | mul | quot | rem
  deriving DecidableEq

def Arithmetic.op : Arithmetic → BinOp
  | .add => .add | .mul => .mul | .quot => .quot | .rem => .rem

def Arithmetic.value : Arithmetic → ℕ → ℕ → ℕ
  | .add,a,b => a+b | .mul,a,b => a*b | .quot,a,b => a/b | .rem,a,b => a%b

def Arithmetic.Valid (w : ℕ) : Arithmetic → ℕ → ℕ → Prop
  | .add,a,b => a+b<wordModulus w
  | .mul,a,b => a*b<wordModulus w
  | .quot,_,b => 0<b
  | .rem,_,b => 0<b

lemma Arithmetic.value_lt {w a b : ℕ} (op : Arithmetic)
    (ha : a<wordModulus w) (hb : b<wordModulus w) (h : op.Valid w a b) :
    op.value a b<wordModulus w := by
  cases op with
  | add => exact h
  | mul => exact h
  | quot => exact lt_of_le_of_lt (Nat.div_le_self _ _) ha
  | rem => exact lt_trans (Nat.mod_lt _ h) hb

lemma Arithmetic.run {w r a b : ℕ} (op : Arithmetic) (s : Data) (u v : Operand)
    (hu : operand w s u=a) (hv : operand w s v=b)
    (h : op.Valid w a b) :
    Eval w (.atom (.binary r op.op u v)) s 1 (put s r (op.value a b)) := by
  apply Eval.atom
  cases op <;> simp_all [Atom.eval,Arithmetic.op,Arithmetic.value,Arithmetic.Valid,evalBinOp,Nat.mod_eq_of_lt] <;> omega

inductive Expr (m : ℕ) where
  | literal : ℕ → Expr m
  | parameter : Fin m → Expr m
  | binary : Arithmetic → Expr m → Expr m → Expr m

def Expr.value {m : ℕ} (env : Fin m → ℕ) : Expr m → ℕ
  | .literal k => k
  | .parameter i => env i
  | .binary op a b => op.value (a.value env) (b.value env)

def Expr.Valid {m : ℕ} (w : ℕ) (env : Fin m → ℕ) : Expr m → Prop
  | .literal k => k<wordModulus w
  | .parameter i => env i<wordModulus w
  | .binary op a b => a.Valid w env ∧ b.Valid w env ∧ op.Valid w (a.value env) (b.value env)

lemma Expr.value_lt {m w : ℕ} (env : Fin m → ℕ) (e : Expr m)
    (h : e.Valid w env) : e.value env<wordModulus w := by
  induction e with
  | literal k => exact h
  | parameter i => exact h
  | binary op a b iha ihb => exact op.value_lt (iha h.1) (ihb h.2.1) h.2.2

def Expr.compile {m : ℕ} : Expr m → ℕ → Command
  | .literal k,r => .atom (.assign r (.literal k))
  | .parameter i,r => .atom (.assign r (.register i.val))
  | .binary op a b,r => .seq (a.compile r) (.seq (b.compile (r+1))
      (.atom (.binary r op.op (.register r) (.register (r+1)))))

def Expr.cost {m : ℕ} : Expr m → ℕ
  | .literal _ => 1
  | .parameter _ => 1
  | .binary _ a b => a.cost+b.cost+1

theorem Expr.compile_correct {m w r : ℕ} (e : Expr m) (env : Fin m → ℕ)
    (s : Data) (hr : m≤r) (hs : ∀ i, s.registers i.val=env i)
    (h : e.Valid w env) :
    ∃ t, Eval w (e.compile r) s e.cost t ∧ t.memory=s.memory ∧
      t.registers r=e.value env ∧ (∀ k, k<r → t.registers k=s.registers k) := by
  induction e generalizing r s with
  | literal k =>
    refine ⟨put s r k,?_,rfl,by simp [put,Expr.value],?_⟩
    · apply Eval.atom
      simp [Atom.eval,operand_literal,put,Nat.mod_eq_of_lt h]
    · intro k' hk
      simp [put,show k'≠r by omega]
  | parameter i =>
    refine ⟨put s r (env i),?_,rfl,by simp [put,Expr.value],?_⟩
    · apply Eval.atom
      simp [Atom.eval,operand_register,put,hs,Nat.mod_eq_of_lt h]
    · intro k hk
      simp [put,show k≠r by omega]
  | binary op a b iha ihb =>
    obtain ⟨u,hu,hum,hur,huf⟩:=iha s hr hs h.1
    obtain ⟨v,hv,hvm,hvr,hvf⟩:=ihb u (by omega : m≤r+1)
      (fun i => (huf i.val (by have:=i.isLt;omega)).trans (hs i)) h.2.1
    have hA : operand w v (.register r)=a.value env := by
      rw [operand_register,hvf r (by omega),hur,Nat.mod_eq_of_lt (a.value_lt env h.1)]
    have hB : operand w v (.register (r+1))=b.value env := by
      rw [operand_register,hvr,Nat.mod_eq_of_lt (b.value_lt env h.2.1)]
    have he:=op.run (r:=r) v (.register r) (.register (r+1)) hA hB h.2.2
    refine ⟨put v r (op.value (a.value env) (b.value env)),?_,hvm.trans hum,by simp [put,Expr.value],?_⟩
    · simpa only [Expr.compile,Expr.cost,Nat.add_assoc] using Eval.seq hu (Eval.seq hv he)
    · intro k hk
      simp only [put,Function.update_of_ne (show k≠r by omega)]
      exact (hvf k (by omega)).trans (huf k hk)

end DeterministicThreeSum.Structured.Indexed
namespace DeterministicThreeSum.Structured.Indexed
open Command

inductive RingOp where
  | add | mul

def RingOp.bin : RingOp → BinOp | .add => .add | .mul => .mul

def RingOp.raw : RingOp → ℕ → ℕ → ℕ | .add,a,b => a+b | .mul,a,b => a*b

def RingOp.command (op : RingOp) (r : ℕ) : Command :=
  straight [.binary r op.bin (.register r) (.register (r+1)),
    .binary r .rem (.register r) (.register 2)]

lemma RingOp.run {w T r a b : ℕ} (op : RingOp) (s : Data)
    (hr : 3≤r) (hT : 0<T) (hadd : 2*T<wordModulus w) (hmul : T*T<wordModulus w)
    (ha : a<T) (hb : b<T) (h0 : s.registers r=a)
    (h1 : s.registers (r+1)=b) (h2 : s.registers 2=T) :
    Eval w (op.command r) s 2 (put s r (op.raw a b%T)) := by
  have haa : a<wordModulus w := by omega
  have hbb : b<wordModulus w := by omega
  have htt : T<wordModulus w := by omega
  have hsum : a+b<wordModulus w := by omega
  have hprod : a*b<wordModulus w := lt_of_le_of_lt (Nat.mul_le_mul ha.le hb.le) hmul
  apply straight_correct
  cases op <;> simp [RingOp.bin,RingOp.raw,execStraight,Atom.eval,evalBinOp,
    operand_register,put,h0,h1,h2,Nat.mod_eq_of_lt haa,Nat.mod_eq_of_lt hbb,
    Nat.mod_eq_of_lt htt,Nat.mod_eq_of_lt hsum,Nat.mod_eq_of_lt hprod,
    show 2≠r by omega,hT.ne',Function.update_idem]

inductive Scalar (m : ℕ) where
  | literal : ℕ → Scalar m
  | input : Expr m → Scalar m
  | binary : RingOp → Scalar m → Scalar m → Scalar m
  | branch : Expr m → Expr m → Scalar m → Scalar m → Scalar m

def Scalar.value {m : ℕ} (T : ℕ) (env : Fin m → ℕ) (mem : ℕ → Option ℕ) : Scalar m → ℕ
  | .literal k => k%T
  | .input a => (mem (a.value env)).getD 0
  | .binary op a b => op.raw (a.value T env mem) (b.value T env mem)%T
  | .branch x y a b => if x.value env<y.value env then a.value T env mem else b.value T env mem

def Scalar.Valid {m : ℕ} (w T : ℕ) (env : Fin m → ℕ) (mem : ℕ → Option ℕ) : Scalar m → Prop
  | .literal k => k<wordModulus w
  | .input a => a.Valid w env ∧ ∃ v, mem (a.value env)=some v ∧ v<T
  | .binary _ a b => a.Valid w T env mem ∧ b.Valid w T env mem
  | .branch x y a b => x.Valid w env ∧ y.Valid w env ∧
      if x.value env<y.value env then a.Valid w T env mem else b.Valid w T env mem

lemma Scalar.value_lt {m w T : ℕ} (env : Fin m → ℕ) (mem : ℕ → Option ℕ)
    (e : Scalar m) (hT : 0<T) (h : e.Valid w T env mem) : e.value T env mem<T := by
  induction e with
  | literal k => exact Nat.mod_lt _ hT
  | input a => obtain ⟨_,v,hv,hv'⟩:=h; simpa [Scalar.value,hv] using hv'
  | binary op a b iha ihb => exact Nat.mod_lt _ hT
  | branch x y a b iha ihb =>
    simp only [Scalar.Valid] at h
    simp only [Scalar.value]
    split_ifs with hh
    · exact iha (by simpa [hh] using h.2.2)
    · exact ihb (by simpa [hh] using h.2.2)

def Scalar.compile {m : ℕ} : Scalar m → ℕ → Command
  | .literal k,r => straight [.assign r (.literal k),.binary r .rem (.register r) (.register 2)]
  | .input a,r => .seq (a.compile r) (.atom (.load r (.register r)))
  | .binary op a b,r => .seq (a.compile r) (.seq (b.compile (r+1)) (op.command r))
  | .branch x y a b,r => .seq (x.compile r) (.seq (y.compile (r+1))
      (.ite .lt (.register r) (.register (r+1)) (a.compile r) (b.compile r)))

def Scalar.cost {m : ℕ} : Scalar m → ℕ
  | .literal _ => 2
  | .input a => a.cost+1
  | .binary _ a b => a.cost+b.cost+2
  | .branch x y a b => x.cost+y.cost+max a.cost b.cost+2

theorem Scalar.compile_correct {m w T r : ℕ} (e : Scalar m) (env : Fin m → ℕ)
    (mem : ℕ → Option ℕ) (s : Data) (hr : m≤r) (hr' : 3≤r)
    (hT : 0<T) (hadd : 2*T<wordModulus w) (hmul : T*T<wordModulus w)
    (hs : ∀ i, s.registers i.val=env i) (h2 : s.registers 2=T) (hmem : s.memory=mem)
    (h : e.Valid w T env mem) :
    ∃ c t, Eval w (e.compile r) s c t ∧ c≤e.cost ∧ t.memory=mem ∧
      t.registers r=e.value T env mem ∧ (∀ k, k<r → t.registers k=s.registers k) := by
  induction e generalizing r s with
  | literal k =>
    refine ⟨2,put s r (k%T),?_,le_rfl,hmem,by simp [put,Scalar.value],?_⟩
    · apply straight_correct
      simp [execStraight,Atom.eval,evalBinOp,operand_literal,operand_register,put,
        Nat.mod_eq_of_lt h,h2,Nat.mod_eq_of_lt (show T<wordModulus w by omega),
        show 2≠r by omega,hT.ne',Function.update_idem]
    · intro k' hk; simp [put,show k'≠r by omega]
  | input a =>
    obtain ⟨ha,v,hv,hv'⟩:=h
    obtain ⟨u,hu,hum,hur,huf⟩:=a.compile_correct env s hr hs ha
    have he : Eval w (.atom (.load r (.register r))) u 1 (put u r v) := by
      apply Eval.atom
      simp [Atom.eval,operand_register,hur,Nat.mod_eq_of_lt (a.value_lt env ha),hum,hmem,hv]
    refine ⟨a.cost+1,put u r v,Eval.seq hu he,le_rfl,hum.trans hmem,?_,?_⟩
    · simp [put,Scalar.value,hv]
    · intro k hk
      simp only [put,Function.update_of_ne (show k≠r by omega)]
      exact huf k hk
  | binary op a b iha ihb =>
    obtain ⟨ca,u,hu,hca,hum,hur,huf⟩:=iha s hr hr' hs h2 hmem h.1
    obtain ⟨cb,v,hv,hcb,hvm,hvr,hvf⟩:=ihb u (by omega : m≤r+1) (by omega : 3≤r+1)
      (fun i => (huf _ (by have:=i.isLt;omega)).trans (hs i))
      ((huf 2 (by omega)).trans h2) hum h.2
    have he:=op.run v hr' hT hadd hmul (a.value_lt env mem hT h.1) (b.value_lt env mem hT h.2)
      ((hvf r (by omega)).trans hur) hvr ((hvf 2 (by omega)).trans ((huf 2 (by omega)).trans h2))
    refine ⟨ca+(cb+2),put v r (op.raw (a.value T env mem) (b.value T env mem)%T),
      Eval.seq hu (Eval.seq hv he),by simp only [Scalar.cost];omega,hvm,by simp [put,Scalar.value],?_⟩
    intro k hk
    simp only [put,Function.update_of_ne (show k≠r by omega)]
    exact (hvf k (by omega)).trans (huf k hk)
  | branch x y a b iha ihb =>
    obtain ⟨u,hu,hum,hur,huf⟩:=x.compile_correct env s hr hs h.1
    obtain ⟨v,hv,hvm,hvr,hvf⟩:=y.compile_correct env u (by omega : m≤r+1)
      (fun i => (huf _ (by have:=i.isLt;omega)).trans (hs i)) h.2.1
    have hp : ∀ i, v.registers i.val=env i := fun i =>
      (hvf _ (by have:=i.isLt;omega)).trans ((huf _ (by have:=i.isLt;omega)).trans (hs i))
    have hmod : v.registers 2=T := (hvf _ (by omega)).trans ((huf _ (by omega)).trans h2)
    have hvMem : v.memory=mem := hvm.trans (hum.trans hmem)
    have ht : test w v .lt (.register r) (.register (r+1))=decide (x.value env<y.value env) := by
      simp [test,operand_register,evalTest,hvf r (by omega),hur,hvr,
        Nat.mod_eq_of_lt (x.value_lt env h.1),Nat.mod_eq_of_lt (y.value_lt env h.2.1)]
    by_cases hh : x.value env<y.value env
    · obtain ⟨ca,z,hz,hca,hzm,hzr,hzf⟩:=iha v hr hr' hp hmod hvMem (by simpa [hh] using h.2.2)
      refine ⟨x.cost+(y.cost+(1+ca+1)),z,?_,?_,hzm,?_,?_⟩
      · exact Eval.seq hu (Eval.seq hv (Eval.iteTrue (by simpa [hh] using ht) hz))
      · simp only [Scalar.cost];omega
      · simpa [Scalar.value,hh] using hzr
      · intro k hk; exact (hzf k hk).trans ((hvf k (by omega)).trans (huf k hk))
    · obtain ⟨cb,z,hz,hcb,hzm,hzr,hzf⟩:=ihb v hr hr' hp hmod hvMem (by simpa [hh] using h.2.2)
      refine ⟨x.cost+(y.cost+(1+cb)),z,?_,?_,hzm,?_,?_⟩
      · exact Eval.seq hu (Eval.seq hv (Eval.iteFalse (by simpa [hh] using ht) hz))
      · simp only [Scalar.cost];omega
      · simpa [Scalar.value,hh] using hzr
      · intro k hk; exact (hzf k hk).trans ((hvf k (by omega)).trans (huf k hk))

end DeterministicThreeSum.Structured.Indexed

end OAI
