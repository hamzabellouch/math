import Mathlib
import OAI.Computability.QuantumFactoring.NaturalExpressions
import OAI.Computability.QuantumFactoring.NaturalExpressionCircuit
import OAI.Computability.QuantumFactoring.NetworkStackCompiler
import OAI.Computability.QuantumFactoring.NetworkEmissionWords
import OAI.Computability.QuantumFactoring.AIGBitArithmeticEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
open AIGNetworkEmission

/-- Variables, scalar constants, and the fixed algebra instruction vocabulary. -/
abbrev ExprToken (v : Type) := v ⊕ (ℕ ⊕ ℕ)
def exprTokenCode {v : Type} (ev : v→List Bool) : ExprToken v→List Bool:=sumCode ev (sumCode Nat.bits Nat.bits)
def pairToken {v : Type} : ExprToken v:=.inr (.inr 0)
def compToken {v : Type} : ExprToken v:=.inr (.inr 1)
def opToken {v : Type} (j : ℕ) : ExprToken v:=.inr (.inr (j+2))
def primPack (w : ℕ) : ℕ→Pack
  | 0=>binaryPack NativeAIG.add w
  | 1=>binaryPack NativeAIG.mul w
  | 2=>binaryPack NativeAIG.sub w
  | 3=>binaryPack NativeAIG.divide w
  | 4=>binaryPack NativeAIG.remainder w
  | 5=>ultPack w
  | 6=>nodePack 1 (.neg 0) (by simp [Node.Bound])
  | _=>vectorPack (1+w+w) ((List.range w).map (fun i=>muxPack (bitPack (1+w+w) 0)
      (bitPack (1+w+w) (1+i)) (bitPack (1+w+w) (1+w+i))))
def tokenOp {v : Type} (n w : ℕ) (vars : v→Pack) : ExprToken v→StackOp
  | .inl i=>.inl (vars i)
  | .inr (.inl c)=>.inl (wordConstPack n w c)
  | .inr (.inr 0)=>.inr false
  | .inr (.inr 1)=>.inr true
  | .inr (.inr (j+2))=>.inl (primPack w j)
def exprRun {v : Type} (n w : ℕ) (vars : v→Pack) (ts : List (ExprToken v)) (s : List Pack) : List Pack:=
  (ts.map (tokenOp n w vars)).foldl (fun s o=>stackStep o s) s
lemma exprRun_append {v : Type} (n w : ℕ) (vars : v→Pack) (ts us : List (ExprToken v)) (s : List Pack) :
    exprRun n w vars (ts++us) s=exprRun n w vars us (exprRun n w vars ts s):=by
  simp only [exprRun,List.map_append,List.foldl_append]
def Produces {v : Type} (n w : ℕ) (vars : v→Pack) (ts : List (ExprToken v)) (p : Pack) : Prop:=
  ∀s,exprRun n w vars ts s=p::s
lemma produces_var {v : Type} (n w : ℕ) (vars : v→Pack) (i : v) : Produces n w vars [.inl i] (vars i):=by
  intro s;rfl
lemma produces_const {v : Type} (n w : ℕ) (vars : v→Pack) (c : ℕ) :
    Produces n w vars [.inr (.inl c)] (wordConstPack n w c):=by intro s;rfl
lemma produces_op {v : Type} {n w : ℕ} {vars : v→Pack} {ts : List (ExprToken v)} {a : Pack}
    (ha : Produces n w vars ts a) (j : ℕ) :
    Produces n w vars (ts++[opToken j,compToken]) (compPack a (primPack w j)):=by
  intro s;rw [exprRun_append,ha];rfl
lemma produces_pair {v : Type} {n w : ℕ} {vars : v→Pack} {ts us : List (ExprToken v)} {a b : Pack}
    (ha : Produces n w vars ts a) (hb : Produces n w vars us b) :
    Produces n w vars (ts++us++[pairToken]) (pairPack a b):=by
  intro s;rw [exprRun_append,exprRun_append,ha,hb];rfl
lemma produces_binary {v : Type} {n w : ℕ} {vars : v→Pack} {ts us : List (ExprToken v)} {a b : Pack}
    (ha : Produces n w vars ts a) (hb : Produces n w vars us b) (j : ℕ) :
    Produces n w vars ((ts++us++[pairToken])++[opToken j,compToken]) (compPack (pairPack a b) (primPack w j)):=
  produces_op (produces_pair ha hb) j

def leTokens {v : Type} (a b : List (ExprToken v)) : List (ExprToken v):=
  ((b++a++[pairToken])++[opToken 5,compToken])++[opToken 6,compToken]
def muxTokens {v : Type} (c a b : List (ExprToken v)) : List (ExprToken v):=
  (((c++a++[pairToken])++b++[pairToken])++[opToken 7,compToken])
def lePack (w : ℕ) (a b : Pack) : Pack:=bnotPack (compPack (pairPack b a) (ultPack w))
lemma produces_le {v : Type} {n w : ℕ} {vars : v→Pack} {ts us : List (ExprToken v)} {a b : Pack}
    (ha : Produces n w vars ts a) (hb : Produces n w vars us b) :
    Produces n w vars (leTokens ts us) (lePack w a b):=
  produces_op (produces_binary hb ha 5) 6
lemma produces_mux {v : Type} {n w : ℕ} {vars : v→Pack} {ts us vs : List (ExprToken v)} {c a b : Pack}
    (hc : Produces n w vars ts c) (ha : Produces n w vars us a) (hb : Produces n w vars vs b) :
    Produces n w vars (muxTokens ts us vs) (wordMuxPack w c a b):=
  produces_op (produces_pair (produces_pair hc ha) hb) 7

def exprTokens {v : Type} : NatExpr v→List (ExprToken v)
  | .var i=>[.inl i]
  | .const c=>[.inr (.inl c)]
  | .add a b=>((exprTokens a++exprTokens b++[pairToken])++[opToken 0,compToken])
  | .mul a b=>((exprTokens a++exprTokens b++[pairToken])++[opToken 1,compToken])
  | .sub a b=>muxTokens (leTokens (exprTokens b) (exprTokens a))
      ((exprTokens a++exprTokens b++[pairToken])++[opToken 2,compToken]) [.inr (.inl 0)]
  | .div a b=>((exprTokens a++exprTokens b++[pairToken])++[opToken 3,compToken])
  | .mod a b=>((exprTokens a++exprTokens b++[pairToken])++[opToken 4,compToken])
  | .iteLe a b c d=>muxTokens (leTokens (exprTokens a) (exprTokens b)) (exprTokens c) (exprTokens d)
def exprPack {v : Type} (n w : ℕ) (vars : v→Pack) : NatExpr v→Pack
  | .var i=>vars i
  | .const c=>wordConstPack n w c
  | .add a b=>compPack (pairPack (exprPack n w vars a) (exprPack n w vars b)) (binaryPack NativeAIG.add w)
  | .mul a b=>compPack (pairPack (exprPack n w vars a) (exprPack n w vars b)) (binaryPack NativeAIG.mul w)
  | .sub a b=>wordMuxPack w (lePack w (exprPack n w vars b) (exprPack n w vars a))
      (compPack (pairPack (exprPack n w vars a) (exprPack n w vars b)) (binaryPack NativeAIG.sub w)) (wordConstPack n w 0)
  | .div a b=>compPack (pairPack (exprPack n w vars a) (exprPack n w vars b)) (binaryPack NativeAIG.divide w)
  | .mod a b=>compPack (pairPack (exprPack n w vars a) (exprPack n w vars b)) (binaryPack NativeAIG.remainder w)
  | .iteLe a b c d=>wordMuxPack w (lePack w (exprPack n w vars a) (exprPack n w vars b))
      (exprPack n w vars c) (exprPack n w vars d)
lemma exprTokens_produces {v : Type} (n w : ℕ) (vars : v→Pack) (e : NatExpr v) :
    Produces n w vars (exprTokens e) (exprPack n w vars e):=by
  induction e with
  | var i=>exact produces_var n w vars i
  | const c=>exact produces_const n w vars c
  | add a b ha hb=>exact produces_binary ha hb 0
  | mul a b ha hb=>exact produces_binary ha hb 1
  | div a b ha hb=>exact produces_binary ha hb 3
  | mod a b ha hb=>exact produces_binary ha hb 4
  | sub a b ha hb=>exact produces_mux (produces_le hb ha) (produces_binary ha hb 2) (produces_const n w vars 0)
  | iteLe a b c d ha hb hc hd=>exact produces_mux (produces_le ha hb) hc hd
lemma lePack_value {n w : ℕ} (a b : Pack) (f g : BooleanNetwork n w)
    (ha : a.val.value=erase f) (hb : b.val.value=erase g) :
    (lePack w a b).val.value=erase (BitArithmetic.wordLe f g):=
  bnotPack_value _ _ (compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ hb ha) (ultPack_value w))
lemma exprPack_value {v : Type} {n w : ℕ} (vars : v→Pack) (fs : v→BooleanNetwork n w)
    (hf : ∀i,(vars i).val.value=erase (fs i)) (e : NatExpr v) :
    (exprPack n w vars e).val.value=erase (e.compile fs):=by
  induction e with
  | var i=>exact hf i
  | const c=>exact wordConstPack_value n w c
  | add a b ha hb=>exact compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ ha hb) (addPack_value w)
  | mul a b ha hb=>exact compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ ha hb) (mulPack_value w)
  | div a b ha hb=>exact compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ ha hb) (divPack_value w)
  | mod a b ha hb=>exact compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ ha hb) (modPack_value w)
  | sub a b ha hb=>
    exact wordMuxPack_value _ _ _ _ _ _ (lePack_value _ _ _ _ hb ha)
      (compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ ha hb) (subPack_value w)) (wordConstPack_value n w 0)
  | iteLe a b c d ha hb hc hd=>exact wordMuxPack_value _ _ _ _ _ _ (lePack_value _ _ _ _ ha hb) hc hd
end ExactQuantumFactoring.NetworkEmission

end


end OAI
