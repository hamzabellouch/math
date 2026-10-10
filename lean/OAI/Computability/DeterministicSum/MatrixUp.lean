import Mathlib
import OAI.Computability.DeterministicSum.NewtonCommands
import OAI.Computability.DeterministicSum.MatrixDown

namespace OAI

/-! Return-count stacks and uniform upward matrix recursion. -/

namespace DeterministicThreeSum.Structured.Indexed.MatrixLayout
open Command DeterministicThreeSum.Rectangular Axis Finset
open scoped BigOperators

theorem combine_level_correct {w T a b k r d t P S C : ℕ}
    (state : Data) (f : FixedFormula (ZMod T) a b k r)
    (z : OutputBatch (ZMod T) a d (batchCount t k*r)) (data co : ℕ → ℕ)
    (ha : 0<a) (hk : 0<k) (hr : 0<r) (hT : 0<T)
    (hadd : 2*T<wordModulus w) (hmul : T*T<wordModulus w)
    (hN : batchCount t k*(k*(a*a))*((a*a)^d)+1<wordModulus w)
    (hP : P+batchCount t k*(k*(a*a))*((a*a)^d)<wordModulus w)
    (hS : S+batchCount t k*r*((a*a)^d)<wordModulus w)
    (hC : C+(k*(a*a))*r<wordModulus w)
    (hdisS : S+batchCount t k*r*((a*a)^d)≤P ∨ P+batchCount t k*(k*(a*a))*((a*a)^d)≤S)
    (hdisC : C+(k*(a*a))*r≤P ∨ P+batchCount t k*(k*(a*a))*((a*a)^d)≤C)
    (hregs : ∀ i : Fin 8, state.registers i.val=
      environment T (batchCount t k*(k*(a*a))*((a*a)^d)) P S C ((a*a)^d) (batchCount t k) 0 i)
    (hx : ∀ i, i<batchCount t k*r*((a*a)^d) → state.memory (S+i)=some (data i) ∧ data i<T)
    (hc : ∀ i, i<(k*(a*a))*r → state.memory (C+i)=some (co i) ∧ co i<T)
    (hsource : ∀ e u v, (data (e.val*((a*a)^d)+pairCode a a d u v):ZMod T)=z e u v)
    (hformula : ∀ (s : Fin r) (i : Fin k × Fin a × Fin a),
      (co ((tripleIndex k a a i).val*r+s.val):ZMod T)=f.out s i) :
    ∃ cost out, Eval w (pass r (k*(a*a))) state cost out ∧
      cost≤((row r (k*(a*a))).cost+5)*(batchCount t k*(k*(a*a))*((a*a)^d))+1 ∧
      (∀ i, i<8 → i≠0 → out.registers i=state.registers i) ∧
      out.registers 0=batchCount t k*(k*(a*a))*((a*a)^d) ∧
      (∀ (e : Fin t) (u v : DigitBox a (d+1)), ∃ n,
        out.memory (P+e.val*((a*a)^(d+1))+pairCode a a (d+1) u v)=some n ∧
          n<T ∧ (n:ZMod T)=combineChildren f hk z e u v) ∧
      (∀ addr, addr<P ∨ P+batchCount t k*(k*(a*a))*((a*a)^d)≤addr → out.memory addr=state.memory addr) := by
  have hQ := Nat.mul_pos ha ha
  have hR := Nat.mul_pos hk hQ
  have hB := pow_pos hQ d
  obtain ⟨cost,out,he,hcost,hframe,hzero,hmem,houtside⟩ := pass_exact state data co
    hr hR hB hT hadd hmul hN hP hS hC hdisS hdisC hregs hx hc
  refine ⟨cost,out,he,hcost,hframe,hzero,?_,houtside⟩
  intro e u v
  have hi0 : e.val*((a*a)^(d+1))+pairCode a a (d+1) u v<t*((a*a)^(d+1)) :=
    (packed_lt (pow_pos hQ (d+1)) _ _ _ (pairCode_lt ha ha (d+1) u v)).mpr e.isLt
  have hi : e.val*((a*a)^(d+1))+pairCode a a (d+1) u v<batchCount t k*(k*(a*a))*((a*a)^d) :=
    hi0.trans_le (input_padding_bound hk)
  refine ⟨_,?_,mapValue_lt hT _ _ _ _ _ _,combine_level_value ha hk f z data co hsource hformula e u v⟩
  simpa only [Nat.add_assoc] using hmem _ hi

end DeterministicThreeSum.Structured.Indexed.MatrixLayout
namespace DeterministicThreeSum.Structured.Indexed.MatrixTrace
open Command DeterministicThreeSum.Rectangular MatrixDown

def body (k r : ℕ) : Command := straight [
  .binary 8 .add (.register 2) (.literal (k-1)),
  .binary 8 .quot (.register 8) (.literal k),
  .binary 9 .add (.register 3) (.register 0),
  .store (.register 9) (.register 8),
  .binary 2 .mul (.register 8) (.literal r),
  .binary 0 .add (.register 0) (.literal 1)]
def command (k r : ℕ) : Command := .loop .lt (.register 0) (.register 1) (body k r)

def next (s : Data) (k r M i n : ℕ) : Data :=
  let v := put (put (put s 8 (n+(k-1))) 8 (batchCount n k)) 9 (M+i)
  put (put {v with memory:=Function.update v.memory (M+i) (some (batchCount n k))}
    2 (batchCount n k*r)) 0 (i+1)

lemma body_correct {w k r M i n : ℕ} (s : Data)
    (hk : 0<k) (hkW : k<wordModulus w) (hrW : r<wordModulus w)
    (hnum : n+k<wordModulus w) (hprod : batchCount n k*r<wordModulus w)
    (haddr : M+i<wordModulus w) (hindex : i+1<wordModulus w)
    (h0 : s.registers 0=i) (h2 : s.registers 2=n) (h3 : s.registers 3=M) :
    Eval w (body k r) s 6 (next s k r M i n) := by
  have hn : n<wordModulus w := by omega
  have hsum : n+(k-1)<wordModulus w := by omega
  have hdiv : batchCount n k<wordModulus w := (batch_le hk n).trans_lt hnum
  apply straight_correct
  simp [next,execStraight,Atom.eval,operand_literal,operand_register,evalBinOp,put,
    h0,h2,h3,hk.ne',Nat.mod_eq_of_lt hkW,Nat.mod_eq_of_lt hrW,
    Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt hsum,ceil_eq hk,
    Nat.mod_eq_of_lt hdiv,Nat.mod_eq_of_lt hprod,Nat.mod_eq_of_lt haddr,
    Nat.mod_eq_of_lt hindex,
    Nat.mod_eq_of_lt (show k-1<wordModulus w by omega),
    Nat.mod_eq_of_lt (show 1<wordModulus w by omega),Function.update_idem]

lemma finalCount_succ (k r d t : ℕ) :
    finalCount k r (d+1) t=batchCount (finalCount k r d t) k*r := by
  induction d generalizing t with
  | zero => rfl
  | succ d ih => exact ih (batchCount t k*r)

theorem command_correct {w k r M d t : ℕ} (s : Data)
    (hk : 0<k) (hkW : k<wordModulus w) (hrW : r<wordModulus w)
    (hnum : ∀ i, i<d → finalCount k r i t+k<wordModulus w)
    (hprod : ∀ i, i<d → finalCount k r (i+1) t<wordModulus w)
    (haddr : M+d<wordModulus w) (hindex : d+1<wordModulus w)
    (h0 : s.registers 0=0) (h1 : s.registers 1=d)
    (h2 : s.registers 2=t) (h3 : s.registers 3=M) :
    ∃ cost out, Eval w (command k r) s cost out ∧ cost≤8*d+1 ∧
      out.registers 0=d ∧ out.registers 2=finalCount k r d t ∧
      out.memory=written s M (fun i=>batchCount (finalCount k r i t) k) d ∧
      (∀ j, j≠0 → j≠2 → j≠8 → j≠9 → out.registers j=s.registers j) := by
  let Inv : ℕ → Data → Prop := fun i u => u.registers 0=i ∧
    u.registers 2=finalCount k r i t ∧ u.registers 1=d ∧ u.registers 3=M ∧
    u.memory=written s M (fun j=>batchCount (finalCount k r j t) k) i
  have hy : ∀ i u, i<d → Inv i u → test w u .lt (.register 0) (.register 1)=true := by
    intro i u hi hu
    simp [test,operand_register,evalTest,hu.1,hu.2.2.1,
      Nat.mod_eq_of_lt (show i<wordModulus w by omega),
      Nat.mod_eq_of_lt (show d<wordModulus w by omega),hi]
  have hn : ∀ u, Inv d u → test w u .lt (.register 0) (.register 1)=false := by
    intro u hu
    simp [test,operand_register,evalTest,hu.1,hu.2.2.1]
  have hb : ∀ i u, i<d → Inv i u → ∃ cost v, Eval w (body k r) u cost v ∧
      cost≤6 ∧ Inv (i+1) v := by
    intro i u hi hu
    let v:=next u k r M i (finalCount k r i t)
    have he:=body_correct u hk hkW hrW (hnum i hi)
      (by simpa only [finalCount_succ] using hprod i hi)
      (by omega : M+i<wordModulus w) (by omega : i+1<wordModulus w)
      hu.1 hu.2.1 hu.2.2.2.1
    refine ⟨6,v,he,by omega,?_,?_,?_,?_,?_⟩
    · simp [v,next,put]
    · simp [v,next,put,finalCount_succ]
    · simpa [v,next,put] using hu.2.2.1
    · simpa [v,next,put] using hu.2.2.2.1
    · change Function.update u.memory (M+i) (some (batchCount (finalCount k r i t) k))=_
      rw [hu.2.2.2.2,written_next]
  have hi : Inv 0 s := ⟨h0,h2,h1,h3,(written_zero ..).symm⟩
  obtain ⟨cost,out,he,hcost,hout⟩ := bounded_loop (N:=d) (B:=6) Inv hy hn hb (i:=0) (by omega) hi
  refine ⟨cost,out,he,by simpa using hcost,hout.1,hout.2.1,hout.2.2.2.2,?_⟩
  intro j hj0 hj2 hj8 hj9
  apply register_frame he
  simp [body,straight,Command.writes,Atom.writes,hj0,hj2,hj8,hj9]

end DeterministicThreeSum.Structured.Indexed.MatrixTrace
namespace DeterministicThreeSum.Structured.Indexed.MatrixUp
open Command DeterministicThreeSum.Rectangular Axis

def setup (Q k K : ℕ) : Command := straight [
  .binary K .sub (.register K) (.literal 1), .load 7 (.register K),
  .binary 1 .mul (.register 7) (.literal (k*Q)),
  .binary 1 .mul (.register 1) (.register 6), .assign 0 (.literal 0)]
def prepared (s : Data) (K J A k Q B : ℕ) : Data :=
  put (put (put (put (put s K J) 7 A) 1 (A*(k*Q))) 1 (A*(k*Q)*B)) 0 0

lemma setup_correct {w Q k K J A B : ℕ} (s : Data)
    (hK : 10≤K) (hJ : J+1<wordModulus w) (hA : A<wordModulus w)
    (hR : k*Q<wordModulus w) (hAR : A*(k*Q)<wordModulus w)
    (hB : B<wordModulus w) (hARB : A*(k*Q)*B<wordModulus w)
    (hKval : s.registers K=J+1) (h6 : s.registers 6=B)
    (hm : s.memory J=some A) :
    Eval w (setup Q k K) s 5 (prepared s K J A k Q B) := by
  apply straight_correct
  simp [prepared,execStraight,Atom.eval,operand_literal,operand_register,evalBinOp,put,
    hKval,h6,hm,Nat.mod_eq_of_lt hJ,Nat.mod_eq_of_lt hA,
    Nat.mod_eq_of_lt hR,Nat.mod_eq_of_lt hB,
    Nat.mod_eq_of_lt hAR,Nat.mod_eq_of_lt hARB,
    Nat.mod_eq_of_lt (show J<wordModulus w by omega),
    Nat.mod_eq_of_lt (show 1<wordModulus w by omega),
    show (6:ℕ)≠K by omega,Function.update_idem,-Nat.mul_mod_mod,-Nat.mod_mul_mod]

def update (Q : ℕ) : Command := straight [
  .assign 8 (.register 3), .assign 3 (.register 4), .assign 4 (.register 8),
  .binary 6 .mul (.register 6) (.literal Q)]
def updated (s : Data) (Q P S B : ℕ) : Data :=
  put (put (put (put s 8 P) 3 S) 4 P) 6 (B*Q)

lemma update_correct {w Q P S B : ℕ} (s : Data)
    (hQ : Q<wordModulus w) (hP : P<wordModulus w) (hS : S<wordModulus w)
    (hB : B<wordModulus w) (hBQ : B*Q<wordModulus w)
    (h3 : s.registers 3=P) (h4 : s.registers 4=S) (h6 : s.registers 6=B) :
    Eval w (update Q) s 4 (updated s Q P S B) := by
  apply straight_correct
  simp [updated,execStraight,Atom.eval,operand_literal,operand_register,evalBinOp,put,
    h3,h4,h6,Nat.mod_eq_of_lt hQ,Nat.mod_eq_of_lt hP,Nat.mod_eq_of_lt hS,
    Nat.mod_eq_of_lt hB,Nat.mod_eq_of_lt hBQ,-Nat.mul_mod_mod,-Nat.mod_mul_mod]

def body (Q k r K : ℕ) : Command :=
  .seq (setup Q k K) (.seq (pass r (k*Q)) (update Q))
def command (Q k r K : ℕ) : Command :=
  .loop .lt (.register (K+1)) (.register K) (body Q k r K)

theorem body_correct {w T Q k r K J A B P S C : ℕ} (s : Data) (x co : ℕ → ℕ)
    (hK : 10≤K) (hKw : (pass r (k*Q)).writes.sup id<K)
    (hQ : 0<Q) (hk : 0<k) (hr : 0<r) (hB : 0<B) (hT : 0<T)
    (hadd : 2*T<wordModulus w) (hmul : T*T<wordModulus w)
    (hQW : Q<wordModulus w) (hRW : k*Q<wordModulus w)
    (hAW : A<wordModulus w) (hARW : A*(k*Q)<wordModulus w)
    (hBW : B<wordModulus w) (hBQ : B*Q<wordModulus w)
    (hJ : J+1<wordModulus w)
    (hN : A*(k*Q)*B+1<wordModulus w)
    (hP : P+A*(k*Q)*B<wordModulus w) (hS : S+A*r*B<wordModulus w)
    (hC : C+(k*Q)*r<wordModulus w)
    (hdisS : S+A*r*B≤P ∨ P+A*(k*Q)*B≤S)
    (hdisC : C+(k*Q)*r≤P ∨ P+A*(k*Q)*B≤C)
    (h2 : s.registers 2=T) (h3 : s.registers 3=P) (h4 : s.registers 4=S)
    (h5 : s.registers 5=C) (h6 : s.registers 6=B) (hKV : s.registers K=J+1)
    (hmeta : s.memory J=some A)
    (hx : ∀ i, i<A*r*B → s.memory (S+i)=some (x i) ∧ x i<T)
    (hc : ∀ i, i<(k*Q)*r → s.memory (C+i)=some (co i) ∧ co i<T) :
    ∃ cost out, Eval w (body Q k r K) s cost out ∧
      cost≤((row r (k*Q)).cost+5)*(A*(k*Q)*B)+10 ∧
      (∀ a : Fin 8, out.registers a.val=
        environment T (A*(k*Q)*B) S P C (B*Q) A (A*(k*Q)*B) a) ∧
      out.registers K=J ∧ out.registers (K+1)=s.registers (K+1) ∧
      (∀ i, i<A*(k*Q)*B → out.memory (P+i)=some (mapValue T r (k*Q) B x co i)) ∧
      (∀ addr, addr<P ∨ P+A*(k*Q)*B≤addr → out.memory addr=s.memory addr) := by
  let u:=prepared s K J A k Q B
  have eu:=setup_correct s hK hJ hAW hRW hARW hBW (by omega) hKV h6 hmeta
  have hregsu : ∀ a : Fin 8, u.registers a.val=
      environment T (A*(k*Q)*B) P S C B A 0 a := by
    intro a
    fin_cases a <;> simp [u,prepared,put,environment,h2,h3,h4,h5,h6,
      show (2:ℕ)≠K by omega,show (3:ℕ)≠K by omega,show (4:ℕ)≠K by omega,
      show (5:ℕ)≠K by omega,show (6:ℕ)≠K by omega]
  obtain ⟨c,v,ev,hcv,hframe,hzero,hm,houtside⟩ := pass_exact u x co hr
    (Nat.mul_pos hk hQ) hB hT hadd hmul hN hP hS hC hdisS hdisC hregsu hx hc
  have hp (a : Fin 8) (ha : a.val≠0) : v.registers a.val=
      environment T (A*(k*Q)*B) P S C B A 0 a :=
    (hframe a.val a.isLt ha).trans (hregsu a)
  have h3v : v.registers 3=P := by simpa [environment] using hp ⟨3,by omega⟩ (by norm_num)
  have h4v : v.registers 4=S := by simpa [environment] using hp ⟨4,by omega⟩ (by norm_num)
  have h6v : v.registers 6=B := by simpa [environment] using hp ⟨6,by omega⟩ (by norm_num)
  have ew:=update_correct v hQW (by omega) (by omega) hBW hBQ h3v h4v h6v
  let out:=updated v Q P S B
  refine ⟨5+(c+4),out,Eval.seq eu (Eval.seq ev ew),by omega,?_,?_,?_,hm,houtside⟩
  · intro a
    have h1v : v.registers 1=A*(k*Q)*B := by simpa [environment] using hp ⟨1,by omega⟩ (by norm_num)
    have h2v : v.registers 2=T := by simpa [environment] using hp ⟨2,by omega⟩ (by norm_num)
    have h5v : v.registers 5=C := by simpa [environment] using hp ⟨5,by omega⟩ (by norm_num)
    have h7v : v.registers 7=A := by simpa [environment] using hp ⟨7,by omega⟩ (by norm_num)
    fin_cases a <;> simp [out,updated,put,environment,hzero,h1v,h2v,h5v,h7v]
  · have hv:=protected_frame ev hKw 0
    simpa [out,updated,put,u,prepared,show K≠0 by omega,show K≠1 by omega,
      show K≠3 by omega,show K≠4 by omega,show K≠6 by omega,show K≠7 by omega,
      show K≠8 by omega] using hv
  · have hv:=protected_frame ev hKw 1
    simpa [out,updated,put,u,prepared,Function.update_apply,show K≠0 by omega,show K+1≠0 by omega,show K+1≠1 by omega,
      show K+1≠3 by omega,show K+1≠4 by omega,show K+1≠6 by omega,
      show K+1≠7 by omega,show K+1≠8 by omega,show K+1≠K by omega] using hv

end DeterministicThreeSum.Structured.Indexed.MatrixUp
namespace DeterministicThreeSum.Structured.Indexed.MatrixUp
open Command DeterministicThreeSum.Rectangular Axis

def Bounds (Q k r L : ℕ) (A : ℕ → ℕ) : ℕ → ℕ → ℕ → Prop
  | 0,_,N => N≤L
  | d+1,B,N => N≤L ∧ 0<A d ∧ A d*r*B≤N ∧ A d*(k*Q)*B≤L ∧
      Bounds Q k r L A d (B*Q) (A d*(k*Q)*B)
def outputSize (Q k : ℕ) (A : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,_,N => N
  | d+1,B,_ => outputSize Q k A d (B*Q) (A d*(k*Q)*B)
def value (T Q k r : ℕ) (co : ℕ → ℕ) : ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | 0,_,x => x
  | d+1,B,x => value T Q k r co d (B*Q) (mapValue T r (k*Q) B x co)

theorem command_correct {w T Q k r K L n B N P S C M : ℕ}
    (s : Data) (x co A : ℕ → ℕ)
    (hK : 10≤K) (hKw : (pass r (k*Q)).writes.sup id<K)
    (hQ : 0<Q) (hk : 0<k) (hr : 0<r) (hB : 0<B) (hT : 0<T)
    (hadd : 2*T<wordModulus w) (hmul : T*T<wordModulus w)
    (hbounds : Bounds Q k r L A n B N)
    (hLW : L+3<wordModulus w) (hBW : B*Q^n<wordModulus w)
    (hP : P+L+1<wordModulus w) (hS : S+L+1<wordModulus w)
    (hC : C+(k*Q)*r<wordModulus w) (hM : M+n+1<wordModulus w)
    (hPS : S+L≤P ∨ P+L≤S)
    (hCP : C+(k*Q)*r≤P ∨ P+L≤C) (hCS : C+(k*Q)*r≤S ∨ S+L≤C)
    (hMP : M+n≤P ∨ P+L≤M) (hMS : M+n≤S ∨ S+L≤M)
    (h2 : s.registers 2=T) (h3 : s.registers 3=P) (h4 : s.registers 4=S)
    (h5 : s.registers 5=C) (h6 : s.registers 6=B)
    (hptr : s.registers K=M+n) (hbase : s.registers (K+1)=M)
    (hx : ∀ i, i<N → s.memory (S+i)=some (x i) ∧ x i<T)
    (hc : ∀ i, i<(k*Q)*r → s.memory (C+i)=some (co i) ∧ co i<T)
    (hmeta : ∀ i, i<n → s.memory (M+i)=some (A i)) :
    ∃ cost out, Eval w (command Q k r K) s cost out ∧
      cost≤(((row r (k*Q)).cost+5)*L+12)*n+1 ∧
      out.registers 2=T ∧ out.registers 3=(banks n P S).1 ∧
      out.registers 4=(banks n P S).2 ∧ out.registers 5=C ∧
      out.registers 6=B*Q^n ∧ out.registers K=M ∧ out.registers (K+1)=M ∧
      (∀ i, i<outputSize Q k A n B N →
        out.memory ((banks n P S).2+i)=some (value T Q k r co n B x i) ∧
          value T Q k r co n B x i<T) ∧
      (∀ addr, (addr<P ∨ P+L≤addr) → (addr<S ∨ S+L≤addr) →
        out.memory addr=s.memory addr) := by
  induction n generalizing s x B N P S with
  | zero =>
    have ht : test w s .lt (.register (K+1)) (.register K)=false := by
      simp [test,operand_register,evalTest,hptr,hbase]
    exact ⟨1,s,Eval.loopFalse ht,by simp,h2,by simpa [banks_zero] using h3,
      by simpa [banks_zero] using h4,h5,by simpa using h6,by simpa using hptr,hbase,
      by simpa [outputSize,value,banks_zero] using hx,by simp⟩
  | succ n ih =>
    obtain ⟨hNL,hA,hinput,houtput,hnext⟩:=hbounds
    have hR : 0<k*Q := Nat.mul_pos hk hQ
    have hRW : k*Q<wordModulus w := by
      have hh : k*Q≤(k*Q)*r := by simpa using Nat.mul_le_mul_left (k*Q) hr
      omega
    have hQW : Q<wordModulus w := by
      have hh : Q≤k*Q := by simpa using Nat.mul_le_mul_right Q hk
      omega
    have hAR : A n*(k*Q)≤L :=
      (by simpa using Nat.mul_le_mul_left (A n*(k*Q)) hB : A n*(k*Q)≤A n*(k*Q)*B) |>.trans houtput
    have hAW : A n<wordModulus w := by
      have hh : A n≤A n*(k*Q) := by simpa using Nat.mul_le_mul_left (A n) hR
      omega
    have hpow : 1≤Q^n := one_le_pow₀ hQ
    have hBQ : B*Q<wordModulus w := by
      have hh : B*Q≤B*Q^(n+1) := by
        calc
          _ ≤ (B*Q)*Q^n := by simpa using Nat.mul_le_mul_left (B*Q) hpow
          _ = _ := by rw [pow_succ]; ring
      exact hh.trans_lt hBW
    have hBW0 : B<wordModulus w := by
      have hh : B≤B*Q := by simpa using Nat.mul_le_mul_left B hQ
      omega
    have htest : test w s .lt (.register (K+1)) (.register K)=true := by
      simp [test,operand_register,evalTest,hptr,hbase,
        Nat.mod_eq_of_lt (show M<wordModulus w by omega),
        Nat.mod_eq_of_lt (show M+(n+1)<wordModulus w by omega)]
    obtain ⟨cost,u,he,hcost,hu,hptru,hbaseu,hm,ho⟩ := body_correct s x co hK hKw
      hQ hk hr hB hT hadd hmul hQW hRW hAW (by omega) hBW0 hBQ
      (by omega : M+n+1<wordModulus w) (by omega) (by omega) (by omega) hC
      (by omega) (by omega) h2 h3 h4 h5 h6 (by simpa only [Nat.add_assoc] using hptr)
      (hmeta n (by omega)) (fun i hi=>hx i (hi.trans_le hinput)) hc
    have h2u : u.registers 2=T := by simpa [environment] using hu ⟨2,by omega⟩
    have h3u : u.registers 3=S := by simpa [environment] using hu ⟨3,by omega⟩
    have h4u : u.registers 4=P := by simpa [environment] using hu ⟨4,by omega⟩
    have h5u : u.registers 5=C := by simpa [environment] using hu ⟨5,by omega⟩
    have h6u : u.registers 6=B*Q := by simpa [environment] using hu ⟨6,by omega⟩
    have hx' : ∀ i, i<A n*(k*Q)*B → u.memory (P+i)=some (mapValue T r (k*Q) B x co i) ∧
        mapValue T r (k*Q) B x co i<T := fun i hi=>⟨hm i hi,mapValue_lt hT _ _ _ _ _ _⟩
    have hc' : ∀ i, i<(k*Q)*r → u.memory (C+i)=some (co i) ∧ co i<T := by
      intro i hi
      rw [ho (C+i) (by omega)]
      exact hc i hi
    have hm' : ∀ i, i<n → u.memory (M+i)=some (A i) := by
      intro i hi
      rw [ho (M+i) (by omega)]
      exact hmeta i (by omega)
    have hBW' : (B*Q)*Q^n<wordModulus w := by
      convert hBW using 1
      rw [pow_succ]
      ring
    obtain ⟨rest,out,er,hrcost,hr2,hr3,hr4,hr5,hr6,hrK,hrBase,hmF,hoF⟩ := ih
      u (mapValue T r (k*Q) B x co) (Nat.mul_pos hB hQ) hnext hBW'
      hS hP (by omega) (by omega) hCS hCP (by omega) (by omega)
      h2u h3u h4u h5u h6u hptru (hbaseu.trans hbase) hx' hc' hm'
    refine ⟨1+cost+1+rest,out,Eval.loopTrue htest he er,?_,hr2,?_,?_,hr5,?_,hrK,hrBase,?_,?_⟩
    · have hcL : cost≤((row r (k*Q)).cost+5)*L+10 := hcost.trans (by gcongr)
      nlinarith only [hcL,hrcost]
    · simpa only [banks_succ] using hr3
    · simpa only [banks_succ] using hr4
    · convert hr6 using 1
      rw [pow_succ]
      ring
    · simpa only [banks_succ,outputSize,value] using hmF
    · intro addr ha hb
      rw [hoF addr hb ha]
      exact ho addr (by omega)

end DeterministicThreeSum.Structured.Indexed.MatrixUp

end OAI
