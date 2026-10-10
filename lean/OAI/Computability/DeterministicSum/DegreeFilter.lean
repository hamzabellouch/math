import Mathlib
import OAI.Computability.DeterministicSum.WordArithmetic

namespace OAI

/-! Charged digit-degree filters and finite-memory output bounds. -/

namespace DeterministicThreeSum.Structured.Indexed.DigitSum
open Command

def value (q : ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 0
  | d+1,n => n%q+value q d (n/q)

lemma value_zero (q d : ℕ) : value q d 0=0 := by induction d <;> simp [value, *]

lemma value_le {q : ℕ} (hq : 1 < q) (d n : ℕ) : value q d n≤n := by
  induction d generalizing n with
  | zero => simp [value]
  | succ d ih =>
    have h:=ih (n/q)
    have hq' : n/q≤q*(n/q) := by nlinarith
    have he:=Nat.mod_add_div n q
    simp only [value]
    omega

def step (q : ℕ) : Command := straight [
  .binary 10 .rem (.register 8) (.literal q),
  .binary 9 .add (.register 9) (.register 10),
  .binary 8 .quot (.register 8) (.literal q)]
def loop (q : ℕ) : Command := .loop .lt (.literal 0) (.register 8) (step q)

def stepState (s : Data) (q n a : ℕ) : Data := put (put (put s 10 (n%q)) 9 (a+n%q)) 8 (n/q)

lemma step_correct {w q n a : ℕ} (s : Data) (hq : 0 < q) (hqw : q<wordModulus w)
    (hn : n<wordModulus w) (ha : a+n%q<wordModulus w)
    (h8 : s.registers 8=n) (h9 : s.registers 9=a) :
    Eval w (step q) s 3 (stepState s q n a) := by
  apply straight_correct
  simp [stepState,execStraight,Atom.eval,operand_register,operand_literal,evalBinOp,put,
    h8,h9,hq.ne',Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt hqw,Nat.mod_eq_of_lt ha]

theorem loop_correct {w q : ℕ} (hq : 1 < q) (hqw : q<wordModulus w)
    (d n a : ℕ) (s : Data) (hn : n<q^d) (hnw : n<wordModulus w)
    (hasum : a+value q d n<wordModulus w)
    (h8 : s.registers 8=n) (h9 : s.registers 9=a) :
    ∃ cost z, Eval w (loop q) s cost z ∧ cost≤5*d+1 ∧ z.memory=s.memory ∧
      z.registers 8=0 ∧ z.registers 9=a+value q d n ∧
      (∀ r, r≠8 → r≠9 → r≠10 → z.registers r=s.registers r) := by
  induction d generalizing n a s with
  | zero =>
    have hn0 : n=0 := by simpa using hn
    rcases hn0 with rfl
    refine ⟨1,s,Eval.loopFalse ?_,by omega,rfl,h8,by simpa [value] using h9,by simp⟩
    simp [test,operand_register,operand_literal,evalTest,h8]
  | succ d ih =>
    by_cases hn0 : n=0
    · rcases hn0 with rfl
      refine ⟨1,s,Eval.loopFalse ?_,by omega,rfl,h8,by simpa [value_zero] using h9,by simp⟩
      simp [test,operand_register,operand_literal,evalTest,h8]
    have hqn : n/q<q^d := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0<q)).mpr
      simpa only [pow_succ] using hn
    have ha : a+n%q<wordModulus w := by simpa only [value] using (show a+n%q<wordModulus w by simp only [value] at hasum; omega)
    let u:=stepState s q n a
    have hs:=step_correct s (by omega : 0<q) hqw hnw ha h8 h9
    obtain ⟨c,z,he,hc,hm,hz8,hz9,hf⟩:=ih (n/q) (a+n%q) u hqn ((Nat.div_le_self ..).trans_lt hnw)
      (by simpa only [value,Nat.add_assoc] using hasum) (by simp [u,stepState,put]) (by simp [u,stepState,put])
    refine ⟨1+3+1+c,z,Eval.loopTrue ?_ hs he,by omega,hm,hz8,?_,?_⟩
    · simp [test,operand_register,operand_literal,evalTest,h8,Nat.mod_eq_of_lt hnw,show 0<n by omega]
    · simpa only [value,Nat.add_assoc] using hz9
    · intro r hr8 hr9 hr10
      rw [hf r hr8 hr9 hr10]
      simp [u,stepState,put,hr8,hr9,hr10]
end DeterministicThreeSum.Structured.Indexed.DigitSum
namespace DeterministicThreeSum.Structured.Indexed.DegreeFilter
open Command

def memory (q d D P k : ℕ) (mem : ℕ → Option ℕ) (a : ℕ) : Option ℕ :=
  if P≤a ∧ a<P+k ∧ D<DigitSum.value q d ((a-P)%(q^d)) then some 0 else mem a

lemma memory_zero (q d D P : ℕ) (mem : ℕ → Option ℕ) : memory q d D P 0 mem=mem := by
  funext a; simp [memory]; omega

lemma memory_succ (q d D P k : ℕ) (mem : ℕ → Option ℕ) :
    memory q d D P (k+1) mem =
      if D<DigitSum.value q d (k%(q^d)) then Function.update (memory q d D P k mem) (P+k) (some 0)
      else memory q d D P k mem := by
  funext a
  by_cases he : a=P+k
  · subst a
    by_cases h : D<DigitSum.value q d (k%(q^d)) <;> simp [memory,h]
  · have hb : a<P+(k+1) ↔ a<P+k := by omega
    by_cases h : D<DigitSum.value q d (k%(q^d)) <;> simp [h,memory,hb,Function.update_of_ne he]

def setup : Command := straight [
  .binary 8 .rem (.register 0) (.register 3),.assign 9 (.literal 0)]
def erase : Command := straight [
  .binary 11 .add (.register 2) (.register 0),.store (.register 11) (.literal 0)]
def conditional : Command := .ite .lt (.register 4) (.register 9) erase .skip
def body (q : ℕ) : Command := .seq setup (.seq (DigitSum.loop q)
  (.seq conditional (.atom (.binary 0 .add (.register 0) (.literal 1)))))
def loop (q : ℕ) : Command := .loop .lt (.register 0) (.register 1) (body q)
def command (q : ℕ) : Command := .seq (.atom (.assign 0 (.literal 0))) (loop q)

lemma setup_correct {w k Q : ℕ} (s : Data) (hk : k<wordModulus w) (hQ : Q<wordModulus w) (hQpos : 0<Q)
    (h0 : s.registers 0=k) (h3 : s.registers 3=Q) :
    Eval w setup s 2 (put (put s 8 (k%Q)) 9 0) := by
  apply straight_correct
  simp [execStraight,Atom.eval,operand_register,operand_literal,evalBinOp,put,h0,h3,
    Nat.mod_eq_of_lt hk,Nat.mod_eq_of_lt hQ,hQpos.ne']

lemma erase_correct {w P k : ℕ} (s : Data) (hPk : P+k<wordModulus w)
    (h0 : s.registers 0=k) (h2 : s.registers 2=P) :
    Eval w erase s 2 {registers:=Function.update s.registers 11 (P+k),memory:=Function.update s.memory (P+k) (some 0)} := by
  apply straight_correct
  simp [execStraight,Atom.eval,operand_register,operand_literal,evalBinOp,put,h0,h2,
    Nat.mod_eq_of_lt hPk,Nat.mod_eq_of_lt (show P<wordModulus w by omega),Nat.mod_eq_of_lt (show k<wordModulus w by omega)]

lemma conditional_correct {w P k D H : ℕ} (s : Data) (hPk : P+k<wordModulus w)
    (hD : D<wordModulus w) (hH : H<wordModulus w)
    (h0 : s.registers 0=k) (h2 : s.registers 2=P) (h4 : s.registers 4=D) (h9 : s.registers 9=H) :
    ∃ cost z, Eval w conditional s cost z ∧ cost≤4 ∧
      z.memory=(if D<H then Function.update s.memory (P+k) (some 0) else s.memory) ∧
      (∀ r, r≠11 → z.registers r=s.registers r) := by
  have ht : test w s .lt (.register 4) (.register 9)=decide (D<H) := by
    simp [test,operand_register,evalTest,h4,h9,Nat.mod_eq_of_lt hD,Nat.mod_eq_of_lt hH]
  by_cases h : D<H
  · refine ⟨4,_,Eval.iteTrue (by simpa [h] using ht) (erase_correct s hPk h0 h2),by omega,by simp [h],?_⟩
    intro r hr; exact Function.update_of_ne hr _ _
  · exact ⟨1,s,Eval.iteFalse (by simpa [h] using ht) (Eval.skip s),by omega,by simp [h],by simp⟩

lemma body_correct {w q d P k D N : ℕ} (s : Data)
    (hq : 1 < q) (hqw : q<wordModulus w) (hQ : q^d<wordModulus w)
    (hP : P+N<wordModulus w) (hk : k<N) (hD : D<wordModulus w)
    (h0 : s.registers 0=k) (h2 : s.registers 2=P) (h3 : s.registers 3=q^d) (h4 : s.registers 4=D) :
    ∃ cost z, Eval w (body q) s cost z ∧ cost≤5*d+8 ∧ z.registers 0=k+1 ∧
      z.memory=(if D<DigitSum.value q d (k%(q^d)) then Function.update s.memory (P+k) (some 0) else s.memory) ∧
      (∀ r, r≠0 → r<8 ∨ 12≤r → z.registers r=s.registers r) := by
  have hkW : k<wordModulus w := by omega
  have hQpos : 0<q^d := pow_pos (by omega : 0<q) d
  have hmod : k%(q^d)<q^d := Nat.mod_lt _ hQpos
  let u:=put (put s 8 (k%(q^d))) 9 0
  have he0:=setup_correct s hkW hQ hQpos h0 h3
  obtain ⟨c,v,he,hc,hm,hv8,hv9,hf⟩:=DigitSum.loop_correct hq hqw d (k%(q^d)) 0 u hmod (hmod.trans hQ)
    (by simpa only [Nat.zero_add] using (DigitSum.value_le hq d (k%(q^d))).trans_lt (hmod.trans hQ))
    (by simp [u,put]) (by simp [u,put])
  have hv : ∀ r, r<8 ∨ 12≤r → v.registers r=s.registers r := by
    intro r hr
    rw [hf r (by omega) (by omega) (by omega)]
    simp [u,put,show r≠8 by omega,show r≠9 by omega]
  obtain ⟨ce,z,hee,hce,hmz,hfz⟩:=conditional_correct (H:=DigitSum.value q d (k%(q^d))) v (by omega) hD
    ((DigitSum.value_le hq d (k%(q^d))).trans_lt (hmod.trans hQ))
    ((hv 0 (by omega)).trans h0) ((hv 2 (by omega)).trans h2) ((hv 4 (by omega)).trans h4)
    (by simpa only [Nat.zero_add] using hv9)
  have hz0 : z.registers 0=k := (hfz 0 (by omega)).trans ((hv 0 (by omega)).trans h0)
  let z' := put z 0 (k+1)
  have heinc : Eval w (.atom (.binary 0 .add (.register 0) (.literal 1))) z 1 z' := by
    apply Eval.atom
    simp [Atom.eval,z',put,evalBinOp,operand_register,operand_literal,hz0,Nat.mod_eq_of_lt hkW,
      Nat.mod_eq_of_lt (show 1<wordModulus w by omega),Nat.mod_eq_of_lt (show k+1<wordModulus w by omega)]
  refine ⟨2+(c+(ce+1)),z',Eval.seq he0 (Eval.seq he (Eval.seq hee heinc)),by omega,by simp [z',put],?_,?_⟩
  · change z.memory=_
    rw [hmz,hm]
    rfl
  · intro r hr0 hr
    simp only [z',put,Function.update_of_ne hr0]
    rw [hfz r (by omega),hv r hr]
end DeterministicThreeSum.Structured.Indexed.DegreeFilter
namespace DeterministicThreeSum.Structured.Indexed.DegreeFilter
open Command

theorem command_correct {w q d P D N : ℕ} (s : Data)
    (hq : 1 < q) (hqw : q<wordModulus w) (hQ : q^d<wordModulus w)
    (hP : P+N<wordModulus w) (hD : D<wordModulus w)
    (h1 : s.registers 1=N) (h2 : s.registers 2=P) (h3 : s.registers 3=q^d) (h4 : s.registers 4=D) :
    ∃ cost z, Eval w (command q) s cost z ∧ cost≤(5*d+10)*N+2 ∧
      z.registers 0=N ∧ z.memory=memory q d D P N s.memory ∧
      (∀ r, r≠0 → r<8 ∨ 12≤r → z.registers r=s.registers r) := by
  let Inv:=fun (i : ℕ) (t : Data) => t.registers 0=i ∧
    (∀ r, r≠0 → r<8 ∨ 12≤r → t.registers r=s.registers r) ∧
    t.memory=memory q d D P i s.memory
  have hyes : ∀ k t, k<N → Inv k t → test w t .lt (.register 0) (.register 1)=true := by
    intro k t hk ht
    have ht1 := ht.2.1 1 (by omega) (by omega)
    simp [test,operand_register,evalTest,ht.1,ht1,h1,Nat.mod_eq_of_lt (show k<wordModulus w by omega),
      Nat.mod_eq_of_lt (show N<wordModulus w by omega),hk]
  have hno : ∀ t, Inv N t → test w t .lt (.register 0) (.register 1)=false := by
    intro t ht
    have ht1:=ht.2.1 1 (by omega) (by omega)
    simp [test,operand_register,evalTest,ht.1,ht1,h1]
  have hb : ∀ k t, k<N → Inv k t → ∃ cost z, Eval w (body q) t cost z ∧ cost≤5*d+8 ∧ Inv (k+1) z := by
    intro k t hk ht
    obtain ⟨c,z,he,hc,hz0,hm,hf⟩:=body_correct t hq hqw hQ hP hk hD ht.1
      ((ht.2.1 2 (by omega) (by omega)).trans h2)
      ((ht.2.1 3 (by omega) (by omega)).trans h3)
      ((ht.2.1 4 (by omega) (by omega)).trans h4)
    refine ⟨c,z,he,hc,hz0,?_,?_⟩
    · intro r hr0 hr
      exact (hf r hr0 hr).trans (ht.2.1 r hr0 hr)
    · rw [hm,ht.2.2,memory_succ]
  let u:=put s 0 0
  have hinit : Eval w (.atom (.assign 0 (.literal 0))) s 1 u := by
    simpa [u,operand_literal] using eval_assign (w:=w) s 0 (.literal 0)
  have hu : Inv 0 u := by
    refine ⟨by simp [u,put],?_,?_⟩
    · intro r hr0 hr; simp [u,put,hr0]
    · exact (memory_zero q d D P s.memory).symm
  obtain ⟨c,z,he,hc,hz⟩:=bounded_loop (N:=N) (B:=5*d+8) Inv hyes hno hb (i:=0) (by omega) hu
  have hc' : c≤(5*d+10)*N+1 := by
    simpa only [Nat.sub_zero,show 5*d+8+2=5*d+10 by omega] using hc
  refine ⟨1+c,z,Eval.seq hinit he,by omega,hz.1,hz.2.2,hz.2.1⟩

lemma memory_entry {q d D P N i : ℕ} (mem : ℕ → Option ℕ) (hi : i<N) :
    memory q d D P N mem (P+i)=
      if D<DigitSum.value q d (i%(q^d)) then some 0 else mem (P+i) := by
  simp [memory,hi]

lemma memory_outside {q d D P N a : ℕ} (mem : ℕ → Option ℕ) (ha : a<P ∨ P+N≤a) :
    memory q d D P N mem a=mem a := by
  simp only [memory]
  rw [ite_eq_right (by omega)]
end DeterministicThreeSum.Structured.Indexed.DegreeFilter

end OAI
