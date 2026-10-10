import Mathlib
import OAI.Computability.DeterministicSum.WordArithmetic
import OAI.Computability.DeterministicSum.PrunedTree

namespace OAI

/-! Instruction-level prefix enumeration and bounded level traversal. -/

namespace DeterministicThreeSum.Structured.Pruned
open Command DeterministicThreeSum.Pruned

def Stored (s : Data) (P : ℕ) (l : List Node) : Prop :=
  ∀ i (hi : i<l.length), s.memory (P+2*i)=some l[i].1 ∧ s.memory (P+2*i+1)=some l[i].2

def storePair (s : Data) (P j : ℕ) (p : Node) : Data :=
  {s with memory:=Function.update (Function.update s.memory (P+2*j) (some p.1)) (P+2*j+1) (some p.2)}

lemma storePair_outside (s : Data) (P j : ℕ) (p : Node) (a : ℕ)
    (ha : a<P+2*j ∨ P+2*j+2≤a) : (storePair s P j p).memory a=s.memory a := by
  simp only [storePair,Function.update_of_ne (by omega : a≠P+2*j+1),Function.update_of_ne (by omega : a≠P+2*j)]

lemma storePair_stored (s : Data) (P : ℕ) (l : List Node) (p : Node) (hs : Stored s P l) :
    Stored (storePair s P l.length p) P (l++[p]) := by
  intro i hi
  by_cases h : i<l.length
  · rw [List.getElem_append_left h]
    have h0:=storePair_outside s P l.length p (P+2*i) (by omega)
    have h1:=storePair_outside s P l.length p (P+2*i+1) (by omega)
    simpa only [h0,h1] using hs i h
  · have he : i=l.length := by simp only [List.length_append,List.length_singleton] at hi; omega
    subst i
    simp [storePair,List.getElem_append_right (by omega : l.length≤l.length)]

lemma stored_nil (s : Data) (P : ℕ) : Stored s P [] := by intro i hi; simp at hi

def pushDigit (r v : ℕ) : Command := straight [
  .binary 11 .mul (.register 8) (.literal r),
  .binary 11 .add (.register 11) (.literal v),
  .binary 12 .mul (.register 6) (.literal 2),
  .binary 12 .add (.register 3) (.register 12),
  .store (.register 12) (.register 11),
  .binary 12 .add (.register 12) (.literal 1),
  .store (.register 12) (.register 10),
  .binary 6 .add (.register 6) (.literal 1)]

def pushDigitState (s : Data) (r v P j c degree : ℕ) : Data :=
  put (put (put (put (put (put (storePair s P j (c*r+v,degree)) 11 (c*r)) 11 (c*r+v)) 12 (2*j))
    12 (P+2*j)) 12 (P+2*j+1)) 6 (j+1)

lemma pushDigit_correct {w r v P j c degree : ℕ} (s : Data)
    (hW : 2<wordModulus w) (hr : r<wordModulus w) (hv : v<wordModulus w)
    (hP : P+2*j+1<wordModulus w) (hc : c*r+v<wordModulus w)
    (hc' : c<wordModulus w) (hd : degree<wordModulus w)
    (h3 : s.registers 3=P) (h6 : s.registers 6=j)
    (h8 : s.registers 8=c) (h10 : s.registers 10=degree) :
    Eval w (pushDigit r v) s 8 (pushDigitState s r v P j c degree) := by
  apply straight_correct
  have hj' : j+1<wordModulus w := by omega
  have h1 : 2*j<wordModulus w := by omega
  have h2 : P+2*j<wordModulus w := by omega
  have hcr : c*r<wordModulus w := by omega
  simp [pushDigitState,storePair,execStraight,Atom.eval,operand_register,operand_literal,evalBinOp,put,
    h3,h6,h8,h10,show j*2=2*j by omega,Nat.mod_eq_of_lt hW,Nat.mod_eq_of_lt hr,Nat.mod_eq_of_lt hv,
    Nat.mod_eq_of_lt hP,Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt hc',Nat.mod_eq_of_lt hd,
    Nat.mod_eq_of_lt hj',Nat.mod_eq_of_lt h1,
    Nat.mod_eq_of_lt h2,Nat.mod_eq_of_lt hcr]

def tryDigit (r v weight : ℕ) : Command :=
  .seq (.atom (.binary 10 .add (.register 9) (.literal weight)))
    (.ite .le (.register 10) (.register 2) (pushDigit r v) .skip)

lemma tryDigit_writes (r v weight : ℕ) : (tryDigit r v weight).writes={6,10,11,12} := by
  simp [tryDigit,pushDigit,straight_writes,Command.writes,Atom.writes]
  decide

theorem tryDigit_correct {w r v weight D P c degree : ℕ} (s : Data) (l : List Node)
    (hW : 2<wordModulus w) (hr : r<wordModulus w) (hv : v<wordModulus w)
    (hP : P+2*l.length+1<wordModulus w) (hc : c*r+v<wordModulus w)
    (hc' : c<wordModulus w) (hd : degree+weight<wordModulus w)
    (hD : D<wordModulus w)
    (h2 : s.registers 2=D) (h3 : s.registers 3=P) (h6 : s.registers 6=l.length)
    (h8 : s.registers 8=c) (h9 : s.registers 9=degree) (hm : Stored s P l) :
    ∃ cost t, Eval w (tryDigit r v weight) s cost t ∧ cost≤11 ∧
      (∀ j, j≠6 → j≠10 → j≠11 → j≠12 → t.registers j=s.registers j) ∧
      let out:=l++(if degree+weight≤D then [(c*r+v,degree+weight)] else [])
      t.registers 6=out.length ∧ Stored t P out ∧
      (∀ a, (a<P+2*l.length ∨ P+2*out.length≤a) → t.memory a=s.memory a) := by
  let s1:=put s 10 (degree+weight)
  have e1 : Eval w (.atom (.binary 10 .add (.register 9) (.literal weight))) s 1 s1 := by
    apply Eval.atom
    simp [Atom.eval,evalBinOp,operand_register,operand_literal,h9,Nat.mod_eq_of_lt hd,
      Nat.mod_eq_of_lt (show degree<wordModulus w by omega),Nat.mod_eq_of_lt (show weight<wordModulus w by omega),s1]
  by_cases h : degree+weight≤D
  · have ht : test w s1 .le (.register 10) (.register 2)=true := by
      simp [test,operand_register,evalTest,s1,put,h2,Nat.mod_eq_of_lt hd,Nat.mod_eq_of_lt hD,h]
    have ep:=pushDigit_correct s1 hW hr hv hP hc hc' hd
      (by simp [s1,put,h3]) (by simp [s1,put,h6]) (by simp [s1,put,h8]) (by simp [s1,put])
    let t:=pushDigitState s1 r v P l.length c (degree+weight)
    have he : Eval w (tryDigit r v weight) s 11 t := Eval.seq e1 (Eval.iteTrue ht ep)
    refine ⟨11,t,he,by omega,?_,?_,?_,?_⟩
    · intro j h6 h10 h11 h12
      exact register_frame he (by simp [tryDigit_writes,h6,h10,h11,h12])
    · simp [t,pushDigitState,put,h]
    · simpa [t,pushDigitState,Stored,put,s1,storePair,h] using storePair_stored s P l (c*r+v,degree+weight) hm
    · intro a ha
      have ha' : a<P+2*l.length ∨ P+2*l.length+2≤a := by simpa [h,Nat.mul_add,Nat.add_assoc] using ha
      exact storePair_outside s P l.length (c*r+v,degree+weight) a ha'
  · have ht : test w s1 .le (.register 10) (.register 2)=false := by
      simp [test,operand_register,evalTest,s1,put,h2,Nat.mod_eq_of_lt hd,Nat.mod_eq_of_lt hD,h]
    have he : Eval w (tryDigit r v weight) s 2 s1 := Eval.seq e1 (Eval.iteFalse ht (Eval.skip s1))
    refine ⟨2,s1,he,by omega,?_,?_,?_,?_⟩
    · intro j h6 h10 h11 h12
      exact register_frame he (by simp [tryDigit_writes,h6,h10,h11,h12])
    · simp [s1,put,h,h6]
    · simpa [s1,put,h,Stored] using hm
    · intro a ha; rfl

end DeterministicThreeSum.Structured.Pruned
namespace DeterministicThreeSum.Structured.Pruned
open Command DeterministicThreeSum.Pruned

def accepted (A : Alphabet) (D : ℕ) (p : Node) (vs : List ℕ) : List Node :=
  (vs.filter (fun v => p.2+A.weight v≤D)).map (next A p)

lemma accepted_length (A : Alphabet) (D : ℕ) (p : Node) (vs : List ℕ) :
    (accepted A D p vs).length≤vs.length := by
  simpa [accepted] using List.length_filter_le (fun v => decide (p.2+A.weight v≤D)) vs

lemma accepted_cons (A : Alphabet) (D : ℕ) (p : Node) (v : ℕ) (vs : List ℕ) :
    accepted A D p (v::vs)=(if p.2+A.weight v≤D then [next A p v] else [])++accepted A D p vs := by
  simp only [accepted,List.filter_cons]
  split <;> simp_all

def childrenCode (A : Alphabet) : List ℕ → Command
  | [] => .skip
  | v::vs => .seq (tryDigit A.radix v (A.weight v)) (childrenCode A vs)

theorem childrenCode_correct {w D P : ℕ} (A : Alphabet) (s : Data) (l : List Node) (p : Node) (vs : List ℕ)
    (hW : 2<wordModulus w) (hr : A.radix<wordModulus w)
    (hvs : ∀ v∈vs, v<A.radix) (hP : P+2*(l.length+vs.length)+1<wordModulus w)
    (hc : ∀ v∈vs, p.1*A.radix+v<wordModulus w)
    (hc' : p.1<wordModulus w) (hd : ∀ v∈vs, p.2+A.weight v<wordModulus w)
    (hD : D<wordModulus w)
    (h2 : s.registers 2=D) (h3 : s.registers 3=P) (h6 : s.registers 6=l.length)
    (h8 : s.registers 8=p.1) (h9 : s.registers 9=p.2) (hm : Stored s P l) :
    ∃ cost t, Eval w (childrenCode A vs) s cost t ∧ cost≤11*vs.length ∧
      (∀ j, j≠6 → j≠10 → j≠11 → j≠12 → t.registers j=s.registers j) ∧
      t.registers 6=(l++accepted A D p vs).length ∧ Stored t P (l++accepted A D p vs) ∧
      (∀ a, (a<P+2*l.length ∨ P+2*(l++accepted A D p vs).length≤a) → t.memory a=s.memory a) := by
  induction vs generalizing s l with
  | nil => exact ⟨0,s,Eval.skip s,by simp,by simp,by simpa [accepted] using h6,by simpa [accepted] using hm,by simp⟩
  | cons v vs ih =>
    have hv : v∈v::vs := by simp
    obtain ⟨c,t,et,hct,hframe,ht,hm',hout⟩:=tryDigit_correct s l hW hr ((hvs v hv).trans hr)
      (by simp only [List.length_cons] at hP; omega) (hc v hv) hc' (hd v hv) hD h2 h3 h6 h8 h9 hm
    let l' := l++(if p.2+A.weight v≤D then [next A p v] else [])
    have hl' : l'.length≤l.length+1 := by dsimp [l']; split_ifs <;> simp
    have hl : l.length≤l'.length := by dsimp [l']; simp
    have ht' : t.registers 6=l'.length := ht
    have hm'' : Stored t P l' := hm'
    have hP' : P+2*(l'.length+vs.length)+1<wordModulus w := by
      simp only [List.length_cons] at hP; omega
    obtain ⟨c',u,eu,hcu,hframe',hu,hmu,hout'⟩:=ih t l'
      (by intro j hj; exact hvs j (by simp [hj])) hP'
      (by intro j hj; exact hc j (by simp [hj]))
      (by intro j hj; exact hd j (by simp [hj]))
      ((hframe 2 (by omega) (by omega) (by omega) (by omega)).trans h2)
      ((hframe 3 (by omega) (by omega) (by omega) (by omega)).trans h3) ht'
      ((hframe 8 (by omega) (by omega) (by omega) (by omega)).trans h8)
      ((hframe 9 (by omega) (by omega) (by omega) (by omega)).trans h9) hm''
    have heq : l++accepted A D p (v::vs)=l'++accepted A D p vs := by rw [accepted_cons,List.append_assoc]
    refine ⟨c+c',u,Eval.seq et eu,by simp only [List.length_cons]; omega,?_,?_,?_,?_⟩
    · intro j h6 h10 h11 h12
      exact (hframe' j h6 h10 h11 h12).trans (hframe j h6 h10 h11 h12)
    · rwa [heq]
    · rwa [heq]
    · intro a ha
      rw [heq] at ha
      rw [hout' a (by omega)]
      exact hout a (by simp only [List.length_append] at ha; change a<P+2*l.length ∨ P+2*l'.length≤a; omega)

end DeterministicThreeSum.Structured.Pruned
namespace DeterministicThreeSum.Structured.Pruned
open Command DeterministicThreeSum.Pruned

def loadPrefix : Command := straight [
  .binary 10 .mul (.register 0) (.literal 2),
  .binary 10 .add (.register 4) (.register 10),
  .load 8 (.register 10),
  .binary 10 .add (.register 10) (.literal 1),
  .load 9 (.register 10)]

def loadPrefixState (s : Data) (S i : ℕ) (p : Node) : Data :=
  put (put (put (put (put s 10 (2*i)) 10 (S+2*i)) 8 p.1) 10 (S+2*i+1)) 9 p.2

lemma loadPrefix_correct {w S i : ℕ} (s : Data) (p : Node)
    (hW : 2<wordModulus w) (hS : S+2*i+1<wordModulus w)
    (h0 : s.registers 0=i) (h4 : s.registers 4=S)
    (hm : s.memory (S+2*i)=some p.1 ∧ s.memory (S+2*i+1)=some p.2) :
    Eval w loadPrefix s 5 (loadPrefixState s S i p) := by
  apply straight_correct
  simp [loadPrefixState,execStraight,Atom.eval,operand_register,operand_literal,evalBinOp,put,
    h0,h4,show i*2=2*i by omega,Nat.mod_eq_of_lt hW,Nat.mod_eq_of_lt hS,
    Nat.mod_eq_of_lt (show i<wordModulus w by omega),
    Nat.mod_eq_of_lt (show 2*i<wordModulus w by omega),Nat.mod_eq_of_lt (show S+2*i<wordModulus w by omega),
    Nat.mod_eq_of_lt (show 1<wordModulus w by omega),hm.1,hm.2]

lemma childrenCode_writes (A : Alphabet) (vs : List ℕ) :
    (childrenCode A vs).writes⊆({6,10,11,12}:Finset ℕ) := by
  induction vs with
  | nil => simp [childrenCode,Command.writes]
  | cons v vs ih => simp [childrenCode,Command.writes,tryDigit_writes,Finset.insert_subset_iff,ih]

def expandStep (A : Alphabet) : Command := .seq loadPrefix (childrenCode A (List.range A.radix))

lemma expandStep_writes (A : Alphabet) : (expandStep A).writes⊆({6,8,9,10,11,12}:Finset ℕ) := by
  intro j hj
  simp only [expandStep,Command.writes,Finset.mem_union] at hj
  rcases hj with hj|hj
  · simp [loadPrefix,straight_writes,Atom.writes] at hj
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  · have h:=childrenCode_writes A (List.range A.radix) hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at h ⊢
    omega

theorem expandStep_correct {w D P S i : ℕ} (A : Alphabet) (s : Data) (l : List Node) (p : Node)
    (hW : 2<wordModulus w) (hr : A.radix<wordModulus w)
    (hP : P+2*(l.length+A.radix)+1<wordModulus w) (hS : S+2*i+1<wordModulus w)
    (hc : ∀ v, v<A.radix → p.1*A.radix+v<wordModulus w)
    (hc' : p.1<wordModulus w) (hd : ∀ v, v<A.radix → p.2+A.weight v<wordModulus w)
    (hD : D<wordModulus w)
    (h0 : s.registers 0=i) (h2 : s.registers 2=D) (h3 : s.registers 3=P)
    (h4 : s.registers 4=S) (h6 : s.registers 6=l.length)
    (hp : s.memory (S+2*i)=some p.1 ∧ s.memory (S+2*i+1)=some p.2)
    (hm : Stored s P l) :
    ∃ cost t, Eval w (expandStep A) s cost t ∧ cost≤5+11*A.radix ∧
      (∀ j, j<8 → j≠6 → t.registers j=s.registers j) ∧
      t.registers 6=(l++children A D p).length ∧ Stored t P (l++children A D p) ∧
      (∀ a, (a<P+2*l.length ∨ P+2*(l++children A D p).length≤a) → t.memory a=s.memory a) := by
  have he:=loadPrefix_correct s p hW hS h0 h4 hp
  obtain ⟨cost,t,et,hcost,hframe,ht,hm',hout⟩:=childrenCode_correct A (loadPrefixState s S i p) l p (List.range A.radix)
    hW hr (by simp) (by simpa using hP) (by simpa using hc) hc' (by simpa using hd) hD
    (by simp [loadPrefixState,put,h2]) (by simp [loadPrefixState,put,h3])
    (by simp [loadPrefixState,put,h6]) (by simp [loadPrefixState,put]) (by simp [loadPrefixState,put])
    (by simpa [loadPrefixState,put,Stored] using hm)
  have hall : Eval w (expandStep A) s (5+cost) t := Eval.seq he et
  refine ⟨5+cost,t,hall,by simpa using Nat.add_le_add_left hcost 5,?_,ht,hm',hout⟩
  intro j hj h6
  exact register_frame hall (by intro h; have hh:=expandStep_writes A h; simp only [Finset.mem_insert,Finset.mem_singleton] at hh; omega)

lemma expand_take (A : Alphabet) (D : ℕ) (l : List Node) {i : ℕ} (hi : i<l.length) :
    expand A D (l.take (i+1))=expand A D (l.take i)++children A D l[i] := by
  rw [List.take_succ_eq_append_getElem hi,expand_append]
  simp [expand]

def expandLoop (A : Alphabet) : Command := .loop .lt (.register 0) (.register 1)
  (.seq (expandStep A) (.atom (.binary 0 .add (.register 0) (.literal 1))))

theorem expandLoop_correct {w D P S : ℕ} (A : Alphabet) (s : Data) (l : List Node)
    (hW : 2<wordModulus w) (hr : A.radix<wordModulus w)
    (hP : P+2*(l.length*A.radix)+1<wordModulus w) (hS : S+2*l.length+1<wordModulus w)
    (hdis : P+2*(l.length*A.radix)≤S ∨ S+2*l.length≤P)
    (hc : ∀ p∈l, ∀ v, v<A.radix → p.1*A.radix+v<wordModulus w)
    (hc' : ∀ p∈l, p.1<wordModulus w)
    (hd : ∀ p∈l, ∀ v, v<A.radix → p.2+A.weight v<wordModulus w)
    (hD : D<wordModulus w)
    (h0 : s.registers 0=0) (h1 : s.registers 1=l.length)
    (h2 : s.registers 2=D) (h3 : s.registers 3=P) (h4 : s.registers 4=S) (h6 : s.registers 6=0)
    (hm : Stored s S l) :
    ∃ cost t, Eval w (expandLoop A) s cost t ∧ cost≤(11*A.radix+8)*l.length+1 ∧
      (∀ j, j<8 → j≠0 → j≠6 → t.registers j=s.registers j) ∧ t.registers 0=l.length ∧
      t.registers 6=(expand A D l).length ∧ Stored t P (expand A D l) ∧
      (∀ a, (a<P ∨ P+2*(l.length*A.radix)≤a) → t.memory a=s.memory a) := by
  let Inv : ℕ → Data → Prop := fun i t =>
    (∀ j, j<8 → j≠0 → j≠6 → t.registers j=s.registers j) ∧ t.registers 0=i ∧
    t.registers 6=(expand A D (l.take i)).length ∧ Stored t P (expand A D (l.take i)) ∧ Stored t S l ∧
    (∀ a, (a<P ∨ P+2*(l.length*A.radix)≤a) → t.memory a=s.memory a)
  have hN : l.length+1<wordModulus w := by omega
  have hyes : ∀ i t, i<l.length → Inv i t → test w t .lt (.register 0) (.register 1)=true := by
    intro i t hi ht
    have hh:=ht.1 1 (by omega) (by omega) (by omega)
    simp [test,operand_register,evalTest,ht.2.1,hh,h1,
      Nat.mod_eq_of_lt (show i<wordModulus w by omega),Nat.mod_eq_of_lt (show l.length<wordModulus w by omega),hi]
  have hno : ∀ t, Inv l.length t → test w t .lt (.register 0) (.register 1)=false := by
    intro t ht
    simp [test,operand_register,evalTest,ht.2.1,ht.1 1 (by omega) (by omega) (by omega),h1]
  have hbody : ∀ i t, i<l.length → Inv i t → ∃ cost u,
      Eval w (.seq (expandStep A) (.atom (.binary 0 .add (.register 0) (.literal 1)))) t cost u ∧
      cost≤11*A.radix+6 ∧ Inv (i+1) u := by
    intro i t hi ht
    let out:=expand A D (l.take i)
    have hlen : out.length≤ i*A.radix := by simpa [out,List.length_take, min_eq_left hi.le] using expand_length_le A D (l.take i)
    have hlen' : (out++children A D l[i]).length≤l.length*A.radix := by
      have hh:=children_length_le A D l[i]
      have hb:=Nat.mul_le_mul_right A.radix (show i+1≤l.length by omega)
      simp only [List.length_append]; nlinarith only [hlen,hh,hb]
    have hp : l[i]∈l := List.getElem_mem ..
    have hP' : P+2*(out.length+A.radix)+1<wordModulus w := by
      have hb:=Nat.mul_le_mul_right A.radix (show i+1≤l.length by omega)
      nlinarith only [hP,hlen,hb]
    obtain ⟨c,u,eu,hcu,hfr,hu,hmu,hout⟩:=expandStep_correct A t out l[i] hW hr hP' (by omega)
      (hc _ hp) (hc' _ hp) (hd _ hp) hD ht.2.1
      ((ht.1 2 (by omega) (by omega) (by omega)).trans h2)
      ((ht.1 3 (by omega) (by omega) (by omega)).trans h3)
      ((ht.1 4 (by omega) (by omega) (by omega)).trans h4)
      ht.2.2.1 (ht.2.2.2.2.1 i hi) ht.2.2.2.1
    have hidx : u.registers 0=i := (hfr 0 (by omega) (by omega)).trans ht.2.1
    have einc:=eval_increment (w:=w) (s:=u) (r:=0) (by rw [hidx]; omega)
    rw [hidx] at einc
    refine ⟨c+1,put u 0 (i+1),Eval.seq eu einc,by omega,?_,?_,?_,?_,?_,?_⟩
    · intro j hj hj0 hj6
      simp only [put,Function.update_of_ne hj0]
      exact (hfr j hj hj6).trans (ht.1 j hj hj0 hj6)
    · simp [put]
    · simpa only [put,Function.update_of_ne (by omega : 6≠0),expand_take A D l hi] using hu
    · simpa only [put,Stored,expand_take A D l hi] using hmu
    · intro j hj
      have hS0 : u.memory (S+2*j)=t.memory (S+2*j) := hout _ (by omega)
      have hS1 : u.memory (S+2*j+1)=t.memory (S+2*j+1) := hout _ (by omega)
      simpa only [put,hS0,hS1] using ht.2.2.2.2.1 j hj
    · intro a ha
      change u.memory a=s.memory a
      rw [hout a (by omega)]
      exact ht.2.2.2.2.2 a ha
  have hstart : Inv 0 s := by
    refine ⟨by simp,h0,?_,?_,hm,by simp⟩
    · simpa [expand] using h6
    · simpa [expand] using stored_nil s P
  obtain ⟨cost,t,he,hcost,ht⟩:=bounded_loop Inv hyes hno hbody (i:=0) (by omega) hstart
  refine ⟨cost,t,he,by simpa using hcost,ht.1,ht.2.1,?_,?_,ht.2.2.2.2.2⟩
  · simpa using ht.2.2.1
  · simpa using ht.2.2.2.1

end DeterministicThreeSum.Structured.Pruned
namespace DeterministicThreeSum.Structured.Pruned
open Command DeterministicThreeSum.Pruned

def levels (A : Alphabet) (D : ℕ) : ℕ → List Node → List Node
  | 0,l => l
  | m+1,l => levels A D m (expand A D l)

def banks (m P S : ℕ) : ℕ × ℕ := if Even m then (P,S) else (S,P)
lemma banks_zero (P S : ℕ) : banks 0 P S=(P,S) := by simp [banks]
lemma banks_succ (m P S : ℕ) : banks (m+1) P S=banks m S P := by
  simp only [banks,Nat.even_add_one]
  by_cases h : Even m  <;> simp [h]

def levelUpdate : Command := straight [
  .assign 13 (.register 3), .assign 3 (.register 4), .assign 4 (.register 13),
  .assign 1 (.register 6), .assign 0 (.literal 0), .assign 6 (.literal 0),
  .binary 5 .sub (.register 5) (.literal 1)]

def levelUpdateState (s : Data) (P S N m : ℕ) : Data :=
  put (put (put (put (put (put (put s 13 P) 3 S) 4 P) 1 N) 0 0) 6 0) 5 m

lemma levelUpdate_correct {w P S N m : ℕ} (s : Data)
    (hW : 2 < wordModulus w) (hP : P < wordModulus w) (hS : S < wordModulus w)
    (hN : N < wordModulus w) (hm : m+1 < wordModulus w)
    (h3 : s.registers 3=P) (h4 : s.registers 4=S)
    (h5 : s.registers 5=m+1) (h6 : s.registers 6=N) :
    Eval w levelUpdate s 7 (levelUpdateState s P S N m) := by
  have he : m+1+wordModulus w-1=m+wordModulus w := by omega
  apply straight_correct
  simp [levelUpdateState,execStraight,Atom.eval,operand_register,operand_literal,
    evalBinOp,put,h3,h4,h5,h6,Nat.mod_eq_of_lt hP,Nat.mod_eq_of_lt hS,Nat.mod_eq_of_lt hN,
    Nat.mod_eq_of_lt hm,Nat.mod_eq_of_lt (show m < wordModulus w by omega),
    Nat.mod_eq_of_lt (show 1 < wordModulus w by omega),he]

def levelsCommand (A : Alphabet) : Command :=
  .loop .lt (.literal 0) (.register 5) (.seq (expandLoop A) levelUpdate)

def LevelRegs (s : Data) (D P S m N : ℕ) : Prop :=
  s.registers 0=0 ∧ s.registers 1=N ∧ s.registers 2=D ∧ s.registers 3=P ∧
  s.registers 4=S ∧ s.registers 5=m ∧ s.registers 6=0

theorem levelsCommand_correct {w D K : ℕ} (A : Alphabet) (m : ℕ)
    (hW : 2 < wordModulus w) (hr : 0 < A.radix) (hrW : A.radix < wordModulus w)
    (hD : D < wordModulus w) (hm : m < wordModulus w) :
    ∀ (s : Data) (l : List Node) (P S : ℕ),
    P+2*K*A.radix+1 < wordModulus w → S+2*K*A.radix+1 < wordModulus w →
    (P+2*K*A.radix ≤ S ∨ S+2*K*A.radix ≤ P) →
    (∀ i, i ≤ m → (levels A D i l).length ≤ K) →
    (∀ i, i < m → ∀ p∈levels A D i l, ∀ v, v < A.radix → p.1*A.radix+v < wordModulus w) →
    (∀ i, i < m → ∀ p∈levels A D i l, p.1 < wordModulus w) →
    (∀ i, i < m → ∀ p∈levels A D i l, ∀ v, v < A.radix → p.2+A.weight v < wordModulus w) →
    LevelRegs s D P S m l.length → Stored s S l →
    ∃ cost t, Eval w (levelsCommand A) s cost t ∧
      cost ≤ m*((11*A.radix+8)*K+10)+1 ∧
      LevelRegs t D (banks m P S).1 (banks m P S).2 0 (levels A D m l).length ∧
      Stored t (banks m P S).2 (levels A D m l) ∧
      (∀ a, (a < P ∨ P+2*K*A.radix ≤ a) → (a < S ∨ S+2*K*A.radix ≤ a) → t.memory a=s.memory a) := by
  induction m with
  | zero =>
    intro s l P S hP hS hdis hlen hc hc' hd hreg hmem
    have ht : test w s .lt (.literal 0) (.register 5)=false := by
      simp [test,operand_literal,operand_register,evalTest,hreg.2.2.2.2.2.1]
    exact ⟨1,s,Eval.loopFalse ht,by simp,by simpa [levels,banks_zero] using hreg,
      by simpa [levels,banks_zero] using hmem,by simp⟩
  | succ m ih =>
    intro s l P S hP hS hdis hlen hc hc' hd hreg hmem
    simp only [Nat.mul_assoc] at hP hS hdis
    have hlt : l.length ≤ K := hlen 0 (by omega)
    have hKr : K ≤ K*A.radix := by simpa using Nat.mul_le_mul_left K hr
    have hlr : l.length*A.radix ≤ K*A.radix := Nat.mul_le_mul_right A.radix hlt
    have ht : test w s .lt (.literal 0) (.register 5)=true := by
      simp [test,operand_literal,operand_register,evalTest,hreg.2.2.2.2.2.1,Nat.mod_eq_of_lt hm]
    obtain ⟨c,u,eu,hcost,hframe,hi,hu,hmu,hout⟩:=expandLoop_correct A s l hW hrW
      (by nlinarith only [hP,hlr]) (by nlinarith only [hS,hlt,hKr]) (by omega)
      (hc 0 (by omega)) (hc' 0 (by omega)) (hd 0 (by omega)) hD
      hreg.1 hreg.2.1 hreg.2.2.1 hreg.2.2.2.1 hreg.2.2.2.2.1 hreg.2.2.2.2.2.2 hmem
    have hnew : (expand A D l).length ≤ K := by simpa [levels] using hlen 1 (by omega)
    have h3 : u.registers 3=P := (hframe 3 (by omega) (by omega) (by omega)).trans hreg.2.2.2.1
    have h4 : u.registers 4=S := (hframe 4 (by omega) (by omega) (by omega)).trans hreg.2.2.2.2.1
    have h5 : u.registers 5=m+1 := (hframe 5 (by omega) (by omega) (by omega)).trans hreg.2.2.2.2.2.1
    have eupdate:=levelUpdate_correct u hW (by omega) (by omega) (by omega) hm h3 h4 h5 hu
    let v:=levelUpdateState u P S (expand A D l).length m
    have hregv : LevelRegs v D S P m (expand A D l).length := by
      have h2 : u.registers 2=D := (hframe 2 (by omega) (by omega) (by omega)).trans hreg.2.2.1
      simp [v,levelUpdateState,LevelRegs,put,h2]
    obtain ⟨c',t,et,hcost',hregt,hmt,hout'⟩:=ih (by omega) v (expand A D l) S P (by simpa [Nat.mul_assoc] using hS) (by simpa [Nat.mul_assoc] using hP) (by simpa [Nat.mul_assoc] using Or.symm hdis)
      (by intro i hi; exact hlen (i+1) (by omega))
      (by intro i hi; exact hc (i+1) (by omega))
      (by intro i hi; exact hc' (i+1) (by omega))
      (by intro i hi; exact hd (i+1) (by omega)) hregv (by simpa [v,levelUpdateState,put,Stored] using hmu)
    refine ⟨1+(c+7)+1+c',t,Eval.loopTrue ht (Eval.seq eu eupdate) et,?_,?_,?_,?_⟩
    · have hh : c ≤ (11*A.radix+8)*K+1 := hcost.trans (by gcongr)
      nlinarith only [hh,hcost']
    · simpa only [banks_succ,levels] using hregt
    · simpa only [banks_succ,levels] using hmt
    · intro a ha hb
      rw [hout' a hb ha]
      simp only [Nat.mul_assoc] at ha
      exact hout a (by omega)

end DeterministicThreeSum.Structured.Pruned

namespace DeterministicThreeSum.Pruned
def scalarAlphabet (q : ℕ) : Alphabet := ⟨q,id⟩
lemma volume_append (front back : List Alphabet) : volume (front++back)=volume back*volume front := by
  induction front with
  | nil => simp [volume]
  | cons A rest ih => simp [volume,ih,Nat.mul_assoc]
lemma volume_replicate (A : Alphabet) (t : ℕ) : volume (List.replicate t A)=A.radix^t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [List.replicate_succ,volume,ih,pow_succ]
lemma volume_pos (shape : List Alphabet) (h : ∀ A∈shape, 0 < A.radix) : 0 < volume shape := by
  induction shape with
  | nil => decide
  | cons A rest ih => exact Nat.mul_pos (ih (by intro B hB; exact h B (by simp [hB]))) (h A (by simp))

end DeterministicThreeSum.Pruned
namespace DeterministicThreeSum.Structured.Pruned
open Command DeterministicThreeSum.Pruned

lemma levels_enumerate (A : Alphabet) (D i : ℕ) (rest : List Alphabet) :
    levels A D i (enumerate D rest)=enumerate D (List.replicate i A++rest) := by
  induction i generalizing rest with
  | zero => rfl
  | succ i ih =>
    rw [levels]
    change levels A D i (enumerate D (A::rest))=_
    rw [ih,List.replicate_succ']
    simp

lemma levelsCommand_writes (A : Alphabet) : (levelsCommand A).writes⊆Finset.range 14 := by
  intro r hr
  simp only [levelsCommand,expandLoop,expandStep,loadPrefix,levelUpdate,Command.writes,
    straight_writes] at hr
  have hc := childrenCode_writes A (List.range A.radix)
  simp only [List.foldr_cons,List.foldr_nil,Atom.writes,Finset.mem_union,Finset.mem_singleton,
    Finset.notMem_empty,or_false] at hr
  rcases hr with ((hr|hr)|hr)|hr
  · rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide
  · have hh:=hc hr
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with rfl|rfl|rfl|rfl <;> decide
  · subst r; decide
  · rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

lemma volume_prefix_le (front back : List Alphabet) (h : ∀ A∈front, 0 < A.radix) :
    volume back ≤ volume (front++back) := by
  rw [volume_append]
  exact le_mul_of_one_le_right (Nat.zero_le _) (volume_pos front h)

lemma repeat_remaining (A : Alphabet) {i t : ℕ} (hi : i≤t) (rest : List Alphabet) :
    List.replicate t A++rest=List.replicate (t-i) A++(List.replicate i A++rest) := by
  rw [←List.append_assoc,←List.replicate_add,Nat.sub_add_cancel hi]

theorem levelsEnumerate_correct {w D K P S t W : ℕ} (A : Alphabet) (rest : List Alphabet) (s : Data)
    (hW : 2 < wordModulus w) (hA : 0 < A.radix) (hAw : A.radix < wordModulus w)
    (hzero : A.weight 0=0) (hweight : ∀ v, v < A.radix → A.weight v≤W)
    (hrest : ∀ B∈rest, 0 < B.radix) (hD : D+W < wordModulus w) (ht : t < wordModulus w)
    (hP : P+2*K*A.radix+1 < wordModulus w) (hS : S+2*K*A.radix+1 < wordModulus w)
    (hdis : P+2*K*A.radix≤S ∨ S+2*K*A.radix≤P)
    (hK : (enumerate D (List.replicate t A++rest)).length≤K)
    (hV : volume (List.replicate t A++rest)*A.radix < wordModulus w)
    (hregs : LevelRegs s D P S t (enumerate D rest).length) (hmem : Stored s S (enumerate D rest)) :
    ∃ cost z, Eval w (levelsCommand A) s cost z ∧
      cost≤t*((11*A.radix+8)*K+10)+1 ∧
      LevelRegs z D (banks t P S).1 (banks t P S).2 0 (enumerate D (List.replicate t A++rest)).length ∧
      Stored z (banks t P S).2 (enumerate D (List.replicate t A++rest)) ∧
      (∀ a, (a < P ∨ P+2*K*A.radix≤a) → (a < S ∨ S+2*K*A.radix≤a) → z.memory a=s.memory a) := by
  have hp (i : ℕ) : ∀ B∈List.replicate i A++rest, 0 < B.radix := by
    intro B hB
    rcases List.mem_append.mp hB with hB|hB
    · obtain ⟨_,rfl⟩:=List.mem_replicate.mp hB; exact hA
    · exact hrest B hB
  have hv (i : ℕ) (hi : i≤t) : volume (List.replicate i A++rest)≤volume (List.replicate t A++rest) := by
    rw [repeat_remaining A hi]
    exact volume_prefix_le _ _ (by intro B hB; obtain ⟨_,rfl⟩:=List.mem_replicate.mp hB; exact hA)
  have hkeys (i : ℕ) (p : Node) (hpm : p∈levels A D i (enumerate D rest)) :
      p.1 < volume (List.replicate i A++rest) ∧ p.2≤D := by
    rw [levels_enumerate] at hpm
    have hh:=(enumerate_child D _ (hp i) p).mp hpm
    exact ⟨hh.1,hh.2.2⟩
  obtain ⟨c,z,he,hc,hz,hm,ho⟩:=levelsCommand_correct (K:=K) A t hW hA hAw (by omega) ht s (enumerate D rest) P S hP hS hdis
    (by
      intro i hi
      rw [levels_enumerate]
      apply le_trans _ hK
      rw [repeat_remaining A hi]
      exact length_enumerate_suffix _ _ _
        (by intro B hB; obtain ⟨_,rfl⟩:=List.mem_replicate.mp hB; exact hA)
        (by intro B hB; obtain ⟨_,rfl⟩:=List.mem_replicate.mp hB; exact hzero))
    (by
      intro i hi p hpm v hvv
      have hkey:=(hkeys i p hpm).1
      have hvol:=hv i hi.le
      have hcode : p.1*A.radix+v < volume (List.replicate t A++rest)*A.radix := by
        nlinarith only [Nat.mul_le_mul_right A.radix (show p.1+1≤volume (List.replicate t A++rest) by omega),hvv]
      exact hcode.trans hV)
    (by
      intro i hi p hpm
      have hk : p.1 < volume (List.replicate t A++rest) := (hkeys i p hpm).1.trans_le (hv i hi.le)
      exact hk.trans_le ((le_mul_of_one_le_right (Nat.zero_le _) hA).trans hV.le))
    (by intro i hi p hpm v hv; have hk:=(hkeys i p hpm).2; have hw:=hweight v hv; omega)
    hregs hmem
  exact ⟨c,z,he,hc,by simpa only [levels_enumerate] using hz,by simpa only [levels_enumerate] using hm,ho⟩

end DeterministicThreeSum.Structured.Pruned

end OAI
