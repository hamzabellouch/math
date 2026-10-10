import Mathlib
import OAI.Computability.QuantumFactoring.BitStackAdder

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def borrowBit (a b c : Bool) : Bool := (!a && b) || (!a && c) || (b && c)

lemma difference_borrow (a b c : Bool) :
    (a.toNat : ℤ)-b.toNat-c.toNat=(sumBit a b c).toNat-2*(borrowBit a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

lemma binaryValue_lt (xs : List Bool) : binaryValue xs<2^xs.length := by
  induction xs with
  | nil=>simp [binaryValue]
  | cons b bs ih=>
    simp only [List.length_cons,binaryValue,pow_succ]
    cases b <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

abbrev SubState := AddState
abbrev subStateCode := addStateCode

def subStep (s : SubState) : SubState :=
  (s.1.tail,s.2.1.tail,
    borrowBit (s.1.headD false) (s.2.1.headD false) s.2.2.1,
    sumBit (s.1.headD false) (s.2.1.headD false) s.2.2.1 :: s.2.2.2)

def subInvariant (s : SubState) : ℤ :=
  (binaryValue s.2.2.2.reverse : ℤ)+2^s.2.2.2.length*
    ((binaryValue s.1 : ℤ)-binaryValue s.2.1-s.2.2.1.toNat)

lemma subInvariant_step (s : SubState) : subInvariant (subStep s)=subInvariant s := by
  have hx:=binaryValue_head_tail s.1
  have hy:=binaryValue_head_tail s.2.1
  have hh:=difference_borrow (s.1.headD false) (s.2.1.headD false) s.2.2.1
  simp only [subInvariant,subStep,List.reverse_cons,binaryValue_append,List.length_reverse,
    binaryValue,List.length_cons,pow_succ]
  push_cast
  have hx' : (binaryValue s.1 : ℤ)=(s.1.headD false).toNat+2*binaryValue s.1.tail:=by
    exact_mod_cast hx
  have hy' : (binaryValue s.2.1 : ℤ)=(s.2.1.headD false).toNat+2*binaryValue s.2.1.tail:=by
    exact_mod_cast hy
  rw [hx',hy']
  nlinarith [congrArg (fun n : ℤ=>2^s.2.2.2.length*n) hh]

lemma subInvariant_iterate (i : ℕ) (s : SubState) :
    subInvariant (subStep^[i] s)=subInvariant s := by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',subInvariant_step,ih]

lemma subStep_tapes (i : ℕ) (s : SubState) :
    (subStep^[i] s).1=s.1.drop i ∧ (subStep^[i] s).2.1=s.2.1.drop i := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    simp only [subStep,ih.1,ih.2,List.tail_drop]
    trivial

def wordSubtract (x : List Bool×List Bool) : Bool×List Bool :=
  let s:=subStep^[x.1.length+x.2.length+1] (x.1,x.2,false,[])
  (s.2.2.1,s.2.2.2.reverse)

lemma wordSubtract_spec (x : List Bool×List Bool) :
    (binaryValue (wordSubtract x).2 : ℤ) -
      2^(wordSubtract x).2.length*((wordSubtract x).1.toNat : ℤ)=
      (binaryValue x.1 : ℤ)-binaryValue x.2 := by
  let s : SubState:=(x.1,x.2,false,[])
  let i:=x.1.length+x.2.length+1
  have hx : (subStep^[i] s).1=[]:=by
    rw [(subStep_tapes i s).1]
    exact List.drop_eq_nil_iff.mpr (by dsimp [s,i];omega)
  have hy : (subStep^[i] s).2.1=[]:=by
    rw [(subStep_tapes i s).2]
    exact List.drop_eq_nil_iff.mpr (by dsimp [s,i];omega)
  have hh:=subInvariant_iterate i s
  simp only [subInvariant,hx,hy,binaryValue,Int.natCast_zero,zero_sub] at hh
  simpa [wordSubtract,s,i,List.length_reverse,subInvariant,binaryValue,sub_eq_add_neg] using hh

lemma wordSubtract_borrow (x : List Bool×List Bool) :
    (wordSubtract x).1=decide (binaryValue x.1<binaryValue x.2) := by
  have hh:=wordSubtract_spec x
  have hl:=binaryValue_lt (wordSubtract x).2
  have hl' : (binaryValue (wordSubtract x).2 : ℤ)<2^(wordSubtract x).2.length:=by
    exact_mod_cast hl
  cases hb : (wordSubtract x).1 <;> simp only [hb,Bool.toNat_false,Bool.toNat_true,
    Int.natCast_zero,Int.natCast_one,mul_zero,mul_one,sub_zero] at hh
  · symm;apply decide_eq_false;omega
  · symm;apply decide_eq_true;omega

lemma wordSubtract_value (x : List Bool×List Bool) :
    (if (wordSubtract x).1 then 0 else binaryValue (wordSubtract x).2)=
      binaryValue x.1-binaryValue x.2 := by
  have hh:=wordSubtract_spec x
  have hb:=wordSubtract_borrow x
  cases hc : (wordSubtract x).1
  · simp only [hc,Bool.false_eq_true,ite_false,Bool.toNat_false,Int.natCast_zero,mul_zero,sub_zero] at *
    omega
  · simp only [hc,ite_true,true_eq_decide_iff] at *
    omega

lemma subStep_size (s : SubState) :
    (subStateCode (subStep s)).length≤(subStateCode s).length+1 := by
  simp only [subStateCode,addStateCode,subStep,prodCode,pairBits_length,id_eq,Procedure.boolCode,
    List.length_cons,List.length_tail]
  omega


end ExactQuantumFactoring.BitStackProgram
end

end OAI
