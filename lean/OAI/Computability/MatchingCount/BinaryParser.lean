import OAI.Computability.MatchingCount.ParserSupport

namespace OAI

section

namespace BinaryMatching.Parse
open StackCode Polynomial
abbrev RecordBits := List Bool×(List Bool×List Bool)
def recordRepr (r : Record) : RecordBits := (r.left.bits,(r.right.bits,r.multiplicity.bits))
def record (l : List Bool) : RecordBits×List Bool :=
  let a := numeral l
  let b := numeral a.2
  let c := numeral b.2
  ((a.1,(b.1,c.1)),c.2)
lemma record_encode (r : Record) (l : List Bool) : record (encodeRecord r++l)=(recordRepr r,l) := by
  unfold record encodeRecord
  simp only [List.append_assoc,numeral_encode]
  rfl
lemma record_size (l : List Bool) : (record l).2.length≤l.length ∧
    (encode (record l).1).length≤20*l.length+10 := by
  have h₁ := numeral_lengths l
  have h₂ := numeral_lengths (numeral l).2
  have h₃ := numeral_lengths (numeral (numeral l).2).2
  simp only [record,code_pair_length,cut_code_length]
  omega
@[fun_prop] theorem record_poly : Poly record := by unfold record; fun_prop

def recordStep (z : List Bool×List RecordBits) : List Bool×List RecordBits :=
  if z.1.isEmpty then z else ((record z.1).2,z.2++[(record z.1).1])
lemma recordStep_nil (k : ℕ) (l : List RecordBits) : recordStep^[k] ([],l)=([],l) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl
lemma encodeRecord_ne_nil (r : Record) : encodeRecord r≠[] := by
  simp [encodeRecord,encodeNat]
lemma recordStep_encode (r : Record) (l : List Bool) (acc : List RecordBits) :
    recordStep (encodeRecord r++l,acc)=(l,acc++[recordRepr r]) := by
  simp [recordStep, List.isEmpty_iff, List.append_eq_nil_iff, encodeRecord_ne_nil, record_encode]
lemma recordStep_records (rs : List Record) (acc : List RecordBits) :
    recordStep^[rs.length] (rs.flatMap encodeRecord,acc)=([],acc++rs.map recordRepr) := by
  induction rs generalizing acc with
  | nil => simp
  | cons r rs ih =>
    rw [List.length_cons,Function.iterate_succ_apply,List.flatMap_cons,recordStep_encode,ih]
    simp [List.append_assoc]
lemma records_length_le_bits (rs : List Record) : rs.length≤(rs.flatMap encodeRecord).length := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hr := List.length_pos_iff.mpr (encodeRecord_ne_nil r)
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

def records (l : List Bool) : List RecordBits := (recordStep^[l.length] (l,[])).2
lemma records_encoded (rs : List Record) : records (rs.flatMap encodeRecord)=rs.map recordRepr := by
  unfold records
  have h := records_length_le_bits rs
  rw [show (rs.flatMap encodeRecord).length=((rs.flatMap encodeRecord).length-rs.length)+rs.length by omega,
    Function.iterate_add_apply,recordStep_records]
  simp only [List.nil_append,recordStep_nil]

lemma recordStep_size (z : List Bool×List RecordBits) : (recordStep z).1.length≤z.1.length ∧
    (encode (recordStep z).2).length≤(encode z.2).length+40*z.1.length+21 := by
  have hr := record_size z.1
  unfold recordStep
  split_ifs
  · simp; omega
  · simp only [code_append,List.length_append,code_cons,pairBits_length,List.length_nil,code_nil]
    omega
lemma recordStep_iterate_size (k : ℕ) (z : List Bool×List RecordBits) :
    (recordStep^[k] z).1.length≤z.1.length ∧
    (encode (recordStep^[k] z).2).length≤(encode z.2).length+k*(40*z.1.length+21) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := recordStep_size (recordStep^[k] z)
    constructor
    · exact h.1.trans ih.1
    · nlinarith
@[fun_prop] theorem records_poly : Poly records := by
  have hs : Poly recordStep := by unfold recordStep; fun_prop
  have hi := Poly.boundedIterate recordStep hs (100*(X+1)^2) (by
    intro z j hj
    obtain ⟨h₁,h₂⟩ := recordStep_iterate_size j z.2
    have he : (encode (recordStep^[j] z.2)).length ≤
        6*z.2.1.length+(encode z.2.2).length+j*(40*z.2.1.length+21)+1 := by
      simp only [code_pair_length,cut_code_length]
      omega
    have hl : z.2.1.length≤(encode z).length := by simp only [code_pair_length,code_nat_length,cut_code_length]; omega
    have hk : j≤(encode z).length := by simp only [code_pair_length,code_nat_length]; omega
    have ha : (encode z.2.2).length≤(encode z).length := by simp only [code_pair_length]; omega
    have hm := Nat.mul_le_mul hk hl
    simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
    nlinarith)
  exact Poly.second _ (Poly.comp _ (fun l : List Bool => (l.length,(l,([]:List RecordBits)))) hi (by fun_prop))

def input (l : List Bool) : List Bool×List RecordBits :=
  let a := numeral l
  (a.1,records (numeral a.2).2)
lemma input_encoded (G : Input) : input (encodeInput G)=(G.n.bits,G.records.map recordRepr) := by
  unfold input encodeInput
  simp only [List.append_assoc,numeral_encode,records_encoded]
@[fun_prop] theorem input_poly : Poly input := by unfold input; fun_prop
end BinaryMatching.Parse
end

end OAI
