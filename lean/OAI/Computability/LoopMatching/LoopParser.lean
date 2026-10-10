import OAI.Computability.LoopMatching.CountedParser
import OAI.Computability.LoopMatching.InputDecode

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.InputMachine
open BinaryMatching BinaryMatching.StackCode Polynomial

def loopRecord (l : List Bool) : LoopBits × List Bool :=
  let a := Parse.numeral l
  let b := Parse.numeral a.2
  ((a.1,b.1),b.2)

lemma loopRecord_encode (r : LoopRecord) (l : List Bool) :
    loopRecord (encodeLoopRecord r ++ l)=(loopBitsRepr r,l) := by
  unfold loopRecord encodeLoopRecord
  simp only [List.append_assoc,Parse.numeral_encode]
  rfl

@[fun_prop] theorem loopRecord_poly : Poly loopRecord := by unfold loopRecord; fun_prop

lemma loopRecord_size (l : List Bool) : (loopRecord l).2.length≤l.length ∧
    (encode (loopRecord l).1).length≤20*l.length+10 := by
  have h₁ := Parse.numeral_lengths l
  have h₂ := Parse.numeral_lengths (Parse.numeral l).2
  simp only [loopRecord,code_pair_length,cut_code_length]
  omega

def loopStep (z : List Bool × List LoopBits) : List Bool × List LoopBits :=
  if z.1.isEmpty then z else ((loopRecord z.1).2,z.2++[(loopRecord z.1).1])

lemma encodeLoopRecord_ne_nil (r : LoopRecord) : encodeLoopRecord r≠[] := by
  simp [encodeLoopRecord,encodeNat]

lemma loopStep_encode (r : LoopRecord) (l : List Bool) (acc : List LoopBits) :
    loopStep (encodeLoopRecord r ++ l,acc)=(l,acc++[loopBitsRepr r]) := by
  simp [loopStep,List.isEmpty_iff,List.append_eq_nil_iff,
    encodeLoopRecord_ne_nil,loopRecord_encode]

lemma loopStep_records_suffix (rs : List LoopRecord) (suffix : List Bool)
    (acc : List LoopBits) :
    loopStep^[rs.length] (rs.flatMap encodeLoopRecord ++ suffix,acc)=
      (suffix,acc++rs.map loopBitsRepr) := by
  induction rs generalizing acc with
  | nil => simp
  | cons r rs ih =>
    rw [List.length_cons,Function.iterate_succ_apply,List.flatMap_cons,
      List.append_assoc,loopStep_encode,ih]
    simp [List.append_assoc]

lemma loopRecords_length_le_bits (rs : List LoopRecord) :
    rs.length ≤ (rs.flatMap encodeLoopRecord).length := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hr := List.length_pos_iff.mpr (encodeLoopRecord_ne_nil r)
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

lemma loopStep_size (z : List Bool × List LoopBits) :
    (loopStep z).1.length≤z.1.length ∧
    (encode (loopStep z).2).length≤(encode z.2).length+40*z.1.length+21 := by
  have hr := loopRecord_size z.1
  unfold loopStep
  split_ifs
  · simp; omega
  · simp only [code_append,List.length_append,code_cons,pairBits_length,List.length_nil,code_nil]
    omega

lemma loopStep_iterate_size (k : ℕ) (z : List Bool × List LoopBits) :
    (loopStep^[k] z).1.length≤z.1.length ∧
    (encode (loopStep^[k] z).2).length≤(encode z.2).length+k*(40*z.1.length+21) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := loopStep_size (loopStep^[k] z)
    constructor
    · exact h.1.trans ih.1
    · nlinarith

def countedLoops (k : ℕ) (l : List Bool) : List LoopBits := (loopStep^[k] (l,[])).2

@[fun_prop] theorem countedLoops_poly : Poly (fun z : ℕ × List Bool => countedLoops z.1 z.2) := by
  have hs : Poly loopStep := by unfold loopStep; fun_prop
  have hi := Poly.boundedIterate loopStep hs (100*(X+1)^2) (by
    intro z j hj
    obtain ⟨h₁,h₂⟩ := loopStep_iterate_size j z.2
    have he : (encode (loopStep^[j] z.2)).length ≤
        6*z.2.1.length+(encode z.2.2).length+j*(40*z.2.1.length+21)+1 := by
      simp only [code_pair_length,cut_code_length]
      omega
    have hl : z.2.1.length≤(encode z).length := by
      simp only [code_pair_length,code_nat_length,cut_code_length]; omega
    have hk : j≤(encode z).length := by
      simp only [code_pair_length,code_nat_length]; omega
    have ha : (encode z.2.2).length≤(encode z).length := by
      simp only [code_pair_length]; omega
    have hm := Nat.mul_le_mul hk hl
    simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
    nlinarith)
  exact Poly.second _ (Poly.comp _
    (fun z : ℕ × List Bool => (z.1,(z.2,([]:List LoopBits)))) hi (by fun_prop))

lemma countedLoops_encoded (rs : List LoopRecord) :
    countedLoops rs.length (rs.flatMap encodeLoopRecord)=rs.map loopBitsRepr := by
  have h := loopStep_records_suffix rs [] []
  simpa only [countedLoops,List.append_nil,List.nil_append] using congrArg Prod.snd h

def loops (l : List Bool) : List LoopBits :=
  let a := Parse.numeral l
  countedLoops (Parse.boundedValue l.length a.1) a.2

@[fun_prop] theorem loops_poly : Poly loops := by unfold loops; fun_prop

lemma loops_encoded (rs : List LoopRecord) :
    loops (encodeNat rs.length ++ rs.flatMap encodeLoopRecord)=rs.map loopBitsRepr := by
  have h := loopRecords_length_le_bits rs
  have hb : rs.length ≤ (encodeNat rs.length ++ rs.flatMap encodeLoopRecord).length := by
    rw [List.length_append]
    omega
  unfold loops
  rw [Parse.numeral_encode]
  dsimp only
  rw [Parse.boundedValue_bits,min_eq_right hb,countedLoops_encoded]

def parse (l : List Bool) : BitsData :=
  let a := ordinaryPrefix l
  (a.1,(a.2.2,loops a.2.1))

@[fun_prop] theorem parse_poly : Poly parse := by unfold parse; fun_prop

lemma parse_encoded (G : LoopMatching.Input) : parse (LoopMatching.encodeInput G)=bitsRepr G := by
  unfold parse
  rw [ordinaryPrefix_encoded]
  dsimp only
  rw [loops_encoded]
  rfl

def prepare (l : List Bool) : Option Data :=
  let z := decode (parse l)
  if 2*z.2.1.length+z.2.2.length<z.1 then none else some z

@[fun_prop] theorem prepare_poly : Poly prepare := by
  have h : Poly (fun l : List Bool =>
      if decide (2*(decode (parse l)).2.1.length+(decode (parse l)).2.2.length <
        (decode (parse l)).1) then (none : Option Data) else some (decode (parse l))) := by
    fun_prop
  exact h.congr (fun l => by simp only [prepare,decide_eq_true_eq])

lemma prepare_encoded (G : LoopMatching.Input) :
    prepare (LoopMatching.encodeInput G)=
      if 2*G.ordinary.records.length+G.loops.length<G.n then none else some (repr G) := by
  unfold prepare
  rw [parse_encoded]
  by_cases h : 2*G.ordinary.records.length+G.loops.length<G.n
  · rw [ite_eq_left h,ite_eq_left ((sparse_guard_repr G).mpr h)]
  · rw [ite_eq_right h,ite_eq_right (by simpa only [sparse_guard_repr] using h),decode_repr G (by omega)]

lemma prepare_encoded_pass (G : LoopMatching.Input)
    (h : G.n ≤ 2*G.ordinary.records.length+G.loops.length) :
    prepare (LoopMatching.encodeInput G)=some (repr G) := by
  rw [prepare_encoded,ite_eq_right (by omega)]

lemma prepare_encoded_reject (G : LoopMatching.Input)
    (h : 2*G.ordinary.records.length+G.loops.length<G.n) :
    prepare (LoopMatching.encodeInput G)=none := by rw [prepare_encoded,ite_eq_left h]

end LoopMatching.InputMachine

end OAI
