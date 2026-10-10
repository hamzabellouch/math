import OAI.Computability.LoopMatching.Model
import OAI.Computability.MatchingCount.BinaryParser

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.InputMachine
open BinaryMatching BinaryMatching.StackCode Polynomial

def countedRecords (k : ℕ) (l : List Bool) : List Bool × List Parse.RecordBits :=
  Parse.recordStep^[k] (l,[])

lemma recordStep_records_suffix (rs : List BinaryMatching.Record)
    (suffix : List Bool) (acc : List Parse.RecordBits) :
    Parse.recordStep^[rs.length] (rs.flatMap encodeRecord ++ suffix,acc) =
      (suffix,acc ++ rs.map Parse.recordRepr) := by
  induction rs generalizing acc with
  | nil => simp
  | cons r rs ih =>
    rw [List.length_cons,Function.iterate_succ_apply,List.flatMap_cons,
      List.append_assoc,Parse.recordStep_encode,ih]
    simp [List.append_assoc]

lemma countedRecords_encoded (rs : List BinaryMatching.Record) (suffix : List Bool) :
    countedRecords rs.length (rs.flatMap encodeRecord ++ suffix) =
      (suffix,rs.map Parse.recordRepr) := by
  simpa only [countedRecords,List.nil_append] using
    recordStep_records_suffix rs suffix []

@[fun_prop] theorem countedRecords_poly :
    Poly (fun z : ℕ × List Bool => countedRecords z.1 z.2) := by
  have hs : Poly Parse.recordStep := by unfold Parse.recordStep; fun_prop
  have hi := Poly.boundedIterate Parse.recordStep hs (100*(X+1)^2) (by
    intro z j hj
    obtain ⟨h₁,h₂⟩ := Parse.recordStep_iterate_size j z.2
    have he : (encode (Parse.recordStep^[j] z.2)).length ≤
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
  exact Poly.comp _ (fun z : ℕ × List Bool => (z.1,(z.2,([]:List Parse.RecordBits))))
    hi (by fun_prop)

def ordinaryPrefix (l : List Bool) : List Bool × (List Bool × List Parse.RecordBits) :=
  let n := Parse.numeral l
  let r := Parse.numeral n.2
  (n.1,countedRecords (Parse.boundedValue l.length r.1) r.2)

@[fun_prop] theorem ordinaryPrefix_poly : Poly ordinaryPrefix := by
  unfold ordinaryPrefix
  fun_prop

lemma ordinaryPrefix_encoded (G : LoopMatching.Input) :
    ordinaryPrefix (LoopMatching.encodeInput G) =
      (G.n.bits,(encodeNat G.loops.length ++ G.loops.flatMap encodeLoopRecord,
        G.ordinary.records.map Parse.recordRepr)) := by
  have hr := Parse.records_length_le_bits G.ordinary.records
  have hbound : G.ordinary.records.length ≤ (LoopMatching.encodeInput G).length := by
    simp only [LoopMatching.encodeInput,BinaryMatching.encodeInput,List.length_append]
    omega
  unfold ordinaryPrefix LoopMatching.encodeInput BinaryMatching.encodeInput
  simp only [List.append_assoc,Parse.numeral_encode,Parse.boundedValue_bits]
  simp only [LoopMatching.encodeInput,BinaryMatching.encodeInput,List.append_assoc] at hbound
  rw [min_eq_right hbound,countedRecords_encoded]

end LoopMatching.InputMachine

end OAI
