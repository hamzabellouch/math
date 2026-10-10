import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.Encode2
import OAI.Combinatorics.KMedianRecovery.Encoding.UnaryParser

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream
open WordOperations
abbrev raw (rs : List ℚ) : List Bool := (rs.map RationalMetricInput.rationalBits).flatten
abbrev codes (rs : List ℚ) : List Bool := WordList.encode (rs.map BinaryRational.encode)
def pack (rs acc : List ℚ) : List Bool := pairBits (raw rs,codes acc)
noncomputable def step (x : List Bool) : List Bool :=
  if extractPrefix x=[] then x else
    pairBits (discardPrefix (rational (extractPrefix x)),
      WordList.cons (extractPrefix (rational (extractPrefix x))) (discardPrefix x))
attribute [local irreducible] rational
noncomputable def step_computes : PolyComputes step := by
  have hp:=extractPrefix_computes.comp rational_computes
  have hc:=WordList.cons_computes (hp.comp extractPrefix_computes) discardPrefix_computes
  have hh:=(extractPrefix_computes.comp isEmpty_computes).cond id_computes ((hp.comp discardPrefix_computes).pair hc)
  unfold step
  simpa only [Function.comp_def,decide_eq_true_eq,id_eq] using hh
lemma raw_cons (r : ℚ) (rs : List ℚ) : raw (r::rs)=RationalMetricInput.rationalBits r++raw rs := rfl
lemma raw_length_pos (r : ℚ) : 0<(RationalMetricInput.rationalBits r).length := by
  simp only [RationalMetricInput.rationalBits,List.length_append,List.length_singleton]
  omega
lemma step_nil (acc : List ℚ) : step (pack [] acc)=pack [] acc := by
  unfold step pack
  rw [extractPrefix_pairBits,ite_eq_left (show raw []=[] from rfl)]
lemma step_cons (r : ℚ) (rs acc : List ℚ) : step (pack (r::rs) acc)=pack rs (r::acc) := by
  have hn : raw (r::rs)≠[] := by
    intro he
    have hh:=congrArg List.length he
    have hp:=raw_length_pos r
    simp only [raw_cons,List.length_append,List.length_nil] at hh
    omega
  rw [step,pack,extractPrefix_pairBits,ite_eq_right hn,raw_cons,rational_code,extractPrefix_pairBits,discardPrefix_pairBits,discardPrefix_pairBits]
  rfl
lemma code_length (r : ℚ) : (BinaryRational.encode r).length≤(RationalMetricInput.rationalBits r).length := by
  simp only [BinaryRational.encode_length,RationalMetricInput.rationalBits,RationalMetricInput.natBits,
    List.length_append,List.length_singleton,List.length_replicate,←Nat.size_eq_bits_len]
  omega
lemma codes_length (rs : List ℚ) : (codes rs).length≤3*(raw rs).length := by
  induction rs with
  | nil=>simp only [codes,raw,List.map_nil,List.flatten_nil,WordList.encode,List.length_nil,Nat.mul_zero,Nat.le_refl]
  | cons r rs ih=>
    have hc:=code_length r
    have hp : 2≤(RationalMetricInput.rationalBits r).length := by
      simp only [RationalMetricInput.rationalBits,RationalMetricInput.natBits,List.length_append,List.length_singleton,List.length_replicate]
      omega
    simp only [codes,List.map_cons,WordList.encode,WordList.length_cons,raw_cons,List.length_append] at *
    omega
lemma raw_append (rs ss : List ℚ) : (raw (rs++ss)).length=(raw rs).length+(raw ss).length := by
  simp only [raw,List.map_append,List.flatten_append,List.length_append]
lemma raw_reverse (rs : List ℚ) : (raw rs.reverse).length=(raw rs).length := by
  simp only [raw,List.length_flatten,List.map_reverse,List.map_map,List.sum_reverse]
lemma pack_length (rs acc : List ℚ) : (pack rs acc).length≤3*((raw rs).length+(raw acc).length)+1 := by
  have hc:=codes_length acc
  simp only [pack,pairBits_length]
  omega
lemma iterate_shape (rs acc : List ℚ) (n : ℕ) :
    ∃ rs' acc',step^[n] (pack rs acc)=pack rs' acc' ∧
      (raw rs').length+(raw acc').length=(raw rs).length+(raw acc).length := by
  induction n generalizing rs acc with
  | zero=>exact ⟨rs,acc,rfl,rfl⟩
  | succ n ih=>
    cases rs with
    | nil=>rw [Function.iterate_fixed (step_nil acc)]; exact ⟨[],acc,rfl,rfl⟩
    | cons r rs=>
      rw [Function.iterate_succ_apply,step_cons]
      obtain ⟨rs',acc',he,hl⟩:=ih rs (r::acc)
      refine ⟨rs',acc',he,?_⟩
      simp only [raw_cons,List.length_append] at hl ⊢
      omega
lemma iterate_done (rs acc : List ℚ) (n : ℕ) (hn : rs.length≤n) :
    step^[n] (pack rs acc)=pack [] (rs.reverse++acc) := by
  induction rs generalizing acc n with
  | nil=>rw [Function.iterate_fixed (step_nil acc)]; rfl
  | cons r rs ih=>
    cases n with
    | zero=>simp only [List.length_cons] at hn; omega
    | succ n=>
      rw [Function.iterate_succ_apply,step_cons,ih (r::acc) n (by simp only [List.length_cons] at hn; omega)]
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
lemma count_le_raw (rs : List ℚ) : rs.length≤(raw rs).length := by
  induction rs with
  | nil=>rfl
  | cons r rs ih=>have hh:=raw_length_pos r; simp only [List.length_cons,raw_cons,List.length_append]; omega
noncomputable def run (x : List Bool) : List Bool :=
  WordList.reverse (discardPrefix (BoundedIteration.polynomialRun step Polynomial.X (3*Polynomial.X+1) (pairBits (x,[]))))
noncomputable def run_computes : PolyComputes run :=
  ((id_computes.pair (const_computes [])).comp
    (BoundedIteration.polynomialRun_computes step_computes Polynomial.X (3*Polynomial.X+1))).comp
    (discardPrefix_computes.comp WordList.reverse_computes)
lemma run_code (rs : List ℚ) : run (raw rs)=codes rs := by
  unfold run
  change WordList.reverse (discardPrefix (BoundedIteration.polynomialRun step Polynomial.X (3*Polynomial.X+1) (pack rs [])))=_
  rw [BoundedIteration.polynomialRun_eq step Polynomial.X (3*Polynomial.X+1) (pack rs []) ?_]
  · simp only [Polynomial.eval_X]
    rw [iterate_done rs [] (pack rs []).length (by
      have hh:=count_le_raw rs
      simp only [pack,pairBits_length]
      omega),pack,discardPrefix_pairBits,List.append_nil]
    change WordList.reverse (WordList.encode ((rs.reverse).map BinaryRational.encode))=_
    rw [WordList.reverse_encode,List.map_reverse,List.reverse_reverse]
  · intro j _
    obtain ⟨rs',acc',he,hl⟩:=iterate_shape rs [] j
    rw [he]
    have hb:=pack_length rs' acc'
    change (raw rs').length+(raw acc').length=(raw rs).length+0 at hl
    simp only [Nat.add_zero] at hl
    rw [hl] at hb
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    have hh : (raw rs).length≤(pack rs []).length := by simp only [pack,pairBits_length]; omega
    omega
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream

end OAI
