import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplerContext

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInverseCDF
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Dyadic.Canonical

noncomputable def prefixCounts (x : List Bool) : List Bool :=
  Take.run (pairBits (UnaryResources.inc (discardPrefix x),extractPrefix (extractPrefix x)))
attribute [local irreducible] Take.run UnaryResources.inc
noncomputable def prefix_computes : PolyComputes prefixCounts :=
  ((discardPrefix_computes.comp UnaryResources.inc_computes).pair
    (extractPrefix_computes.comp extractPrefix_computes)).comp Take.run_computes
noncomputable def total (x : List Bool) : List Bool := NaturalArray.sumWords (prefixCounts x)
attribute [local irreducible] prefixCounts NaturalArray.sumWords
noncomputable def total_computes : PolyComputes total := prefix_computes.comp NaturalArray.sumWords_computes
noncomputable def predicate (x : List Bool) : Bool :=
  decide (value (discardPrefix (extractPrefix x))<value (total x))
attribute [local irreducible] total
noncomputable def predicate_computes : PolyComputes (fun x=>[predicate x]) :=
  NatOps.lt (extractPrefix_computes.comp discardPrefix_computes) total_computes
lemma predicate_pack (ws : List ℕ) (v j : ℕ) :
    predicate (pairBits (pairBits (NaturalArray.encode ws,v.bits),j.bits))=
      decide (v<(ws.take (j+1)).sum) := by
  simp only [predicate,total,prefixCounts,extractPrefix_pairBits,discardPrefix_pairBits,
    UnaryResources.inc,value_bits,NaturalArray.encode,Take.run_encode,←List.map_take]
  change decide (v<value (NaturalArray.sumWords (NaturalArray.encode (ws.take (j+1)))))=_
  rw [NaturalArray.sumWords_encode,value_bits]
noncomputable def find (x : List Bool) : List Bool :=
  Find.run predicate (pairBits (x,Indices.run (extractPrefix x)))
noncomputable def find_computes : PolyComputes find :=
  (id_computes.pair (extractPrefix_computes.comp Indices.run_computes)).comp (Find.run_computes predicate_computes)
def encodeOption : Option ℕ→List Bool
  | none=>[]
  | some j=>true::j.bits
lemma find_pack (ws : List ℕ) (v : ℕ) :
    find (pairBits (NaturalArray.encode ws,v.bits))=encodeOption (rank ws v) := by
  simp only [find,extractPrefix_pairBits,NaturalArray.encode,Indices.run_encode,List.length_map,Find.run_encode,
    List.find?_map,Function.comp_def]
  have he : (fun j=>predicate (pairBits (pairBits (NaturalArray.encode ws,v.bits),j.bits)))=
      (fun j=>decide (v<(ws.take (j+1)).sum)) := funext (predicate_pack ws v)
  change Find.optionEncode (((List.range ws.length).find? (fun j=>predicate
    (pairBits (pairBits (NaturalArray.encode ws,v.bits),j.bits)))).map Nat.bits)=_
  rw [he]
  change Find.optionEncode ((findRank ws v).map Nat.bits)=_
  rw [findRank_eq]
  cases rank ws v <;> rfl

def pack (d : ℕ) (ws : List ℕ) (tape : List Bool) : List Bool := encode [d.bits,NaturalArray.encode ws,tape]
noncomputable def searched (x : List Bool) : List Bool := find (pairBits (field 1 x,BinarySeed.normalizeBig (field 2 x)))
noncomputable def searched_computes : PolyComputes searched :=
  ((field_computes 1).pair ((field_computes 2).comp BinarySeed.normalizeBig_computes)).comp find_computes
attribute [local irreducible] searched
noncomputable def run (x : List Bool) : List Bool := if searched x=[] then field 0 x else (searched x).tail
noncomputable def run_computes : PolyComputes run := by
  have hh := (searched_computes.comp isEmpty_computes).cond (field_computes 0) (searched_computes.comp WordOperations.tail_computes)
  unfold run
  simpa only [decide_eq_true_eq,Function.comp_def] using hh
lemma run_pack (d : ℕ) (ws : List ℕ) (b : ℕ) (s : Fin b→Bool) :
    run (pack d ws (List.ofFn s))=((rank ws (Categorical.uniformBits b s).val).getD d).bits := by
  simp only [run,searched,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinarySeed.normalizeBig_ofFn,find_pack]
  cases rank ws (Categorical.uniformBits b s).val <;> simp [encodeOption]
end MetricKMedianRecovery.BitMachine.BinaryInverseCDF
namespace MetricKMedianRecovery.BitMachine.RatOps
noncomputable def natFloor {f : List Bool→ℚ} (hf : PolyComputes (fun x=>BinaryRational.encode (f x))) :
    PolyComputes (fun x=>(⌊f x⌋₊).bits) := by
  have hh := (hf.comp BinaryRational.floorWords_computes).comp Signed.natWords_computes
  simpa only [Function.comp_def,BinaryRational.floorWords_encode,Signed.natWords_encode,Int.floor_toNat] using hh
end MetricKMedianRecovery.BitMachine.RatOps

namespace MetricKMedianRecovery.BitMachine.BinaryDyadic
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
lemma bits_two_pow (b : ℕ) : (2^b).bits=List.replicate b false++[true] := by
  induction b with
  | zero=>rfl
  | succ b ih=>rw [pow_succ,Nat.mul_comm,Nat.bit0_bits _ (by positivity),ih,List.replicate_succ,List.cons_append]
noncomputable def power (x : List Bool) : List Bool := List.replicate x.length false++[true]
noncomputable def power_computes : PolyComputes power := by
  have hh:=UnaryResources.copy_computes id_computes (const_computes [false])
  have he : PolyComputes (fun x : List Bool=>List.replicate x.length false) := by
    simpa only [id_eq,RawUnary.copies_singleton] using hh
  exact he.append (const_computes [true])
lemma power_replicate (b : ℕ) : power (List.replicate b true)=(2^b).bits := by
  rw [power,List.length_replicate,bits_two_pow]
noncomputable def scale (x : List Bool) : ℚ := (value (power x):ℚ)
noncomputable def scale_computes : PolyComputes (fun x=>BinaryRational.encode (scale x)) := RatOps.nat power_computes
lemma scale_replicate (b : ℕ) : scale (List.replicate b true)=(2:ℚ)^b := by
  rw [scale,power_replicate,value_bits,Nat.cast_pow,Nat.cast_ofNat]
noncomputable def count (x : List Bool) : List Bool :=
  (⌊BinaryRational.decode (discardPrefix x)*BinaryRational.decode (extractPrefix x)⌋₊).bits
noncomputable def count_computes : PolyComputes count :=
  RatOps.natFloor (RatOps.mul (RatOps.ofWords discardPrefix_computes) (RatOps.ofWords extractPrefix_computes))
lemma count_pack (p : ℚ) (b : ℕ) :
    count (pairBits (BinaryRational.encode ((2:ℚ)^b),BinaryRational.encode p))=(⌊p*(2:ℚ)^b⌋₊).bits := by
  simp only [count,extractPrefix_pairBits,discardPrefix_pairBits,BinaryRational.decode_encode]

def pack (b d : ℕ) (ps : List ℚ) (raw : List Bool) : List Bool :=
  encode [List.replicate b true,RationalArray.encode ps,d.bits,raw]
noncomputable def counts (x : List Bool) : List Bool :=
  mapWith count (pairBits (BinaryRational.encode (scale (field 0 x)),field 1 x))
noncomputable def counts_computes : PolyComputes counts := by
  have computation := (((field_computes 0).comp scale_computes).pair (field_computes 1)).comp (mapWith_computes count_computes)
  unfold counts
  simpa only [Function.comp_def] using computation
lemma counts_pack (b d : ℕ) (ps : List ℚ) (raw : List Bool) :
    counts (pack b d ps raw)=NaturalArray.encode (ps.map (fun p=>⌊p*(2:ℚ)^b⌋₊)) := by
  simp only [counts,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    scale_replicate,RationalArray.encode,mapWith_encode,List.map_map,Function.comp_def,count_pack,NaturalArray.encode]
noncomputable def prepared (x : List Bool) : List Bool := encode [field 2 x,counts x,field 3 x]
noncomputable def prepared_computes : PolyComputes prepared :=
  cons_computes (field_computes 2) (cons_computes counts_computes (cons_computes (field_computes 3) (const_computes [])))
noncomputable def run (x : List Bool) : List Bool := BinaryInverseCDF.run (prepared x)
noncomputable def run_computes : PolyComputes run := prepared_computes.comp BinaryInverseCDF.run_computes
lemma run_pack (b d : ℕ) (ps : List ℚ) (s : Fin b→Bool) :
    run (pack b d ps (List.ofFn s))=
      ((Dyadic.Canonical.rank (ps.map (fun p=>⌊p*(2:ℚ)^b⌋₊)) (Categorical.uniformBits b s).val).getD d).bits := by
  rw [run,prepared,counts_pack]
  simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  exact BinaryInverseCDF.run_pack d _ b s
lemma floor_cast (p : ℚ) : ⌊(p:ℝ)⌋₊=⌊p⌋₊ := by
  rw [←Int.floor_toNat,←Int.floor_toNat,Rat.floor_cast]
lemma rawCount_cast {A : Type*} (p : A→ℚ) (b : ℕ) (a : A) :
    Dyadic.rawCount (fun a=>(p a:ℝ)) b a=⌊p a*(2:ℚ)^b⌋₊ := by
  unfold Dyadic.rawCount
  have he : (2:ℝ)^b*(p a:ℝ)=((p a*(2:ℚ)^b:ℚ):ℝ) := by
    simp only [Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,mul_comm]
  rw [he,floor_cast]
end MetricKMedianRecovery.BitMachine.BinaryDyadic

end OAI
