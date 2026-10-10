import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.CopyComputes

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RawDrop
open WordOperations BinaryArithmetic
def step (x : List Bool) : List Bool :=
  if value (extractPrefix x)=0 then x
  else pairBits ((value (extractPrefix x)-1).bits,List.tail (discardPrefix x))
noncomputable def step_computes : PolyComputes step := by
  have hd := NatOps.sub extractPrefix_computes (const_computes [true])
  have hp := hd.pair (discardPrefix_computes.comp WordOperations.tail_computes)
  have hh := (NatOps.zero extractPrefix_computes).cond id_computes hp
  unfold step
  simpa [value,Function.comp_def] using hh
lemma decrement_length (x : List Bool) : (value x-1).bits.length ≤ x.length := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le_size (Nat.sub_le _ _) |>.trans
  simpa only [normalize_eq_bits,Nat.size_eq_bits_len] using BinaryDivision.normalize_length x
lemma first_step (x : List Bool) : (extractPrefix (step x)).length ≤ (extractPrefix x).length := by
  unfold step; split_ifs
  · exact le_rfl
  · rw [extractPrefix_pairBits]; exact decrement_length _
lemma rest_step (x : List Bool) : (discardPrefix (step x)).length ≤ (discardPrefix x).length := by
  unfold step; split_ifs
  · exact le_rfl
  · rw [discardPrefix_pairBits]; exact by simp only [List.length_tail]; omega
lemma length_step (x : List Bool) : (step x).length ≤ max x.length
    (2*(extractPrefix x).length+1+(discardPrefix x).length) := by
  unfold step; split_ifs
  · exact Nat.le_max_left _ _
  · rw [pairBits_length]
    dsimp only
    have hi := decrement_length (extractPrefix x)
    have hl : (discardPrefix x).tail.length ≤ (discardPrefix x).length := by simp only [List.length_tail]; omega
    omega
lemma iterate_bounds (x : List Bool) (n : ℕ) :
    (extractPrefix (step^[n] x)).length ≤ (extractPrefix x).length ∧
    (discardPrefix (step^[n] x)).length ≤ (discardPrefix x).length ∧
    (step^[n] x).length ≤ max x.length (2*(extractPrefix x).length+1+(discardPrefix x).length) := by
  induction n with
  | zero => exact ⟨le_rfl,le_rfl,Nat.le_max_left _ _⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hf := first_step (step^[n] x)
    have hr := rest_step (step^[n] x)
    have hl := length_step (step^[n] x)
    exact ⟨hf.trans ih.1,hr.trans ih.2.1,by omega⟩

lemma step_zero (ws : List Bool) : step (pairBits (Nat.bits 0,ws))=pairBits (Nat.bits 0,ws) := by
  simp only [step,extractPrefix_pairBits,value_bits,ite_true]
lemma step_succ (i : ℕ) (ws : List Bool) :
    step (pairBits ((i+1).bits,ws))=pairBits (i.bits,ws.tail) := by
  simp only [step,extractPrefix_pairBits,discardPrefix_pairBits,value_bits,Nat.add_sub_cancel,
    Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false]
def run (x : List Bool) : List Bool := discardPrefix (step^[x.length] x)
noncomputable def run_computes : PolyComputes run := by
  have hi := BoundedIteration.polynomialRun_computes step_computes Polynomial.X (4*Polynomial.X+1)
  have hh := hi.comp discardPrefix_computes
  have he (x : List Bool) : BoundedIteration.polynomialRun step Polynomial.X (4*Polynomial.X+1) x=
      step^[x.length] x := by
    have ht := BoundedIteration.polynomialRun_eq step Polynomial.X (4*Polynomial.X+1) x (by
      intro j _
      have hb := (iterate_bounds x j).2.2
      obtain ⟨hf,hr⟩ := ProductBits.projections_length x
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
        Polynomial.eval_one]
      omega)
    simpa only [Polynomial.eval_X] using ht
  change PolyComputes (fun x=>discardPrefix (step^[x.length] x))
  simpa only [Function.comp_def,he] using hh
lemma drop_iterate (n i : ℕ) (ws : List Bool) (hn : ws.length≤n) :
    discardPrefix (step^[n] (pairBits (i.bits,ws)))=ws.drop i := by
  induction n generalizing i ws with
  | zero=>
    have hw : ws=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst ws
    simp only [Function.iterate_zero_apply,discardPrefix_pairBits,List.drop_nil]
  | succ n ih=>
    cases i with
    | zero=>rw [Function.iterate_fixed (step_zero ws),discardPrefix_pairBits,List.drop_zero]
    | succ i=>
      rw [Function.iterate_succ_apply,step_succ]
      have hl : ws.tail.length≤n := by simp only [List.length_tail]; omega
      rw [ih i ws.tail hl]
      cases ws with
      | nil=>simp only [List.tail_nil,List.drop_nil]
      | cons w ws=>rfl
lemma run_encode (i : ℕ) (ws : List Bool) :
    run (pairBits (i.bits,ws))=ws.drop i := by
  apply drop_iterate
  rw [pairBits_length]
  dsimp only
  omega
end MetricKMedianRecovery.BitMachine.RawDrop
namespace MetricKMedianRecovery.BitMachine.RawTake
open WordOperations BinaryArithmetic
noncomputable def number (x : List Bool) : List Bool :=
  (value (UnaryResources.lengthBits (discardPrefix x))-value (extractPrefix x)).bits
noncomputable def number_computes : PolyComputes number :=
  NatOps.sub (discardPrefix_computes.comp UnaryResources.lengthBits_computes) extractPrefix_computes
noncomputable def run (x : List Bool) : List Bool :=
  (RawDrop.run (pairBits (number x,(discardPrefix x).reverse))).reverse
attribute [local irreducible] number RawDrop.run
noncomputable def run_computes : PolyComputes run :=
  ((number_computes.pair (discardPrefix_computes.comp reverse_computes)).comp RawDrop.run_computes).comp reverse_computes
lemma run_pack (n : ℕ) (ws : List Bool) : run (pairBits (n.bits,ws))=ws.take n := by
  simp only [run,number,extractPrefix_pairBits,discardPrefix_pairBits,UnaryResources.lengthBits_eq,value_bits,
    RawDrop.run_encode,List.reverse_drop,List.reverse_reverse,List.length_reverse]
  rw [show ws.length-(ws.length-n)=min n ws.length by omega]
  exact List.take_eq_take_min.symm
end MetricKMedianRecovery.BitMachine.RawTake
namespace MetricKMedianRecovery.BitMachine.UnaryTake
open WordOperations
def dropWords (x : List Bool) : List Bool := (discardPrefix x).drop (extractPrefix x).length
noncomputable def dropWords_computes : PolyComputes dropWords := by
  have hi := pack_computes true extractPrefix_computes discardPrefix_computes (const_computes [])
  have hh := (hi.comp loop_computes).comp data_computes
  convert hh using 1
  funext x
  simp only [Function.comp_apply,rank,pack,List.head?_cons,ite_true,counter,List.tail_cons,
    extractPrefix_pairBits]
  change dropWords x=data (next^[(extractPrefix x).length+1]
    (pack true (extractPrefix x) (discardPrefix x) []))
  rw [loop_spec,data_pack]
  rfl
end MetricKMedianRecovery.BitMachine.UnaryTake

end OAI
