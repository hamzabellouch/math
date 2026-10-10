import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.BidPoly

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseTrace
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
open BinaryPhaseFinish
lemma event_length {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (e : Event m d)
    (he : first distance F W v s.phase lam (List.ofFn (fun i : Fin m=>i))=some e) :
    (BinaryPhaseFirst.eventBits e).length ≤ capPoly.eval (stateBits distance F v lam s).length := by
  let L := (stateBits distance F v lam s).length
  let B := bidPoly.eval L
  have hbid := encode_le_bound (List.ofFn (fun j : Fin d=>BinaryRational.encode e.bid[j])) B (by
    intro w hw
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hw
    exact first_bid_bound distance F W v lam s e he j)
  simp only [List.length_ofFn] at hbid
  obtain ⟨hm,hd⟩:=dimensions distance F v lam s
  have hi := (Indices.bits_length_le e.facility.val).trans (Nat.le_of_lt e.facility.isLt)
  have hmul := Nat.mul_le_mul_right (2*B+2) hd
  change _ ≤ L*(2*B+2) at hmul
  simp only [capPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_one]
  change _ ≤ 40*(L+1)^2+4*(L+1)*B
  simp only [BinaryPhaseFirst.eventBits,pairBits_length,RationalMatrix.rowEncode_eq]
  change m ≤ L at hm
  nlinarith
lemma finish_event_length {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (fuel : ℕ) (t : State m d) (ht : t.phase=s.phase) :
    ∀ e∈(finish distance F v lam fuel t).2,
      (BinaryPhaseFirst.eventBits e).length ≤ capPoly.eval (stateBits distance F v lam s).length := by
  induction fuel generalizing t with
  | zero=>simp only [finish,List.not_mem_nil,false_implies,implies_true]
  | succ fuel ih=>
    cases he : first distance F t.opened v t.phase lam (List.ofFn (fun i : Fin m=>i)) with
    | none=>simp only [finish,he,List.not_mem_nil,false_implies,implies_true]
    | some e=>
      simp only [finish,he,List.mem_cons]
      intro e' he'
      rcases he' with rfl|hh
      · apply event_length distance F t.opened v lam s e'
        simpa only [ht] using he
      · exact ih (update distance v t e) ht e' hh
lemma finish_count {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (fuel : ℕ) (s : State m d) : (finish distance F v lam fuel s).2.length ≤ fuel := by
  induction fuel generalizing s with
  | zero=>rfl
  | succ fuel ih=>
    cases he : first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m=>i)) with
    | none=>simp only [finish,he,List.length_nil,Nat.zero_le]
    | some e=>simpa only [finish,he,List.length_cons] using Nat.succ_le_succ (ih (update distance v s e))
def pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (es : List (Event m d)) : List Bool :=
  pairBits (stateBits distance F v lam s,encode (es.map BinaryPhaseFirst.eventBits))
noncomputable def answer : List Bool → List Bool := BinaryPhaseFinish.answer ∘ extractPrefix
noncomputable def answer_computes : PolyComputes answer := extractPrefix_computes.comp BinaryPhaseFinish.answer_computes
noncomputable def step (x : List Bool) : List Bool :=
  if answer x=[] then x else pairBits
    (BinaryPhaseUpdate.run (pairBits (extractPrefix x,(answer x).tail)),cons (answer x).tail (discardPrefix x))
noncomputable def step_computes : PolyComputes step := by
  have ha := answer_computes.comp WordOperations.tail_computes
  have h := (answer_computes.comp isEmpty_computes).cond id_computes
    (((extractPrefix_computes.pair ha).comp BinaryPhaseUpdate.run_computes).pair (cons_computes ha discardPrefix_computes))
  change PolyComputes (fun x=>if answer x=[] then x else pairBits
    (BinaryPhaseUpdate.run (pairBits (extractPrefix x,(answer x).tail)),cons (answer x).tail (discardPrefix x)))
  simpa only [Function.comp_def,decide_eq_true_eq,id_eq] using h
lemma step_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (es : List (Event m d)) :
    step (pack distance F v lam s es)=
      match first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m=>i)) with
      | none=>pack distance F v lam s es
      | some e=>pack distance F v lam (update distance v s e) (e::es) := by
  have ha : answer (pack distance F v lam s es)=BinaryPhaseFirst.resultBits
      (first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m=>i))) := by
    simp only [answer,Function.comp_apply,pack,extractPrefix_pairBits,BinaryPhaseFinish.answer_pack]
  rw [step,ha]
  cases he : first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m=>i)) with
  | none=>rfl
  | some e=>simp only [BinaryPhaseFirst.resultBits,List.cons_ne_nil,ite_false,List.tail_cons,
      pack,extractPrefix_pairBits,discardPrefix_pairBits,BinaryPhaseUpdate.run_pack,List.map_cons,encode]
lemma iterate_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (fuel : ℕ) (s : State m d) (es : List (Event m d)) :
    step^[fuel] (pack distance F v lam s es)=
      pack distance F v lam (finish distance F v lam fuel s).1 ((finish distance F v lam fuel s).2.reverse++es) := by
  induction fuel generalizing s es with
  | zero=>rfl
  | succ fuel ih=>
    rw [Function.iterate_succ_apply,step_pack]
    cases he : first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m=>i)) with
    | none=>simp only [ih,finish_none distance F v lam s he,finish,he,List.reverse_nil,List.nil_append]
    | some e=>simp only [ih,finish,he,List.reverse_cons,List.append_assoc,List.singleton_append]
noncomputable def traceCapPoly : Polynomial ℕ := 2*capPoly+1+Polynomial.X*(2*capPoly+2)
lemma iterate_length {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (fuel j : ℕ) (hj : j ≤ fuel) :
    (step^[j] (pack distance F v lam s [])).length ≤
      traceCapPoly.eval (pairBits (List.replicate fuel true,stateBits distance F v lam s)).length := by
  let L := (stateBits distance F v lam s).length
  let N := (pairBits (List.replicate fuel true,stateBits distance F v lam s)).length
  let C := capPoly.eval L
  have hs := finish_length distance F v lam s j
  have he := finish_event_length distance F v lam s j s rfl
  have hcount := finish_count distance F v lam j s
  have hh := encode_le_bound ((finish distance F v lam j s).2.reverse.map BinaryPhaseFirst.eventBits) C (by
    intro w hw
    obtain ⟨e,he',rfl⟩:=List.mem_map.mp hw
    exact he e (List.mem_reverse.mp he'))
  simp only [List.length_map,List.length_reverse] at hh
  have hcount' := Nat.mul_le_mul_right (2*C+2) hcount
  have hL : L ≤ N := by simp only [L,N,pairBits_length]; omega
  have hf : fuel ≤ N := by simp only [N,pairBits_length,List.length_replicate]; omega
  have hp : C ≤ capPoly.eval N := polynomial_monotone capPoly hL
  have hm := Nat.mul_le_mul (hj.trans hf) (show 2*C+2 ≤ 2*capPoly.eval N+2 by omega)
  simp only [traceCapPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X]
  change _ ≤ 2*capPoly.eval N+1+N*(2*capPoly.eval N+2)
  rw [iterate_pack]
  simp only [pack,pairBits_length,List.append_nil]
  change (stateBits distance F v lam (finish distance F v lam j s).1).length ≤ C at hs
  omega
noncomputable def resource : PolynomialCounter traceCapPoly := PolynomialCounter.choose traceCapPoly
noncomputable def loop (x : List Bool) : List Bool :=
  BoundedIteration.run step (pairBits (extractPrefix x,pairBits (resource.word x,pairBits (discardPrefix x,[]))))
noncomputable def loop_computes : PolyComputes loop :=
  (extractPrefix_computes.pair (resource.computes.pair (discardPrefix_computes.pair (const_computes [])))).comp
    (BoundedIteration.run_computes step_computes)
attribute [local irreducible] loop loop_computes
noncomputable def run (x : List Bool) : List Bool :=
  pairBits (extractPrefix (loop x),WordList.reverse (discardPrefix (loop x)))
noncomputable def run_computes : PolyComputes run :=
  loop_computes.comp (extractPrefix_computes.pair (discardPrefix_computes.comp WordList.reverse_computes))
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (fuel : ℕ) :
    run (pairBits (List.replicate fuel true,stateBits distance F v lam s))=
      pack distance F v lam (finish distance F v lam fuel s).1 (finish distance F v lam fuel s).2 := by
  have hl : loop (pairBits (List.replicate fuel true,stateBits distance F v lam s))=
      pack distance F v lam (finish distance F v lam fuel s).1 (finish distance F v lam fuel s).2.reverse := by
    simp only [loop,extractPrefix_pairBits,discardPrefix_pairBits]
    change BoundedIteration.run step (pairBits (List.replicate fuel true,pairBits (_,
      pack distance F v lam s [])))=_
    rw [BoundedIteration.run_eq]
    · simp only [List.length_replicate,iterate_pack,List.append_nil]
    · intro j hj
      rw [resource.word_length]
      exact iterate_length distance F v lam s fuel j (by simpa only [List.length_replicate] using hj)
  simp only [run,hl,pack,extractPrefix_pairBits,discardPrefix_pairBits,WordList.reverse_encode,
    ←List.map_reverse,List.reverse_reverse]
end MetricKMedianRecovery.BitMachine.BinaryPhaseTrace

end OAI
