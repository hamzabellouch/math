import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.StateBits

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFinish
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
noncomputable def answer (x : List Bool) : List Bool :=
  BinaryPhaseFirst.run (pairBits (extractPrefix x,allFacilities (extractPrefix x)))
noncomputable def answer_computes : PolyComputes answer :=
  (extractPrefix_computes.pair (extractPrefix_computes.comp allFacilities_computes)).comp BinaryPhaseFirst.run_computes
lemma answer_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) :
    answer (stateBits distance F v lam s)=BinaryPhaseFirst.resultBits
      (first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m=>i))) := by
  simp only [answer,stateBits,extractPrefix_pairBits,allFacilities_context,BinaryPhaseFirst.run_pack]
noncomputable def step (x : List Bool) : List Bool :=
  if answer x=[] then x else BinaryPhaseUpdate.run (pairBits (x,(answer x).tail))
noncomputable def step_computes : PolyComputes step := by
  have h := (answer_computes.comp isEmpty_computes).cond id_computes
    ((id_computes.pair (answer_computes.comp WordOperations.tail_computes)).comp BinaryPhaseUpdate.run_computes)
  change PolyComputes (fun x=>if answer x=[] then x else BinaryPhaseUpdate.run (pairBits (x,(answer x).tail)))
  simpa only [Function.comp_def,decide_eq_true_eq,id_eq] using h
lemma step_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : step (stateBits distance F v lam s)=
      stateBits distance F v lam
        (match first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m=>i)) with
         | none=>s | some e=>update distance v s e) := by
  rw [step,answer_pack]
  cases he : first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m=>i)) with
  | none=>rfl
  | some e=>simp only [BinaryPhaseFirst.resultBits,List.cons_ne_nil,ite_false,List.tail_cons,BinaryPhaseUpdate.run_pack]
lemma finish_none {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d)
    (h : first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m=>i))=none) (fuel : ℕ) :
    finish distance F v lam fuel s=(s,[]) := by
  cases fuel <;> simp only [finish,h]
lemma iterate_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (fuel : ℕ) (s : State m d) :
    step^[fuel] (stateBits distance F v lam s)=stateBits distance F v lam (finish distance F v lam fuel s).1 := by
  induction fuel generalizing s with
  | zero=>rfl
  | succ fuel ih=>
    rw [Function.iterate_succ_apply,step_pack]
    cases he : first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m=>i)) with
    | none=>simp only [ih,finish_none distance F v lam s he,finish,he]
    | some e=>simp only [ih,finish,he]

lemma member_length_le (ws : List (List Bool)) {w : List Bool} (hw : w∈ws) : w.length≤(encode ws).length := by
  induction ws with
  | nil=>simp only [List.not_mem_nil] at hw
  | cons a ws ih=>
    simp only [encode,length_cons]
    rcases List.mem_cons.mp hw with h|h
    · subst w; omega
    · have hh:=ih h; omega
lemma indices_length {m : ℕ} (fs : List (Fin m)) (hl : fs.length ≤ m) :
    (BinaryOpeningActivity.indices fs).length ≤ m*(2*m+2) := by
  apply (encode_le_bound (fs.map (fun i=>i.val.bits)) m (by
    intro w hw
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp hw
    exact (Indices.bits_length_le i.val).trans (Nat.le_of_lt i.isLt))).trans
  simpa only [List.length_map] using Nat.mul_le_mul_right (2*m+2) hl
lemma finset_indices_length {m : ℕ} (W : Finset (Fin m)) :
    (BinaryOpeningActivity.indices ((subtypeList W).map Subtype.val)).length ≤ m*(2*m+2) := by
  apply indices_length
  simp only [List.length_map,subtypeList,List.length_ofFn]
  exact (Finset.card_le_univ W).trans_eq (Fintype.card_fin m)
lemma context_length_change {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W W' : Finset (Fin m))
    (v z lam : ℚ) :
    (BinaryPhaseFirst.context distance F W' v z lam).length≤
      (BinaryPhaseFirst.context distance F W v z lam).length+2*m*(2*m+2) := by
  have hh:=finset_indices_length W'
  simp only [BinaryPhaseFirst.context,length_encode,List.map_cons,List.sum_cons,List.length_cons,
    List.map_nil,List.sum_nil,List.length_nil]
  nlinarith
lemma dimensions {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : m≤(stateBits distance F v lam s).length ∧ d≤(stateBits distance F v lam s).length := by
  have hm := length_le_encode (List.ofFn (fun i : Fin m=>RationalMatrix.rowEncode (distance i)))
  have h0 := member_length_le [Rectangular.encode distance,
      BinaryOpeningActivity.indices ((subtypeList s.opened).map Subtype.val),BinaryRational.encode v,
      BinaryRational.encode s.phase,BinaryRational.encode lam,BinaryRational.encode 0,[],
      List.replicate d true,BinaryOpeningActivity.indices ((subtypeList F).map Subtype.val)]
      (w:=Rectangular.encode distance) (by simp only [List.mem_cons, true_or])
  have hd := length_le_encode (List.ofFn (fun j : Fin d=>BinaryRational.encode s.budget[j]))
  simp only [List.length_ofFn] at hm hd
  change _≤(BinaryPhaseFirst.context distance F s.opened v s.phase lam).length at h0
  change m≤(Rectangular.encode distance).length at hm
  simp only [stateBits,pairBits_length,RationalMatrix.rowEncode_eq]
  constructor <;> omega
lemma initial_budget_length {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (j : Fin d) :
    (BinaryRational.encode s.budget[j]).length≤(stateBits distance F v lam s).length := by
  have hh:=member_length_le (List.ofFn (fun j : Fin d=>BinaryRational.encode s.budget[j]))
    (w:=BinaryRational.encode s.budget[j]) (List.mem_ofFn.mpr ⟨j,rfl⟩)
  simp only [stateBits,pairBits_length,RationalMatrix.rowEncode_eq]
  omega
end MetricKMedianRecovery.BitMachine.BinaryPhaseFinish

end OAI
