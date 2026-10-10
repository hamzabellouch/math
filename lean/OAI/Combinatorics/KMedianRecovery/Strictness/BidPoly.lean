import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Answer

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFinish
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
noncomputable def bidPoly : Polynomial ℕ := BinaryPhaseFirst.run_computes.lengthPolynomial.comp (20*(Polynomial.X+1)^2)
noncomputable def capPoly : Polynomial ℕ := 40*(Polynomial.X+1)^2+4*(Polynomial.X+1)*bidPoly
lemma ctx_bound {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v lam : ℚ) (s : State m d) :
    (BinaryPhaseFirst.context distance F W v s.phase lam).length ≤
      (stateBits distance F v lam s).length+2*(stateBits distance F v lam s).length*(2*(stateBits distance F v lam s).length+2) := by
  let L := (stateBits distance F v lam s).length
  have hm := (dimensions distance F v lam s).1
  have hc := context_length_change distance F s.opened W v s.phase lam
  have ho : (BinaryPhaseFirst.context distance F s.opened v s.phase lam).length ≤ L := by
    simp only [L,stateBits,pairBits_length]; omega
  have hmul := Nat.mul_le_mul hm (show 2*m+2 ≤ 2*L+2 by omega)
  change (BinaryPhaseFirst.context distance F W v s.phase lam).length ≤ L+2*L*(2*L+2)
  nlinarith
lemma first_bid_bound {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (e : Event m d)
    (he : first distance F W v s.phase lam (List.ofFn (fun i : Fin m=>i))=some e) (j : Fin d) :
    (BinaryRational.encode e.bid[j]).length ≤ bidPoly.eval (stateBits distance F v lam s).length := by
  let L := (stateBits distance F v lam s).length
  let q := pairBits (BinaryPhaseFirst.context distance F W v s.phase lam,
    BinaryOpeningActivity.indices (List.ofFn (fun i : Fin m=>i)))
  have hm := (dimensions distance F v lam s).1
  have hc := ctx_bound distance F W v lam s
  have hi := indices_length (List.ofFn (fun i : Fin m=>i)) (by simp only [List.length_ofFn,Nat.le_refl])
  have hmul := Nat.mul_le_mul hm (show 2*m+2 ≤ 2*L+2 by omega)
  have hq : q.length ≤ 20*(L+1)^2 := by
    simp only [q,pairBits_length]
    change (BinaryPhaseFirst.context distance F W v s.phase lam).length ≤ L+2*L*(2*L+2) at hc
    nlinarith
  have hout := BinaryPhaseFirst.run_computes.length_bound q
  have hp := polynomial_monotone BinaryPhaseFirst.run_computes.lengthPolynomial hq
  have heq : BinaryPhaseFirst.run q=true::BinaryPhaseFirst.eventBits e := by
    simp only [q,BinaryPhaseFirst.run_pack,he,BinaryPhaseFirst.resultBits]
  rw [heq] at hout
  have hj := member_length_le (List.ofFn (fun j : Fin d=>BinaryRational.encode e.bid[j]))
    (w:=BinaryRational.encode e.bid[j]) (List.mem_ofFn.mpr ⟨j,rfl⟩)
  simp only [List.length_cons,BinaryPhaseFirst.eventBits,pairBits_length,RationalMatrix.rowEncode_eq] at hout
  simp only [bidPoly,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  change _ ≤ BinaryPhaseFirst.run_computes.lengthPolynomial.eval (20*(L+1)^2)
  have hr : (encode (List.ofFn (fun j : Fin d=>BinaryRational.encode e.bid[j]))).length ≤ BinaryPhaseFirst.run_computes.lengthPolynomial.eval q.length := by omega
  exact hj.trans (hr.trans hp)
lemma finish_invariant {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (fuel : ℕ) (t : State m d)
    (ht : t.phase=s.phase)
    (hb : ∀ j : Fin d,(BinaryRational.encode t.budget[j]).length ≤
      (stateBits distance F v lam s).length+bidPoly.eval (stateBits distance F v lam s).length) :
    (finish distance F v lam fuel t).1.phase=s.phase ∧
    ∀ j : Fin d,(BinaryRational.encode (finish distance F v lam fuel t).1.budget[j]).length ≤
      (stateBits distance F v lam s).length+bidPoly.eval (stateBits distance F v lam s).length := by
  induction fuel generalizing t with
  | zero=>exact ⟨ht,hb⟩
  | succ fuel ih=>
    cases he : first distance F t.opened v t.phase lam (List.ofFn (fun i : Fin m=>i)) with
    | none=>simpa only [finish,he] using And.intro ht hb
    | some e=>
      simp only [finish,he]
      apply ih (update distance v t e) ht
      intro j
      rw [update_get]
      split_ifs
      · have hh := first_bid_bound distance F t.opened v lam s e (by simpa only [ht] using he) j
        omega
      · exact hb j
lemma finish_length {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (fuel : ℕ) :
    (stateBits distance F v lam (finish distance F v lam fuel s).1).length ≤
      capPoly.eval (stateBits distance F v lam s).length := by
  let L := (stateBits distance F v lam s).length
  let B := bidPoly.eval L
  obtain ⟨hp,hb⟩ := finish_invariant distance F v lam s fuel s rfl (fun j=>(initial_budget_length distance F v lam s j).trans (Nat.le_add_right _ _))
  have hc := ctx_bound distance F (finish distance F v lam fuel s).1.opened v lam s
  have hbudget := encode_le_bound (List.ofFn (fun j : Fin d=>BinaryRational.encode (finish distance F v lam fuel s).1.budget[j])) (L+B) (by
    intro w hw
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hw
    exact hb j)
  simp only [List.length_ofFn] at hbudget
  have hd := (dimensions distance F v lam s).2
  have hmul := Nat.mul_le_mul_right (2*(L+B)+2) hd
  change _ ≤ L*(2*(L+B)+2) at hmul
  change (BinaryPhaseFirst.context distance F (finish distance F v lam fuel s).1.opened v s.phase lam).length ≤ L+2*L*(2*L+2) at hc
  simp only [capPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_one]
  change _ ≤ 40*(L+1)^2+4*(L+1)*B
  simp only [stateBits,pairBits_length,RationalMatrix.rowEncode_eq,hp]
  nlinarith

noncomputable def cap : PolynomialCounter capPoly := PolynomialCounter.choose capPoly

noncomputable def run (x : List Bool) : List Bool :=
  BoundedIteration.run step (pairBits (extractPrefix x,pairBits (cap.word (discardPrefix x),discardPrefix x)))
noncomputable def run_computes : PolyComputes run :=
  (extractPrefix_computes.pair ((discardPrefix_computes.comp cap.computes).pair discardPrefix_computes)).comp
    (BoundedIteration.run_computes step_computes)
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (fuel : ℕ) :
    run (pairBits (List.replicate fuel true,stateBits distance F v lam s))=
      stateBits distance F v lam (finish distance F v lam fuel s).1 := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [BoundedIteration.run_eq]
  · simp only [List.length_replicate,iterate_pack]
  · intro j _
    rw [iterate_pack,cap.word_length]
    exact finish_length distance F v lam s j
end MetricKMedianRecovery.BitMachine.BinaryPhaseFinish

end OAI
