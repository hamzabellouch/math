import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Fuel
import OAI.Combinatorics.KMedianRecovery.Geometry.NearestHeight

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate RationalHeight
open BinaryPhaseFinish
noncomputable def bidBound : Polynomial ℕ := BinaryPhaseFinish.bidPoly.comp (100*(Polynomial.X+1)^2)
noncomputable def budgetBound : Polynomial ℕ := Polynomial.X+bidBound+100*(Polynomial.X+1)^2
noncomputable def sizeBound : Polynomial ℕ := 1000*(Polynomial.X+1)^3+4*(Polynomial.X+1)*bidBound
lemma context_height {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) :
    Height v (stateBits distance F v lam s).length ∧
    Height s.phase (stateBits distance F v lam s).length ∧
    ∀ f j, Height (distance f j) (stateBits distance F v lam s).length := by
  let ws := [Rectangular.encode distance,
      BinaryOpeningActivity.indices ((subtypeList s.opened).map Subtype.val),BinaryRational.encode v,
      BinaryRational.encode s.phase,BinaryRational.encode lam,BinaryRational.encode 0,[],
      List.replicate d true,BinaryOpeningActivity.indices ((subtypeList F).map Subtype.val)]
  have hc : (encode ws).length ≤ (stateBits distance F v lam s).length := by
    change (BinaryPhaseFirst.context distance F s.opened v s.phase lam).length ≤ _
    simp only [stateBits,pairBits_length]; omega
  have hv := member_length_le ws (w:=BinaryRational.encode v) (by simp only [ws,List.mem_cons,true_or,or_true])
  have hz := member_length_le ws (w:=BinaryRational.encode s.phase) (by simp only [ws,List.mem_cons,true_or,or_true])
  have hd := member_length_le ws (w:=Rectangular.encode distance) (by simp only [ws,List.mem_cons,true_or])
  refine ⟨(BinaryRational.input_height v).mono (hv.trans hc),
    (BinaryRational.input_height s.phase).mono (hz.trans hc),?_⟩
  intro f j
  have hr := member_length_le (List.ofFn (fun f : Fin m=>RationalMatrix.rowEncode (distance f)))
    (w:=RationalMatrix.rowEncode (distance f)) (List.mem_ofFn.mpr ⟨f,rfl⟩)
  have he := member_length_le (List.ofFn (fun j : Fin d=>BinaryRational.encode (distance f j)))
    (w:=BinaryRational.encode (distance f j)) (List.mem_ofFn.mpr ⟨j,rfl⟩)
  rw [RationalMatrix.rowEncode_eq] at hr
  exact (BinaryRational.input_height (distance f j)).mono (he.trans (hr.trans (hd.trans hc)))
lemma change_phase_length {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (z : ℚ) :
    (stateBits distance F v lam {s with phase:=z}).length ≤
      (stateBits distance F v lam s).length+4*(BinaryRational.encode z).length := by
  simp only [stateBits,pairBits_length,BinaryPhaseFirst.context,length_encode,List.map_cons,List.sum_cons,
    List.length_cons,List.map_nil,List.sum_nil,List.length_nil]
  omega
lemma reference_length {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (z : ℚ) (hz : Height z (3*(N+1)^2)) :
    (stateBits distance F v lam {s with phase:=z}).length ≤ 100*(N+1)^2 := by
  have h := change_phase_length distance F v lam s z
  have hh := BinaryRational.encode_height hz
  nlinarith
lemma bid_bound {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (z : ℚ) (hz : Height z (3*(N+1)^2)) (e : Event m d)
    (he : first distance F W v z lam (List.ofFn (fun i : Fin m=>i))=some e) (j : Fin d) :
    (BinaryRational.encode e.bid[j]).length ≤ bidBound.eval N := by
  have hh := first_bid_bound distance F W v lam {s with phase:=z} e he j
  have hp := polynomial_monotone BinaryPhaseFinish.bidPoly (reference_length distance F v lam s hL z hz)
  exact (hh.trans hp).trans_eq (by simp only [bidBound,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one])
lemma finish_bound {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (fuel : ℕ) (t : State m d) (hz : Height t.phase (3*(N+1)^2))
    (hb : ∀ j : Fin d,(BinaryRational.encode t.budget[j]).length ≤ budgetBound.eval N) :
    (finish distance F v lam fuel t).1.phase=t.phase ∧
    ∀ j : Fin d,(BinaryRational.encode (finish distance F v lam fuel t).1.budget[j]).length ≤ budgetBound.eval N := by
  induction fuel generalizing t with
  | zero=>exact ⟨rfl,hb⟩
  | succ fuel ih=>
    cases he : first distance F t.opened v t.phase lam (List.ofFn (fun i : Fin m=>i)) with
    | none=>simpa only [finish,he] using And.intro (rfl : t.phase=t.phase) hb
    | some e=>
      simp only [finish,he]
      apply ih (update distance v t e) hz
      intro j
      rw [update_get]
      split_ifs
      · have hh := bid_bound distance F t.opened v lam s hL t.phase hz e he j
        simp only [budgetBound,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,
          Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_one]
        omega
      · exact hb j
lemma clipped_bound {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (z : ℚ) (hz : Height z (3*(N+1)^2)) (W : Finset (Fin m)) (j : Fin d) :
    (BinaryRational.encode (clipped distance v z W j)).length ≤ budgetBound.eval N := by
  let A := 3*(N+1)^2
  have hNA : N ≤ A := by dsimp only [A]; nlinarith
  obtain ⟨hv,_,hd⟩ := context_height distance F v lam s
  have hv' := hv.mono (hL.trans hNA)
  have h1 : Height (1:ℚ) 0 := natCast 1 0 (by norm_num)
  have h3 : Height (3:ℚ) 2 := natCast 3 2 (by norm_num)
  have ht : Height (1-3*v) (A+3) := by convert h1.sub (h3.mul hv') using 1; omega
  have hn := nearest_height distance (fun f j=>(hd f j).mono (hL.trans hNA)) W j
  have hh : Height (clipped distance v z W j) (2*A+3) := by
    unfold clipped
    split_ifs
    · exact (hz.mono (by dsimp only [A]; omega)).min ((ht.mul hn).mono (by omega))
    · exact hz.mono (by dsimp only [A]; omega)
  have he := BinaryRational.encode_height hh
  simp only [budgetBound,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_one]
  dsimp only [A] at he
  nlinarith
lemma run_bound_invariant {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (q : ℕ) (t : State m d)
    (hz : ∀ j ≤ q,Height ((1+v^2)^j*t.phase) (3*(N+1)^2))
    (hb : ∀ j : Fin d,(BinaryRational.encode t.budget[j]).length ≤ budgetBound.eval N) :
    (RationalPhase.run distance F v lam q t).1.phase=(1+v^2)^q*t.phase ∧
    ∀ j : Fin d,(BinaryRational.encode (RationalPhase.run distance F v lam q t).1.budget[j]).length ≤ budgetBound.eval N := by
  induction q generalizing t with
  | zero=>simpa only [RationalPhase.run,pow_zero,one_mul] using And.intro (rfl : t.phase=t.phase) hb
  | succ q ih=>
    let r := finish distance F v lam F.card t
    obtain ⟨hp,hbudget⟩ := finish_bound distance F v lam s hL F.card t
      (by simpa only [pow_zero,one_mul] using hz 0 (Nat.zero_le _)) hb
    change r.1.phase=t.phase at hp
    change (∀ j : Fin d,(BinaryRational.encode r.1.budget[j]).length ≤ budgetBound.eval N) at hbudget
    have hphase (j : ℕ) (hj : j ≤ q) : Height ((1+v^2)^j*(advance distance v r.1).phase) (3*(N+1)^2) := by
      change Height ((1+v^2)^j*((1+v^2)*r.1.phase)) _
      rw [hp,←mul_assoc,←pow_succ]
      exact hz (j+1) (by omega)
    have hb' (j : Fin d) : (BinaryRational.encode (advance distance v r.1).budget[j]).length ≤ budgetBound.eval N := by
      rw [advance_get]
      split_ifs
      · apply clipped_bound distance F v lam s hL
        rw [hp]
        simpa only [pow_one] using hz 1 (by omega)
      · exact hbudget j
    obtain ⟨hpres,hbres⟩ := ih (advance distance v r.1) hphase hb'
    simp only [RationalPhase.run]
    refine ⟨?_,hbres⟩
    rw [hpres]
    change (1+v^2)^q*((1+v^2)*r.1.phase)=_
    rw [hp,pow_succ]
    ring
lemma state_length_bound {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s t : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (hz : Height t.phase (3*(N+1)^2))
    (hb : ∀ j : Fin d,(BinaryRational.encode t.budget[j]).length ≤ budgetBound.eval N) :
    (stateBits distance F v lam t).length ≤ sizeBound.eval N := by
  have hdim := dimensions distance F v lam s
  have hctx := ctx_bound distance F t.opened v lam {s with phase:=t.phase}
  have href := reference_length distance F v lam s hL t.phase hz
  have hchg := context_length_change distance F s.opened t.opened v t.phase lam
  have hctx0 : (BinaryPhaseFirst.context distance F s.opened v t.phase lam).length ≤
      (stateBits distance F v lam {s with phase:=t.phase}).length := by
    simp only [stateBits,pairBits_length]; omega
  have hbudget := encode_le_bound (List.ofFn (fun j : Fin d=>BinaryRational.encode t.budget[j])) (budgetBound.eval N) (by
    intro w hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact hb j)
  simp only [List.length_ofFn] at hbudget
  have hmul := Nat.mul_le_mul_right (2*budgetBound.eval N+2) (hdim.2.trans hL)
  have hmask := Nat.mul_le_mul (hdim.1.trans hL) (show 2*m+2 ≤ 2*N+2 by omega)
  simp only [stateBits,pairBits_length,RationalMatrix.rowEncode_eq]
  simp only [sizeBound,budgetBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_one] at hbudget hmul ⊢
  nlinarith
lemma run_length_bound {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (q : ℕ) (hq : q ≤ N) :
    (stateBits distance F v lam (RationalPhase.run distance F v lam q s).1).length ≤ sizeBound.eval N := by
  obtain ⟨hv,hz,_⟩ := context_height distance F v lam s
  have hv' := hv.mono hL
  have hz' := hz.mono hL
  have h1 : Height (1:ℚ) 0 := natCast 1 0 (by norm_num)
  have hK : Height (1+v^2) (2*N+1) := by convert h1.add (hv'.pow 2) using 1; omega
  have hphases (j : ℕ) (hj : j ≤ q) : Height ((1+v^2)^j*s.phase) (3*(N+1)^2) := by
    apply ((hK.pow j).mul hz').mono
    have hjN : j ≤ N := hj.trans hq
    nlinarith
  have hb (j : Fin d) : (BinaryRational.encode s.budget[j]).length ≤ budgetBound.eval N := by
    have hh := (initial_budget_length distance F v lam s j).trans hL
    simp only [budgetBound,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_one]
    omega
  obtain ⟨hp,hbudget⟩ := run_bound_invariant distance F v lam s hL q s hphases hb
  apply state_length_bound distance F v lam s _ hL _ hbudget
  rw [hp]
  exact hphases q le_rfl
noncomputable def cap : PolynomialCounter sizeBound := PolynomialCounter.choose sizeBound
noncomputable def run (x : List Bool) : List Bool := BoundedIteration.run step
  (pairBits (extractPrefix x,pairBits (cap.word x,discardPrefix x)))
noncomputable def run_computes : PolyComputes run :=
  (extractPrefix_computes.pair (cap.computes.pair discardPrefix_computes)).comp
    (BoundedIteration.run_computes step_computes)
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q : ℕ) (s : State m d) :
    run (pairBits (List.replicate q true,stateBits distance F v lam s))=
      stateBits distance F v lam (RationalPhase.run distance F v lam q s).1 := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [BoundedIteration.run_eq]
  · simp only [List.length_replicate,iterate_pack]
  · intro j hj
    rw [iterate_pack,cap.word_length]
    apply run_length_bound
    · simp only [pairBits_length,List.length_replicate]; omega
    · simp only [List.length_replicate] at hj
      simp only [pairBits_length,List.length_replicate]; omega
end MetricKMedianRecovery.BitMachine.BinaryPhaseRun

end OAI
