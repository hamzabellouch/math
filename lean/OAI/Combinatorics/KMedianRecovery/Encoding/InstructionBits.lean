import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Pack11
import OAI.Combinatorics.KMedianRecovery.Strictness.BidBound

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRunTrace
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate

def instructionBits {m d : ℕ} : Instruction m d → List Bool
  | .opening e=>true::BinaryPhaseFirst.eventBits e
  | .advance=>[false]
def logBits {m d : ℕ} (is : List (Instruction m d)) : List Bool := encode (is.map instructionBits)
lemma logBits_append {m d : ℕ} (xs ys : List (Instruction m d)) :
    logBits (xs++ys)=logBits xs++logBits ys := by
  simp only [logBits,List.map_append,encode_append]
noncomputable def finished (x : List Bool) : List Bool := BinaryPhaseTrace.run (pairBits (BinaryPhaseRun.fuel x,x))
noncomputable def finished_computes : PolyComputes finished :=
  (BinaryPhaseRun.fuel_computes.pair id_computes).comp BinaryPhaseTrace.run_computes
lemma finished_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : finished (stateBits distance F v lam s)=
      BinaryPhaseTrace.pack distance F v lam (finish distance F v lam F.card s).1 (finish distance F v lam F.card s).2 := by
  rw [finished,BinaryPhaseRun.fuel_pack,BinaryPhaseTrace.run_pack]
noncomputable def chunk (x : List Bool) : List Bool :=
  WordList.map (List.cons true) (discardPrefix (finished x))++logBits ([Instruction.advance] : List (Instruction 0 0))
noncomputable def chunk_computes : PolyComputes chunk := by
  have chunkComputes :=
    ((finished_computes.comp discardPrefix_computes).comp (map_computes (prefix_computes true))).append
      (const_computes (logBits ([Instruction.advance] : List (Instruction 0 0))))
  unfold chunk
  simpa only [Function.comp_def] using chunkComputes
lemma chunk_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : chunk (stateBits distance F v lam s)=
      logBits ((finish distance F v lam F.card s).2.map Instruction.opening++[Instruction.advance]) := by
  rw [logBits_append]
  simp only [chunk,finished_pack,BinaryPhaseTrace.pack,discardPrefix_pairBits,map_encode,
    logBits,List.map_map,Function.comp_def,instructionBits,List.map_cons,List.map_nil]
attribute [local irreducible] chunk chunk_computes
noncomputable def step (x : List Bool) : List Bool :=
  pairBits (BinaryPhaseRun.step (extractPrefix x),discardPrefix x++chunk (extractPrefix x))
noncomputable def step_computes : PolyComputes step :=
  (extractPrefix_computes.comp BinaryPhaseRun.step_computes).pair
    (discardPrefix_computes.append (extractPrefix_computes.comp chunk_computes))
def pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (is : List (Instruction m d)) : List Bool :=
  pairBits (stateBits distance F v lam s,logBits is)
lemma step_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (is : List (Instruction m d)) :
    step (pack distance F v lam s is)=pack distance F v lam
      (advance distance v (finish distance F v lam F.card s).1)
      (is++(finish distance F v lam F.card s).2.map Instruction.opening++[Instruction.advance]) := by
  simp only [step,pack,extractPrefix_pairBits,discardPrefix_pairBits,BinaryPhaseRun.step_pack,
    chunk_pack,logBits_append,List.append_assoc]
lemma iterate_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q : ℕ) (s : State m d) (is : List (Instruction m d)) :
    step^[q] (pack distance F v lam s is)=pack distance F v lam
      (RationalPhase.run distance F v lam q s).1 (is++(RationalPhase.run distance F v lam q s).2) := by
  induction q generalizing s is with
  | zero=>simp only [Function.iterate_zero,Function.id_def,RationalPhase.run,List.append_nil]
  | succ q ih=>
    rw [Function.iterate_succ_apply,step_pack,ih]
    simp only [RationalPhase.run,List.append_assoc,List.singleton_append]
lemma source_run_next {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q : ℕ) (s : State m d) :
    (RationalPhase.run distance F v lam q (advance distance v (finish distance F v lam F.card s).1)).1=
      (RationalPhase.run distance F v lam (q+1) s).1 := rfl
lemma log_length {m d S : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q : ℕ) (s : State m d)
    (hs : ∀ j ≤ q,(stateBits distance F v lam (RationalPhase.run distance F v lam j s).1).length ≤ S) :
    (logBits (RationalPhase.run distance F v lam q s).2).length ≤ q*chunk_computes.lengthPolynomial.eval S := by
  induction q generalizing s with
  | zero=>simp only [RationalPhase.run,logBits,List.map_nil,encode,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | succ q ih=>
    let t := advance distance v (finish distance F v lam F.card s).1
    have hb (j : ℕ) (hj : j ≤ q) : (stateBits distance F v lam (RationalPhase.run distance F v lam j t).1).length ≤ S :=
      hs (j+1) (by omega)
    have hi := ih t hb
    have h0 : (stateBits distance F v lam s).length ≤ S := hs 0 (Nat.zero_le _)
    have hh := (chunk_computes.length_bound (stateBits distance F v lam s)).trans
      (polynomial_monotone chunk_computes.lengthPolynomial h0)
    rw [chunk_pack] at hh
    simp only [logBits_append,List.length_append] at hh
    simp only [RationalPhase.run,logBits_append,List.length_append]
    have he : logBits (Instruction.advance::(RationalPhase.run distance F v lam q t).2)=
        logBits ([Instruction.advance] : List (Instruction m d))++logBits (RationalPhase.run distance F v lam q t).2 := by
      exact logBits_append [Instruction.advance] _
    change (logBits ((finish distance F v lam F.card s).2.map Instruction.opening)).length+
      (logBits (Instruction.advance::(RationalPhase.run distance F v lam q t).2)).length ≤ _
    rw [he,List.length_append]
    nlinarith
noncomputable def capPoly : Polynomial ℕ :=
  2*BinaryPhaseRun.sizeBound+1+Polynomial.X*(chunk_computes.lengthPolynomial.comp BinaryPhaseRun.sizeBound)
lemma iterate_length {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q : ℕ) (s : State m d) (j : ℕ) (hj : j ≤ q) :
    (step^[j] (pack distance F v lam s [])).length ≤
      capPoly.eval (pairBits (List.replicate q true,stateBits distance F v lam s)).length := by
  let N := (pairBits (List.replicate q true,stateBits distance F v lam s)).length
  have hL : (stateBits distance F v lam s).length ≤ N := by simp only [N,pairBits_length]; omega
  have hq : q ≤ N := by simp only [N,pairBits_length,List.length_replicate]; omega
  have hb (i : ℕ) (hi : i ≤ j) :
      (stateBits distance F v lam (RationalPhase.run distance F v lam i s).1).length ≤ BinaryPhaseRun.sizeBound.eval N :=
    BinaryPhaseRun.run_length_bound distance F v lam s hL i (hi.trans (hj.trans hq))
  have hh := log_length distance F v lam j s hb
  have hs := hb j le_rfl
  have hm := Nat.mul_le_mul_right (chunk_computes.lengthPolynomial.eval (BinaryPhaseRun.sizeBound.eval N)) (hj.trans hq)
  rw [iterate_pack]
  simp only [pack,List.nil_append,pairBits_length]
  simp only [capPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one,
    Polynomial.eval_X,Polynomial.eval_comp]
  simp only [N,pairBits_length] at hs hh hm
  omega
noncomputable def cap : PolynomialCounter capPoly := PolynomialCounter.choose capPoly
noncomputable def run (x : List Bool) : List Bool :=
  BoundedIteration.run step (pairBits (extractPrefix x,pairBits (cap.word x,pairBits (discardPrefix x,[]))))
noncomputable def run_computes : PolyComputes run :=
  (extractPrefix_computes.pair (cap.computes.pair (discardPrefix_computes.pair (const_computes [])))).comp
    (BoundedIteration.run_computes step_computes)
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q : ℕ) (s : State m d) :
    run (pairBits (List.replicate q true,stateBits distance F v lam s))=
      pack distance F v lam (RationalPhase.run distance F v lam q s).1 (RationalPhase.run distance F v lam q s).2 := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits]
  change BoundedIteration.run step (pairBits (List.replicate q true,pairBits (_,
    pack distance F v lam s [])))=_
  rw [BoundedIteration.run_eq]
  · simp only [List.length_replicate,iterate_pack,List.nil_append]
  · intro j hj
    rw [cap.word_length]
    exact iterate_length distance F v lam q s j (by simpa only [List.length_replicate] using hj)
end MetricKMedianRecovery.BitMachine.BinaryRunTrace

end OAI
