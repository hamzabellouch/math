import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.LoopSize
import OAI.Combinatorics.KMedianRecovery.Machines.StartResources

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves RationalHeight CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCoupled (stateBits outcomeBits outputBits)
lemma initial_prices_length {m : ℕ} (base : List Bool) (b l u : ℚ) (precision k total : ℕ)
    (T U : List (List (Label (Fin m)))) :
    (BinaryRational.encode l).length ≤ (pack base b precision k ⟨0,total,.inr (initial l u T U)⟩).length ∧
    (BinaryRational.encode u).length ≤ (pack base b precision k ⟨0,total,.inr (initial l u T U)⟩).length := by
  simp only [pack,outcomeBits,stateBits,CanonicalCoupledMerge.initial,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil,List.length_replicate,pairBits_length]
  omega
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma run_initial (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
    (v M l u : ℚ) (eta lo hi : ℝ) (N precision total k : ℕ)
    (hF : F.Nonempty) (hM : 0<M) (hN : 3 ≤ N)
    (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0 ≤ eta)
    (hhi : hi ≤ 8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ) ≤ eta)
    (hdiam : ∀ i∈F,∀ j,dist i (loc j) ≤ (M:ℝ))
    (T U : List (List (Label (Fin m)))) (hc : Certified loc F v eta lo hi 0 total k (initial l u T U)) :
    run (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v 0 0)
      (20*N*M) precision k ⟨0,total,.inr (initial l u T U)⟩)=
      outputBits (CanonicalCoupledMerge.run loc distance F v M N precision k 0 total (initial l u T U)) := by
  apply run_pack distance loc hmetric F ∅ v 0 M eta lo hi N precision 0 total k
    hF hM hN hv hv1 hlo heta hhi hprecision hdiam _ hc
  · trivial
  · dsimp only
    apply initial_resources
    · exact (BinaryRational.input_height l).mono (initial_prices_length _ _ _ _ _ _ _ _ _).1
    · exact (BinaryRational.input_height u).mono (initial_prices_length _ _ _ _ _ _ _ _ _).2
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

namespace MetricKMedianRecovery.BitMachine.BinaryInitial
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outputBits)
attribute [local irreducible] BinaryInitialQuery.count BinaryInitialQuery.history BinaryCoupledLoop.run BinaryBisection.run
def pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (F : Finset (Fin m)) (v lo M : ℚ) (N precision total k : ℕ) : List Bool :=
  encode [BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v 0 0,
    List.replicate N true,List.replicate precision true,List.replicate total true,k.bits,
    BinaryRational.encode lo,BinaryRational.encode M]
def output {m : ℕ} : StartOutput (Fin m)→List Bool
  | .small o=>pairBits ([],outputBits o)
  | .normal o=>pairBits ([true],outputBits o)
noncomputable def unaryRat {f : List Bool→List Bool} (hf : PolyComputes f) :
    PolyComputes (fun x=>BinaryRational.encode ((f x).length:ℚ)) := by
  simpa only [Function.comp_def,UnaryResources.lengthBits_eq,value_bits] using RatOps.nat (hf.comp UnaryResources.lengthBits_computes)
noncomputable def high (x : List Bool) : List Bool := BinaryRational.encode
  (8*((field 1 (field 0 x)).length:ℚ)*BinaryRational.decode (field 6 x))
noncomputable def high_computes : PolyComputes high :=
  RatOps.mul (RatOps.mul (RatOps.const 8) (unaryRat ((field_computes 0).comp (field_computes 1))))
    (RatOps.ofWords (field_computes 6))
noncomputable def far (x : List Bool) : List Bool := BinaryRational.encode
  (20*((field 1 x).length:ℚ)*BinaryRational.decode (field 6 x))
noncomputable def far_computes : PolyComputes far :=
  RatOps.mul (RatOps.mul (RatOps.const 20) (unaryRat (field_computes 1))) (RatOps.ofWords (field_computes 6))
noncomputable def ctx (x : List Bool) : List Bool := pairBits (field 3 x,field 0 x)
noncomputable def ctx_computes : PolyComputes ctx := (field_computes 3).pair (field_computes 0)

noncomputable def loInput (x : List Bool) : List Bool := pairBits (ctx x,field 5 x)
noncomputable def loInput_computes : PolyComputes loInput := ctx_computes.pair (field_computes 5)

noncomputable def loCount (x : List Bool) : List Bool := BinaryInitialQuery.count (loInput x)
noncomputable def loCount_computes : PolyComputes loCount := loInput_computes.comp BinaryInitialQuery.count_computes

noncomputable def loHistory (x : List Bool) : List Bool := BinaryInitialQuery.history (loInput x)
noncomputable def loHistory_computes : PolyComputes loHistory := loInput_computes.comp BinaryInitialQuery.history_computes

noncomputable def loFinish (x : List Bool) : List Bool := encode [((fun _=>[])) x,(field 5) x,(loHistory) x]
noncomputable def loFinish_computes : PolyComputes loFinish := list_computes [(fun _=>[]),field 5,loHistory] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨const_computes []⟩
  · exact ⟨field_computes 5⟩
  · exact ⟨loHistory_computes⟩)

noncomputable def bracketInput (x : List Bool) : List Bool := encode [(field 2) x,(ctx) x,(field 4) x,(field 5) x,(high) x]
noncomputable def bracketInput_computes : PolyComputes bracketInput := list_computes [field 2,ctx,field 4,field 5,high] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl
  · exact ⟨field_computes 2⟩
  · exact ⟨ctx_computes⟩
  · exact ⟨field_computes 4⟩
  · exact ⟨field_computes 5⟩
  · exact ⟨high_computes⟩)

noncomputable def bracket (x : List Bool) : List Bool := BinaryBisection.run BinaryInitialQuery.count (bracketInput x)
noncomputable def bracket_computes : PolyComputes bracket := bracketInput_computes.comp (BinaryBisection.run_computes BinaryInitialQuery.count_computes)

noncomputable def lower (x : List Bool) : List Bool := extractPrefix (bracket x)
noncomputable def lower_computes : PolyComputes lower := bracket_computes.comp extractPrefix_computes

noncomputable def lowerInput (x : List Bool) : List Bool := pairBits (ctx x,lower x)
noncomputable def lowerInput_computes : PolyComputes lowerInput := ctx_computes.pair lower_computes

noncomputable def lowerCount (x : List Bool) : List Bool := BinaryInitialQuery.count (lowerInput x)
noncomputable def lowerCount_computes : PolyComputes lowerCount := lowerInput_computes.comp BinaryInitialQuery.count_computes

noncomputable def lowerHistory (x : List Bool) : List Bool := BinaryInitialQuery.history (lowerInput x)
noncomputable def lowerHistory_computes : PolyComputes lowerHistory := lowerInput_computes.comp BinaryInitialQuery.history_computes

noncomputable def lowerFinish (x : List Bool) : List Bool := encode [((fun _=>[])) x,(lower) x,(lowerHistory) x]
noncomputable def lowerFinish_computes : PolyComputes lowerFinish := list_computes [(fun _=>[]),lower,lowerHistory] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨const_computes []⟩
  · exact ⟨lower_computes⟩
  · exact ⟨lowerHistory_computes⟩)

noncomputable def upper (x : List Bool) : List Bool := discardPrefix (bracket x)
noncomputable def upper_computes : PolyComputes upper := bracket_computes.comp discardPrefix_computes

noncomputable def upperInput (x : List Bool) : List Bool := pairBits (ctx x,upper x)
noncomputable def upperInput_computes : PolyComputes upperInput := ctx_computes.pair upper_computes

noncomputable def upperCount (x : List Bool) : List Bool := BinaryInitialQuery.count (upperInput x)
noncomputable def upperCount_computes : PolyComputes upperCount := upperInput_computes.comp BinaryInitialQuery.count_computes

noncomputable def upperHistory (x : List Bool) : List Bool := BinaryInitialQuery.history (upperInput x)
noncomputable def upperHistory_computes : PolyComputes upperHistory := upperInput_computes.comp BinaryInitialQuery.history_computes

noncomputable def upperFinish (x : List Bool) : List Bool := encode [((fun _=>[])) x,(upper) x,(upperHistory) x]
noncomputable def upperFinish_computes : PolyComputes upperFinish := list_computes [(fun _=>[]),upper,upperHistory] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨const_computes []⟩
  · exact ⟨upper_computes⟩
  · exact ⟨upperHistory_computes⟩)

noncomputable def initialState (x : List Bool) : List Bool := encode [((fun _=>[])) x,((fun _=>[])) x,((fun _=>[])) x,(lower) x,(upper) x,(upperHistory) x,(lowerHistory) x]
noncomputable def initialState_computes : PolyComputes initialState := list_computes [(fun _=>[]),(fun _=>[]),(fun _=>[]),lower,upper,upperHistory,lowerHistory] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨const_computes []⟩
  · exact ⟨const_computes []⟩
  · exact ⟨const_computes []⟩
  · exact ⟨lower_computes⟩
  · exact ⟨upper_computes⟩
  · exact ⟨upperHistory_computes⟩
  · exact ⟨lowerHistory_computes⟩)

noncomputable def initialOutcome (x : List Bool) : List Bool := pairBits ([true],initialState x)
noncomputable def initialOutcome_computes : PolyComputes initialOutcome := (const_computes [true]).pair initialState_computes

noncomputable def loopInput (x : List Bool) : List Bool := encode [(field 0) x,(field 3) x,((fun _=>[])) x,(far) x,(field 2) x,(field 4) x,(initialOutcome) x]
noncomputable def loopInput_computes : PolyComputes loopInput := list_computes [field 0,field 3,(fun _=>[]),far,field 2,field 4,initialOutcome] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨field_computes 0⟩
  · exact ⟨field_computes 3⟩
  · exact ⟨const_computes []⟩
  · exact ⟨far_computes⟩
  · exact ⟨field_computes 2⟩
  · exact ⟨field_computes 4⟩
  · exact ⟨initialOutcome_computes⟩)

noncomputable def normal (x : List Bool) : List Bool := if value (lowerCount x)=value (field 4 x) then lowerFinish x else
  if value (upperCount x)=value (field 4 x) then upperFinish x else BinaryCoupledLoop.run (loopInput x)
noncomputable def normal_computes : PolyComputes normal := by
  change PolyComputes (fun x=>if value (lowerCount x)=value (field 4 x) then lowerFinish x else
    if value (upperCount x)=value (field 4 x) then upperFinish x else BinaryCoupledLoop.run (loopInput x))
  simpa only [decide_eq_true_eq,Function.comp_def] using (NatOps.eq lowerCount_computes (field_computes 4)).cond
    lowerFinish_computes ((NatOps.eq upperCount_computes (field_computes 4)).cond
      upperFinish_computes (loopInput_computes.comp BinaryCoupledLoop.run_computes))

noncomputable def run (x : List Bool) : List Bool := if value (loCount x)≤value (field 4 x) then pairBits ([],loFinish x) else pairBits ([true],normal x)
noncomputable def run_computes : PolyComputes run := by
  change PolyComputes (fun x=>if value (loCount x)≤value (field 4 x) then pairBits ([],loFinish x) else pairBits ([true],normal x))
  simpa only [decide_eq_true_eq,Function.comp_def] using (NatOps.le loCount_computes (field_computes 4)).cond
    ((const_computes []).pair loFinish_computes) ((const_computes [true]).pair normal_computes)

end MetricKMedianRecovery.BitMachine.BinaryInitial

end OAI
