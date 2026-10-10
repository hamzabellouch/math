import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplerUpdate
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplerDraw

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open BitMachine RationalHeight
variable {n : ℕ}
def State.initial : State n := ⟨∅,[]⟩
def State.Bounded (m : ℕ) (s : State n) : Prop := s.leaves.length ≤ m ∧ s.deleted.card ≤ m
lemma initial_height (K : ℕ) : (State.initial (n:=n)).Height K := by simp [State.initial,State.Height]
lemma initial_bounded (m : ℕ) : (State.initial (n:=n)).Bounded m := by simp [State.initial,State.Bounded]
lemma retain_bounded (m : ℕ) (s t : State n) (ht : retain m s=some t) : t.Bounded m := by
  unfold retain at ht
  split_ifs at ht with h
  cases Option.some.inj ht
  exact h
lemma update_bounded (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ)
    (s : Option (State n)) (a : Sampling.Action D M E J) (t : State n)
    (ht : update δ D F S Δ P κ m M E J s a=some t) : t.Bounded m := by
  cases s with
  | none=>simp only [update] at ht;contradiction
  | some s=>
    simp only [update] at ht
    split_ifs at ht
    rcases a with u | (w | ⟨w,e⟩)
    · contradiction
    · dsimp only at ht
      split_ifs at ht
      exact retain_bounded m _ t ht
    · dsimp only at ht
      cases he : menuRadius δ D P κ m M E J s w e with
      | none=>simp only [he] at ht;contradiction
      | some R=>
        simp only [he] at ht
        split_ifs at ht
        exact retain_bounded m _ t ht
lemma fold_height (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J H K : ℕ)
    (hd : ∀ i j,Height (δ i j) H) (hP : Height P H) (hκ : Height κ H)
    (hn : n≤H) (hm : m≤H) (hM : M≤H) (hE : E≤H) (hJ : J≤H)
    (as : List (Sampling.Action D M E J)) (s : Option (State n))
    (hs : ∀ z,s=some z→z.Height K) (t : State n)
    (ht : as.foldl (update δ D F S Δ P κ m M E J) s=some t) : t.Height (K+as.length*heightIncrement H) := by
  induction as generalizing K s with
  | nil=>simpa only [List.length_nil,Nat.zero_mul,Nat.add_zero] using hs t ht
  | cons a as ih=>
    rw [List.foldl_cons] at ht
    have hh : ∀ z,update δ D F S Δ P κ m M E J s a=some z→z.Height (K+heightIncrement H) := by
      intro z hz
      cases s with
      | none=>simp [update] at hz
      | some s=>exact update_height δ D F S Δ P κ m M E J H K hd hP hκ hn hm hM hE hJ s z (hs s rfl) a hz
    have hh2 := ih (K+heightIncrement H) _ hh ht
    convert hh2 using 1
    simp only [List.length_cons];ring
lemma fold_bounded (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ)
    (as : List (Sampling.Action D M E J)) (s : Option (State n))
    (hs : ∀ z,s=some z→z.Bounded m) (t : State n)
    (ht : as.foldl (update δ D F S Δ P κ m M E J) s=some t) : t.Bounded m := by
  induction as generalizing s with
  | nil=>exact hs t ht
  | cons a as ih=>exact ih _ (fun z hz=>update_bounded δ D F S Δ P κ m M E J s a z hz) ht
end MetricKMedianRecovery.RationalSampling
namespace MetricKMedianRecovery.BitMachine.BinarySamplingState
open WordOperations WordList RationalHeight
variable {n : ℕ}
lemma finset_length (D : Finset (Fin n)) : (BinaryFinSet.encode D).length ≤ n*(2*n+2) := by
  rw [BinaryFinSet.encode_eq]
  apply (encode_le_bound _ n ?_).trans
  · simp only [List.length_map,Finset.length_sort]
    exact Nat.mul_le_mul_right _ ((Finset.card_le_univ D).trans_eq (Fintype.card_fin n))
  · intro w hw
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp hw
    exact (Indices.bits_length_le i.val).trans (Nat.le_of_lt i.isLt)
lemma leaf_length (z : Fin n×ℚ) (K : ℕ) (hz : Height z.2 K) : (BinarySamplingReference.leafBits z.1 z.2).length ≤ 2*n+3*K+7 := by
  have hn:=(Indices.bits_length_le z.1.val).trans (Nat.le_of_lt z.1.isLt)
  have hq:=BinaryRational.encode_height hz
  simp only [BinarySamplingReference.leafBits,pairBits_length]
  omega
lemma leaves_length (s : RationalSampling.State n) (m K : ℕ) (hs : s.Height K) (hm : s.leaves.length ≤ m) :
    (BinaryNearestLeaf.leavesBits s.leaves).length ≤ m*(4*n+6*K+16) := by
  unfold BinaryNearestLeaf.leavesBits
  apply (encode_le_bound _ (2*n+3*K+7) ?_).trans
  · simp only [List.length_map]
    rw [show 2*(2*n+3*K+7)+2=4*n+6*K+16 by ring]
    exact Nat.mul_le_mul_right _ hm
  · intro w hw
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hw
    exact leaf_length z K (hs z hz)
lemma encode_length (s : RationalSampling.State n) (m K : ℕ) (hs : s.Height K) (hm : s.leaves.length ≤ m) :
    (encode s).length ≤ 2*n*(2*n+2)+m*(4*n+6*K+16)+1 := by
  have ht:=finset_length s.deleted
  have hl:=leaves_length s m K hs hm
  simp only [encode,pairBits_length]
  nlinarith
lemma option_length (s : Option (RationalSampling.State n)) (m K : ℕ)
    (hs : ∀ z,s=some z→z.Height K) (hm : ∀ z,s=some z→z.leaves.length ≤ m) :
    (optionBits s).length ≤ 4*n*(2*n+2)+2*m*(4*n+6*K+16)+4 := by
  cases s with
  | none=>simp [optionBits,WordList.encode]
  | some s=>
    have hh:=encode_length s m K (hs s rfl) (hm s rfl)
    simp only [optionBits,Option.toList_some,List.map_cons,List.map_nil,WordList.encode,length_cons,List.length_nil]
    nlinarith
end MetricKMedianRecovery.BitMachine.BinarySamplingState

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
noncomputable def next (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ)
    (s : Option (State n)) (seed : Fin b→Bool) : Option (State n) :=
  update δ D F S Δ P κ m M E J s (Dyadic.Canonical.draw
    (fun a=>(transitionWeight δ D S Δ M E J s a:ℝ)) b (Sum.inl ()) (actions D M E J) seed)
lemma next_height (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b H K : ℕ)
    (hd : ∀ i j,RationalHeight.Height (δ i j) H) (hP : RationalHeight.Height P H) (hκ : RationalHeight.Height κ H)
    (hn : n≤H) (hm : m≤H) (hM : M≤H) (hE : E≤H) (hJ : J≤H)
    (s : Option (State n)) (hs : ∀ z,s=some z→z.Height K) (seed : Fin b→Bool) (t : State n)
    (ht : next δ D F S Δ P κ m M E J b s seed=some t) : t.Height (K+heightIncrement H) := by
  unfold next at ht
  cases s with
  | none=>simp [update] at ht
  | some s=>exact update_height δ D F S Δ P κ m M E J H K hd hP hκ hn hm hM hE hJ s t (hs s rfl) _ ht
lemma fold_next_height (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b H K : ℕ)
    (hd : ∀ i j,RationalHeight.Height (δ i j) H) (hP : RationalHeight.Height P H) (hκ : RationalHeight.Height κ H)
    (hn : n≤H) (hm : m≤H) (hM : M≤H) (hE : E≤H) (hJ : J≤H)
    (seeds : List (Fin b→Bool)) (s : Option (State n)) (hs : ∀ z,s=some z→z.Height K) (t : State n)
    (ht : seeds.foldl (next δ D F S Δ P κ m M E J b) s=some t) : t.Height (K+seeds.length*heightIncrement H) := by
  induction seeds generalizing K s with
  | nil=>simpa only [List.length_nil,Nat.zero_mul,Nat.add_zero] using hs t ht
  | cons seed seeds ih=>
    rw [List.foldl_cons] at ht
    have hh := ih (K+heightIncrement H) _ (fun z hz=>next_height δ D F S Δ P κ m M E J b H K hd hP hκ hn hm hM hE hJ s hs seed z hz) ht
    convert hh using 1
    simp only [List.length_cons];ring
lemma fold_next_bounded (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ)
    (seeds : List (Fin b→Bool)) (s : Option (State n)) (hs : ∀ z,s=some z→z.Bounded m) (t : State n)
    (ht : seeds.foldl (next δ D F S Δ P κ m M E J b) s=some t) : t.Bounded m := by
  induction seeds generalizing s with
  | nil=>exact hs t ht
  | cons seed seeds ih=>exact ih _ (fun z hz=>update_bounded δ D F S Δ P κ m M E J s _ z hz) ht
end MetricKMedianRecovery.RationalSampling
namespace MetricKMedianRecovery.BitMachine.BinarySampler.Loop
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] Update.run Draw.run
variable {n : ℕ}

def context (cfg : List Bool) (b : ℕ) : List Bool := pairBits (cfg,List.replicate b true)
noncomputable def input (x : List Bool) : List Bool := pairBits (extractPrefix (extractPrefix x),discardPrefix (discardPrefix x))
noncomputable def input_computes : PolyComputes input := (extractPrefix_computes.comp extractPrefix_computes).pair
  (discardPrefix_computes.comp discardPrefix_computes)
noncomputable def drawInput (x : List Bool) : List Bool := encode [extractPrefix (extractPrefix x),discardPrefix (discardPrefix x),
  discardPrefix (extractPrefix x),extractPrefix (discardPrefix x)]
noncomputable def drawInput_computes : PolyComputes drawInput := cons_computes (extractPrefix_computes.comp extractPrefix_computes)
  (cons_computes (discardPrefix_computes.comp discardPrefix_computes)
    (cons_computes (extractPrefix_computes.comp discardPrefix_computes)
      (cons_computes (discardPrefix_computes.comp extractPrefix_computes) (const_computes []))))
noncomputable def step (x : List Bool) : List Bool := Update.run (pairBits (input x,Draw.run (drawInput x)))
noncomputable def step_computes : PolyComputes step := (input_computes.pair (drawInput_computes.comp Draw.run_computes)).comp Update.run_computes
lemma step_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ)
    (s : Option (RationalSampling.State n)) (seed : Fin b→Bool) :
    step (pairBits (context (config δ D F S Δ P κ m M E J) b,pairBits (List.ofFn seed,BinarySamplingState.optionBits s)))=
      BinarySamplingState.optionBits (RationalSampling.next δ D F S Δ P κ m M E J b s seed) := by
  simp only [step,input,drawInput,context,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [show encode [config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits s,List.replicate b true,List.ofFn seed]=
    Draw.pack (config δ D F S Δ P κ m M E J) s b (List.ofFn seed) from rfl,Draw.run_pack,Update.run_pair]
  rfl
end MetricKMedianRecovery.BitMachine.BinarySampler.Loop

end OAI
