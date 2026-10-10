import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RecoveryEnumeration
import OAI.Combinatorics.KMedianRecovery.Branching.BranchTapeBound

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryBranchTape
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] atBranch atZero context zeroContext
  BinaryRandomizedBranch.Prefix.run BinaryRandomizedZeroBranch.Prefix.run
  BinaryObservableBranch.output BinaryZeroBranch.output ColorLabel.label ColorLabel.color
  BinaryBranchTape.layout BinaryRandomizedZeroBranch.layout
def tapeSize (H : ℕ) : ℕ := 201326592000000015*(H+2)^12
def positiveSeed {n m p H : ℕ} (hn : n≤H) (hm : m≤H) (hp : p≤H) (b : Fin m)
    (seed : Fin (tapeSize H)→Bool) : BinaryBranchTape.Seed n (b.val+1) p :=
  BinaryBranchTape.layout n (b.val+1) p (fun i=>seed (Fin.castLE
    (BinaryBranchTape.count_bound hn ((Nat.succ_le_of_lt b.isLt).trans hm) hp) i))
lemma zeroCount_bound {n p H : ℕ} (hn : n≤H) (hH : 1≤H) (hp : p≤H) :
    BinaryRandomizedZeroBranch.count n p≤tapeSize H := by
  simpa only [tapeSize,BinaryRandomizedZeroBranch.count,count,labelCount,Nat.clog_one_right,Nat.mul_zero,Nat.add_zero]
    using BinaryBranchTape.count_bound hn hH hp
def zeroSeed {n p H : ℕ} (hn : n≤H) (hH : 1≤H) (hp : p≤H)
    (seed : Fin (tapeSize H)→Bool) : BinaryRandomizedZeroBranch.Seed n p :=
  BinaryRandomizedZeroBranch.layout n p (fun i=>seed (Fin.castLE (zeroCount_bound hn hH hp) i))
lemma atBranch_context {n m : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (extra raw : List Bool)
    (d : ℕ) (q c : Fin (n+1)) (b : Fin m) :
    atBranch d (pairBits (pack δ D F S Δ s m extra raw,choiceBits q.val c.val b.val))=
      BinaryRandomizedBranch.Prefix.run d (pairBits
        (BinaryBranchContext.pack δ D F S Δ s (fun _=>0) (fun _=>(0:Fin (b.val+1))) q.val c.val extra,raw)) := by
  rw [atBranch,context_pack δ D F S Δ s m extra raw q.val c.val b.val (by omega) (by omega)]
  congr 1
  simp only [src,Function.comp_apply,extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma atBranch_source (A : ℝ) : ∃ d : ℕ, ∀ {n m H : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (extra : List Bool)
    (r0 y0 : Fin n) (N : ℕ), N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) →
    (hn : n≤H) → (hm : m≤H) → (hp : s.leaves.length≤H) →
    ∀ (q c : Fin (n+1)) (b : Fin m) (seed : Fin (tapeSize H)→Bool),
    atBranch d (pairBits (pack δ D F S Δ s m extra (List.ofFn seed),choiceBits q.val c.val b.val))=
      let seed':=positiveSeed hn hm hp b seed
      BinaryFinSet.encode (BinaryObservableBranch.output δ D F S Δ s (fun i=>ColorLabel.color (seed'.1.1 i))
        (fun i=>ColorLabel.label (b.val+1) (by omega) (seed'.1.2 i)) q.val c.val r0 y0 seed'.2) := by
  obtain ⟨d,hd⟩:=BinaryRandomizedBranch.Prefix.source_run A
  refine ⟨d,?_⟩
  intro n m H δ D F S Δ s extra r0 y0 N hN hlog hn hm hp q c b seed
  have hblog : ((b.val+1:ℕ):ℝ)≤A*Real.log ((N:ℝ)+2) :=
    (by exact_mod_cast Nat.succ_le_of_lt b.isLt : ((b.val+1:ℕ):ℝ)≤ m).trans hlog
  rw [atBranch_context]
  simpa only [positiveSeed] using hd (b:=b.val+1) (K:=tapeSize H) δ D F S Δ s
    (fun _=>(0:Fin 3)) (fun _=>(0:Fin (b.val+1))) q.val c.val extra r0 y0 N hN hblog (by omega)
    (BinaryBranchTape.count_bound hn ((Nat.succ_le_of_lt b.isLt).trans hm) hp) seed

lemma atZero_context {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
    (s : RationalSampling.State n) (m : ℕ) (extra raw : List Bool) (q : ℕ) :
    atZero (pairBits (pack δ D F S Δ s m extra raw,q.bits))=
      BinaryRandomizedZeroBranch.Prefix.run (pairBits (BinaryZeroBranch.pack δ D F S Δ s (fun _=>0) q extra,raw)) := by
  rw [atZero]
  have hpro : promote (pairBits (pack δ D F S Δ s m extra raw,q.bits))=
      pairBits (pack δ D F S Δ s m extra raw,choiceBits q 0 0) := by
    simp only [promote,extractPrefix_pairBits,discardPrefix_pairBits,choiceBits,Nat.zero_bits]
  rw [hpro,zeroContext_pack]
  congr 1
  simp only [src,Function.comp_apply,extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma atZero_pack {n H : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
    (s : RationalSampling.State n) (m : ℕ) (extra : List Bool) (hn : n≤H) (hH : 1≤H)
    (hp : s.leaves.length≤H) (q : Fin (n+1)) (seed : Fin (tapeSize H)→Bool) :
    atZero (pairBits (pack δ D F S Δ s m extra (List.ofFn seed),q.val.bits))=
      let seed':=zeroSeed hn hH hp seed
      BinaryFinSet.encode (BinaryZeroBranch.output δ D F S Δ s (fun i=>ColorLabel.color (seed'.1 i)) q.val seed'.2) := by
  rw [atZero_context]
  simpa only [zeroSeed] using BinaryRandomizedZeroBranch.Prefix.run_pack δ D F S Δ s
    (fun _=>(0:Fin 3)) q.val extra (zeroCount_bound hn hH hp) seed
lemma positiveSeed_probability {n m p H : ℕ} (hn : n≤H) (hm : m≤H) (hp : p≤H) (b : Fin m)
    (E : BinaryBranchTape.Seed n (b.val+1) p→Prop) :
    FiniteSampling.probability (fun seed:Fin (tapeSize H)→Bool=>E (positiveSeed hn hm hp b seed))=FiniteSampling.probability E :=
  BinaryRandomizedBranch.Prefix.probability_layout (BinaryBranchTape.count_bound hn ((Nat.succ_le_of_lt b.isLt).trans hm) hp) E
lemma zeroSeed_probability {n p H : ℕ} (hn : n≤H) (hH : 1≤H) (hp : p≤H)
    (E : BinaryRandomizedZeroBranch.Seed n p→Prop) :
    FiniteSampling.probability (fun seed:Fin (tapeSize H)→Bool=>E (zeroSeed hn hH hp seed))=FiniteSampling.probability E :=
  BinaryRandomizedZeroBranch.Prefix.probability_layout (zeroCount_bound hn hH hp) E
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
