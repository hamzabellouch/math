import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.RandomizedZeroBranch
import OAI.Combinatorics.KMedianRecovery.Sampling.FairPrefix

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.Prefix
open WordOperations BinaryBranchContext
noncomputable def run (d : ℕ) : List Bool→List Bool := BinaryRandomizedBranch.run d ∘ BinaryBranchTape.Count.cut
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) :=
  BinaryBranchTape.Count.cut_computes.comp (BinaryRandomizedBranch.run_computes d)
lemma source_run (A : ℝ) : ∃ d : ℕ, ∀ {n b K : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (colors0 : Fin n→Fin 3)
    (label0 : Fin n→Fin b) (q c : ℕ) (extra : List Bool) (r0 y0 : Fin n) (N : ℕ),
    N≤extra.length → (b:ℝ)≤A*Real.log ((N:ℝ)+2) → (hb0 : 0<b) →
    (hK : BinaryBranchTape.count n b s.leaves.length≤K) → ∀ seed : Fin K→Bool,
    run d (pairBits (pack δ D F S Δ s colors0 label0 q c extra,List.ofFn seed))=
    let seed':=BinaryBranchTape.layout n b s.leaves.length (fun i=>seed (Fin.castLE hK i))
    BinaryFinSet.encode (BinaryObservableBranch.output δ D F S Δ s (fun i=>ColorLabel.color (seed'.1.1 i))
      (fun i=>ColorLabel.label b hb0 (seed'.1.2 i)) q c r0 y0 seed'.2) := by
  obtain ⟨d,hd⟩:=BinaryRandomizedBranch.source_run A
  refine ⟨d,?_⟩
  intro n b K δ D F S Δ s colors0 label0 q c extra r0 y0 N hN hb hb0 hK seed
  rw [run,Function.comp_apply,BinaryBranchTape.Count.cut_pack,FiniteSampling.take_ofFn_cast hK,
    ←BinaryBranchTape.raw_layout]
  exact hd δ D F S Δ s colors0 label0 q c extra r0 y0 N hN hb hb0 _
lemma probability_layout {n b p K : ℕ} (hK : BinaryBranchTape.count n b p≤K)
    (E : BinaryBranchTape.Seed n b p→Prop) :
    FiniteSampling.probability (fun seed:Fin K→Bool=>E (BinaryBranchTape.layout n b p
      (fun i=>seed (Fin.castLE hK i))))=FiniteSampling.probability E := by
  exact (FiniteSampling.probability_prefix hK (fun z=>E (BinaryBranchTape.layout n b p z))).trans
    (BinaryBranchTape.probability_layout n b p E)
end MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.Prefix
namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix
open WordOperations
noncomputable def run : List Bool→List Bool := BinaryRandomizedZeroBranch.run ∘ BinaryBranchTape.Count.cut
noncomputable def run_computes : PolyComputes run :=
  BinaryBranchTape.Count.cut_computes.comp BinaryRandomizedZeroBranch.run_computes
lemma run_pack {n K : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors0 : Fin n→Fin 3) (q : ℕ) (extra : List Bool)
    (hK : BinaryRandomizedZeroBranch.count n s.leaves.length≤K) (seed : Fin K→Bool) :
    run (pairBits (BinaryZeroBranch.pack δ D F S Δ s colors0 q extra,List.ofFn seed))=
      let seed':=BinaryRandomizedZeroBranch.layout n s.leaves.length (fun i=>seed (Fin.castLE hK i))
      BinaryFinSet.encode (BinaryZeroBranch.output δ D F S Δ s (fun i=>ColorLabel.color (seed'.1 i)) q seed'.2) := by
  have hc : BinaryBranchTape.count n 1 s.leaves.length=BinaryRandomizedZeroBranch.count n s.leaves.length := by
    simp only [BinaryBranchTape.count,BinaryBranchTape.labelCount,Nat.clog_one_right,Nat.mul_zero,Nat.add_zero]
  rw [run,Function.comp_apply,BinaryZeroBranch.pack,BinaryBranchTape.Count.cut_pack,hc,
    FiniteSampling.take_ofFn_cast hK,←BinaryRandomizedZeroBranch.raw_layout]
  exact BinaryRandomizedZeroBranch.run_pack δ D F S Δ s colors0 q extra _
lemma probability_layout {n p K : ℕ} (hK : BinaryRandomizedZeroBranch.count n p≤K)
    (E : BinaryRandomizedZeroBranch.Seed n p→Prop) :
    FiniteSampling.probability (fun seed:Fin K→Bool=>E (BinaryRandomizedZeroBranch.layout n p
      (fun i=>seed (Fin.castLE hK i))))=FiniteSampling.probability E := by
  exact (FiniteSampling.probability_prefix hK (fun z=>E (BinaryRandomizedZeroBranch.layout n p z))).trans
    (FiniteSampling.probability_comp_equiv (BinaryRandomizedZeroBranch.layout n p) E)
end MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix

end OAI
