import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.RecoveryTape

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryBranchTape Completion FiniteSampling
variable {n m H : ℕ}
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
  (s : RationalSampling.State n) (hn : n≤H) (hm : m≤H) (hH : 1≤H)
  (hp : s.leaves.length≤H) (r0 y0 : Fin n) (seed : Fin (tapeSize H)→Bool)
noncomputable def positive (q c : Fin (n+1)) (b : Fin m) : Finset (Fin n) :=
  let z:=positiveSeed hn hm hp b seed
  BinaryObservableBranch.output δ D F S Δ s (fun i=>ColorLabel.color (z.1.1 i))
    (fun i=>ColorLabel.label (b.val+1) (by omega) (z.1.2 i)) q.val c.val r0 y0 z.2
noncomputable def zero (q : Fin (n+1)) : Finset (Fin n) :=
  let z:=zeroSeed hn hH hp seed
  BinaryZeroBranch.output δ D F S Δ s (fun i=>ColorLabel.color (z.1 i)) q.val z.2
noncomputable def candidates : List (Finset (Fin n)) :=
  List.ofFn (zero δ D F S Δ s hn hH hp seed) ++
    (List.ofFn (fun q:Fin (n+1)=>q)).flatMap (fun q=>(List.ofFn (fun c:Fin (n+1)=>c)).flatMap
      (fun c=>List.ofFn (fun b:Fin m=>positive δ D F S Δ s hn hm hp r0 y0 seed q c b)))
noncomputable def result : Finset (Fin n) :=
  BinaryMetricBest.best δ D S (candidates δ D F S Δ s hn hm hH hp r0 y0 seed)
lemma zero_mem (q : Fin (n+1)) : zero δ D F S Δ s hn hH hp seed q∈candidates δ D F S Δ s hn hm hH hp r0 y0 seed := by
  exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨q,rfl⟩)
lemma positive_mem (q c : Fin (n+1)) (b : Fin m) : positive δ D F S Δ s hn hm hp r0 y0 seed q c b∈candidates δ D F S Δ s hn hm hH hp r0 y0 seed := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨q,List.mem_ofFn.mpr ⟨q,rfl⟩,
    List.mem_flatMap.mpr ⟨c,List.mem_ofFn.mpr ⟨c,rfl⟩,List.mem_ofFn.mpr ⟨b,rfl⟩⟩⟩
lemma candidates_property (P : Finset (Fin n)→Prop)
    (hz : ∀ q,P (zero δ D F S Δ s hn hH hp seed q))
    (hb : ∀ q c b,P (positive δ D F S Δ s hn hm hp r0 y0 seed q c b)) :
    ∀ U∈candidates δ D F S Δ s hn hm hH hp r0 y0 seed,P U := by
  intro U hU
  rcases List.mem_append.mp hU with hz'|hb'
  · obtain ⟨q,rfl⟩:=List.mem_ofFn.mp hz'
    exact hz q
  · obtain ⟨q,_,hq⟩:=List.mem_flatMap.mp hb'
    obtain ⟨c,_,hc⟩:=List.mem_flatMap.mp hq
    obtain ⟨b,rfl⟩:=List.mem_ofFn.mp hc
    exact hb q c b
lemma result_property (P : Finset (Fin n)→Prop) (hS : P S)
    (hz : ∀ q,P (zero δ D F S Δ s hn hH hp seed q))
    (hb : ∀ q c b,P (positive δ D F S Δ s hn hm hp r0 y0 seed q c b)) :
    P (result δ D F S Δ s hn hm hH hp r0 y0 seed) :=
  BinaryMetricBest.best_property δ D S _ P hS (candidates_property δ D F S Δ s hn hm hH hp r0 y0 seed P hz hb)
lemma run_source (A : ℝ) : ∃ d : ℕ, ∀ {n m H : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (extra : List Bool)
    (r0 y0 : Fin n) (N : ℕ), N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) →
    (hn : n≤H) → (hm : m≤H) → (hH : 1≤H) → (hp : s.leaves.length≤H) →
    ∀ (seed : Fin (tapeSize H)→Bool),
    run d (pack δ D F S Δ s m extra (List.ofFn seed))=
      BinaryFinSet.encode (result δ D F S Δ s hn hm hH hp r0 y0 seed) := by
  obtain ⟨d,hd⟩:=atBranch_source A
  refine ⟨d,?_⟩
  intro n m H δ D F S Δ s extra r0 y0 N hN hlog hn hm hH hp seed
  apply run_of_candidates
  rw [candidateWords_pack]
  unfold candidates
  simp only [List.map_append,List.map_flatMap,List.map_ofFn,Function.comp_def]
  congr 2
  · apply congrArg List.ofFn
    funext q
    exact atZero_pack δ D F S Δ s m extra hn hH hp q seed
  · apply List.flatMap_congr
    intro q _
    apply List.flatMap_congr
    intro c _
    congr 1
    funext b
    exact hd δ D F S Δ s extra r0 y0 N hN hlog hn hm hp q c b seed
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
