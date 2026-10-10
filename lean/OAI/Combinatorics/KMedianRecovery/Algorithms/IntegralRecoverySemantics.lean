import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralRecoveryMachine
import OAI.Combinatorics.KMedianRecovery.Recovery.RecoveryCandidates

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open WordOperations WordList Sampling.Comparison
variable {n : ℕ}
noncomputable def stateAt (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (seed : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool) (i : Fin (2*m+1)) :
    Option (RationalSampling.State n) :=
  ((List.ofFn seed).take i.val).foldl
    (RationalSampling.next δ D F S Δ P (1/1000000) m BinarySampler.Parameters.M BinarySampler.Parameters.E
      (RadiusMenus.thirdSize mainKappa m) (integralPrecision D (Δ:ℝ) m)) (some RationalSampling.State.initial)
lemma stateAt_bounded (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (seed : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool) (i : Fin (2*m+1))
    (s : RationalSampling.State n) (hs : stateAt δ D F S Δ P m seed i=some s) : s.Bounded m := by
  apply RationalSampling.fold_next_bounded δ D F S Δ P (1/1000000) m BinarySampler.Parameters.M BinarySampler.Parameters.E
    (RadiusMenus.thirdSize mainKappa m) (integralPrecision D (Δ:ℝ) m) _ _ _ s hs
  intro z hz
  cases Option.some.inj hz
  simp [RationalSampling.State.Bounded,RationalSampling.State.initial]
noncomputable def optionOutput (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (m : ℕ) (hm : m≤n)
    (r0 y0 : Fin n) (seed : Fin (BinaryRecovery.tapeSize (n+1))→Bool) (w : Option (RationalSampling.State n)) :
    Finset (Fin n) :=
  w.elim S (fun s=>if hp:s.leaves.length≤n+1 then
    BinaryRecovery.result δ D F S Δ s (Nat.le_succ n) (hm.trans (Nat.le_succ n)) (by omega) hp r0 y0 seed else S)
lemma optionOutput_none (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (m : ℕ) (hm : m≤n)
    (r0 y0 : Fin n) (seed : Fin (BinaryRecovery.tapeSize (n+1))→Bool) :
    optionOutput δ D F S Δ m hm r0 y0 seed none=S := rfl
lemma optionOutput_some (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (m : ℕ) (hm : m≤n)
    (r0 y0 : Fin n) (seed : Fin (BinaryRecovery.tapeSize (n+1))→Bool) (s : RationalSampling.State n)
    (hp : s.leaves.length≤n+1) : optionOutput δ D F S Δ m hm r0 y0 seed (some s)=
      BinaryRecovery.result δ D F S Δ s (Nat.le_succ n) (hm.trans (Nat.le_succ n)) (by omega) hp r0 y0 seed := by
  simp only [optionOutput,Option.elim_some,dite_eq_left hp]
noncomputable def candidates (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) (hm : m≤n)
    (r0 y0 : Fin n) (sample : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool)
    (complete : Fin (BinaryRecovery.tapeSize (n+1))→Bool) : List (Finset (Fin n)) :=
  List.ofFn (fun i=>optionOutput δ D F S Δ m hm r0 y0 complete (stateAt δ D F S Δ P m sample i))
noncomputable def result (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) (hm : m≤n)
    (r0 y0 : Fin n) (sample : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool)
    (complete : Fin (BinaryRecovery.tapeSize (n+1))→Bool) : Finset (Fin n) :=
  BinaryMetricBest.best δ D S (candidates δ D F S Δ P m hm r0 y0 sample complete)
lemma run_source (A : ℝ) : ∃ d : ℕ, ∀ {n : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) (hm : m≤n),
    Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16) → ∀ (extra : List Bool) (N : ℕ),
    N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) → ∀ (r0 y0 : Fin n)
    (sample : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool)
    (complete : Fin (BinaryRecovery.tapeSize (n+1))→Bool),
    run d (pack δ D F S Δ P m extra sample (List.ofFn complete))=
      BinaryFinSet.encode (result δ D F S Δ P m hm r0 y0 sample complete) := by
  obtain ⟨d,hd⟩:=BinaryRecovery.run_source A
  refine ⟨d,?_⟩
  intro n δ D F S Δ P m hm hΔ extra N hN hlog r0 y0 sample complete
  have hc : candidateWords d (pack δ D F S Δ P m extra sample (List.ofFn complete))=
      encode ((candidates δ D F S Δ P m hm r0 y0 sample complete).map BinaryFinSet.encode) := by
    rw [candidateWords,recoveryContext_pack δ D F S Δ P m extra sample _ hm hΔ,
      sampleContext_pack δ D F S Δ P m extra _ sample hm hΔ,BinarySampler.Trace.run_pack,mapWith_ofFn]
    simp only [candidates,List.map_ofFn,Function.comp_def]
    apply congrArg encode
    apply congrArg List.ofFn
    funext i
    change BinaryRecovery.atOption d (pairBits (BinaryRecovery.pack δ D F S (Δ:ℚ) RationalSampling.State.initial m extra
      (List.ofFn complete),BinarySamplingState.optionBits (stateAt δ D F S Δ P m sample i)))=_
    cases hs : stateAt δ D F S Δ P m sample i with
    | none=>rw [BinaryRecovery.atOption_none,optionOutput_none]
    | some s=>
      have hp : s.leaves.length≤n+1 := ((stateAt_bounded δ D F S Δ P m sample i s hs).1.trans hm).trans (Nat.le_succ n)
      rw [BinaryRecovery.atOption_some,optionOutput_some δ D F S Δ m hm r0 y0 complete s hp]
      exact hd δ D F S Δ s extra r0 y0 N hN hlog (Nat.le_succ n) (hm.trans (Nat.le_succ n)) (by omega) hp complete
  rw [run,metricContext_pack,start_pack,hc]
  exact BinaryMetricBest.run_pack δ D S _
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
