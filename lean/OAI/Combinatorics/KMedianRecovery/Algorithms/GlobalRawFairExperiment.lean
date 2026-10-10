import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.GlobalPolynomialFairExperiment
import OAI.Combinatorics.KMedianRecovery.Recovery.RawRun

namespace OAI

namespace MetricKMedianRecovery.GlobalAssembly
open FiniteSampling

theorem global_raw_fair_experiment : ∃ σ : ℝ, 0 < σ ∧
    ∀ a : ℝ, 0 < a → ∃ P : Polynomial ℕ, ∃ run : List Bool × List Bool → List Bool,
      (∀ (I : RationalMetricInput) (s : Fin (P.eval I.bits.length) → Bool),
        I.Feasible (I.decodeOutput (run (I.bits,List.ofFn s))) ∧
        (I.cost (I.decodeOutput (run (I.bits,List.ofFn s))):ℝ) ≤ 6*(I.optimum:ℝ)) ∧
      (∀ I : RationalMetricInput, 1-Real.rpow ((I.size:ℝ)+2) (-a) ≤
        probability (fun s : Fin (P.eval I.bits.length) → Bool =>
          (I.cost (I.decodeOutput (run (I.bits,List.ofFn s))):ℝ) ≤ (2-σ)*(I.optimum:ℝ))) ∧
      (∀ I : RationalMetricInput, average (fun s : Fin (P.eval I.bits.length) → Bool =>
        (I.cost (I.decodeOutput (run (I.bits,List.ofFn s))):ℝ)) ≤ (2-σ)*(I.optimum:ℝ)) := by
  obtain ⟨σ,hσ,H⟩ := global_polynomial_fair_experiment
  refine ⟨σ,hσ,?_⟩
  intro a ha
  obtain ⟨P,out,hvalid,hprob,hexp⟩ := H a ha
  have hr (I : RationalMetricInput) (s : Fin (P.eval I.bits.length) → Bool) :
      I.decodeOutput (rawRun P out (I.bits,List.ofFn s)) = out I s :=
    rawRun_output P out I s (hvalid I s).1
  refine ⟨P,rawRun P out,?_,?_,?_⟩
  · intro I s
    simpa only [hr] using hvalid I s
  · intro I
    simpa only [hr] using hprob I
  · intro I
    simpa only [hr] using hexp I

end MetricKMedianRecovery.GlobalAssembly

end OAI
