import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.PolynomialProduct
import OAI.Combinatorics.KMedianRecovery.Strictness.RestrictBits

namespace OAI

namespace MetricKMedianRecovery.GlobalAssembly
open FiniteSampling

theorem global_polynomial_fair_experiment : ∃ σ : ℝ, 0 < σ ∧
    ∀ a : ℝ, 0 < a → ∃ P : Polynomial ℕ,
    ∃ out : (I : RationalMetricInput) → (Fin (P.eval I.bits.length) → Bool) → Finset (Fin I.pointCount),
      (∀ (I : RationalMetricInput) bits, I.Feasible (out I bits) ∧ (I.cost (out I bits):ℝ) ≤ 6*(I.optimum:ℝ)) ∧
      (∀ I : RationalMetricInput, 1-Real.rpow ((I.size:ℝ)+2) (-a) ≤
        probability (fun bits => (I.cost (out I bits):ℝ) ≤ (2-σ)*(I.optimum:ℝ))) ∧
      (∀ I : RationalMetricInput, average (fun bits => (I.cost (out I bits):ℝ)) ≤ (2-σ)*(I.optimum:ℝ)) := by
  classical
  obtain ⟨v,hv,Nstar,_hNstar,c,hc,H⟩ := global_semantic_fair_experiment
  refine ⟨IntegralAssembly.gamma/4,absolute_gap_pos,?_⟩
  intro a ha
  obtain ⟨P,hP⟩ := bitCount_polynomial v Nstar c a hv hc.le
  let f (I : RationalMetricInput) := Classical.choose (H a ha I)
  have hf (I : RationalMetricInput) := Classical.choose_spec (H a ha I)
  let out (I : RationalMetricInput) (bits : Fin (P.eval I.bits.length) → Bool) :=
    f I (restrictBits (hP I) bits)
  refine ⟨P,out,?_,?_,?_⟩
  · intro I bits
    exact (hf I).1 _
  · intro I
    change _ ≤ probability (fun bits => (I.cost (f I (restrictBits (hP I) bits)):ℝ) ≤ _)
    rw [probability_restrictBits (hP I) (fun bits => (I.cost (f I bits):ℝ) ≤
      (2-IntegralAssembly.gamma/4)*(I.optimum:ℝ))]
    exact (hf I).2.1
  · intro I
    change average (fun bits => (I.cost (f I (restrictBits (hP I) bits)):ℝ)) ≤ _
    rw [average_restrictBits (hP I) (fun bits => (I.cost (f I bits):ℝ))]
    exact (hf I).2.2

end MetricKMedianRecovery.GlobalAssembly

end OAI
