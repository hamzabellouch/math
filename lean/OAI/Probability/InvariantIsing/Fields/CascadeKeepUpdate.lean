import OAI.Probability.IsingPerceptron.NoiseTreeKeep

namespace OAI

/-! A finite tree uses only the updates before its depth. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

lemma noiseTreeKeep_update_congr {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (c : ℕ → S × A → ℝ) (u u' : ℕ → S × A → S)
    (hu : ∀ i < n, u i = u' i) (s : S) (T : NoiseTree A n) :
    noiseTreeKeep n b μ c u s T = noiseTreeKeep n b μ c u' s T := by
  induction n generalizing b μ c u u' s with
  | zero => rfl
  | succ n ih =>
    unfold noiseTreeKeep
    congr 1
    funext p
    apply congrArg (fun V => (c 0 (s,p.2.1)*p.1,(p.2.1,V)))
    rw [hu 0 (by omega)]
    exact ih _ _ _ _ _ (fun i hi => hu (i+1) (by omega)) _ _

end InvariantIsing

end

end OAI
