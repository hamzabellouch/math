import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinKernel
import OAI.Probability.InvariantIsing.Fields.VectorTransitionEntropy

namespace OAI

/-! The actual spin law obtained by successively sampling the constrained
Gaussian recursion and then its terminal Gibbs measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal ENNReal

namespace InvariantIsing

def restrictedTailSpinKernel {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty) :
    (n : ℕ) → (b : ℕ → ℝ) → (v : ℕ → ℝ≥0) → (∀ i < n, 0 < b i) →
      Kernel (Fin N → ℝ) (Spin N)
  | 0, _, _, _ => restrictedSpinKernel S
  | n + 1, b, v, hb =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    let hbs := fun i hi => hb (i + 1) (by omega)
    let hreg := restrictedFieldRecursion_regular hN S hS n bs vs hbs
    restrictedTailSpinKernel hN S hS n bs vs hbs ∘ₖ
      vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion S n bs vs) hreg.1

instance restrictedTailSpinKernel_markov {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) : IsMarkovKernel (restrictedTailSpinKernel hN S hS n b v hb) := by
  induction n generalizing b v with
  | zero => exact restrictedSpinKernel_markov S hS
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    let _ := ih bs vs hbs
    change IsMarkovKernel (_ ∘ₖ _)
    infer_instance

end InvariantIsing

end

end OAI
