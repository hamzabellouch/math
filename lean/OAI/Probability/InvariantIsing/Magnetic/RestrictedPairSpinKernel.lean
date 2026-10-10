import OAI.Probability.InvariantIsing.Magnetic.RestrictedTailEntropy
import OAI.Probability.InvariantIsing.Core.KernelProductEntropy

namespace OAI

/-! Two constrained spins sampled independently after a prescribed common
Gaussian prefix. The common prefix is retained in the actual kernel law. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal ENNReal

namespace InvariantIsing

def restrictedPairSpinKernel {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty) :
    (n : ℕ) → (b : ℕ → ℝ) → (v : ℕ → ℝ≥0) → (∀ i < n, 0 < b i) → Fin (n + 1) →
      Kernel (Fin N → ℝ) (Spin N × Spin N)
  | 0, _, _, _, _ => restrictedSpinKernel S ×ₖ restrictedSpinKernel S
  | n + 1, b, v, hb, i =>
    let bs := fun j => b (j + 1)
    let vs := fun j => v (j + 1)
    let hbs := fun j hj => hb (j + 1) (by omega)
    let hreg := restrictedFieldRecursion_regular hN S hS n bs vs hbs
    Fin.cases (restrictedTailSpinKernel hN S hS (n + 1) b v hb ×ₖ
        restrictedTailSpinKernel hN S hS (n + 1) b v hb)
      (fun j => restrictedPairSpinKernel hN S hS n bs vs hbs j ∘ₖ
        vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion S n bs vs) hreg.1) i

instance restrictedPairSpinKernel_markov {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (i : Fin (n + 1)) :
    IsMarkovKernel (restrictedPairSpinKernel hN S hS n b v hb i) := by
  induction n generalizing b v with
  | zero =>
    let _ := restrictedSpinKernel_markov S hS
    change IsMarkovKernel (restrictedSpinKernel S ×ₖ restrictedSpinKernel S)
    infer_instance
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change IsMarkovKernel (_ ×ₖ _)
      infer_instance
    · let bs := fun j => b (j + 1)
      let vs := fun j => v (j + 1)
      have hbs : ∀ j < n, 0 < bs j := fun j hj => hb (j + 1) (by omega)
      let _ := ih bs vs hbs j
      change IsMarkovKernel (_ ∘ₖ _)
      infer_instance

end InvariantIsing

end

end OAI
