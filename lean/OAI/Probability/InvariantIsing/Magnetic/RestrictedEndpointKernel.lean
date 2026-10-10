import OAI.Probability.InvariantIsing.Magnetic.RestrictedPairSpinKernel
import Mathlib.Probability.Kernel.Composition.KernelLemmas

namespace OAI

/-! Actual constrained Gaussian endpoint kernels. Sampling terminal
constrained spins commutes with the shared-prefix construction. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def restrictedTailEndpointKernel {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty) :
    (n : ℕ) → (b : ℕ → ℝ) → (v : ℕ → ℝ≥0) → (∀ i < n, 0 < b i) →
      Kernel (Fin N → ℝ) (Fin N → ℝ)
  | 0, _, _, _ => Kernel.id
  | n + 1, b, v, hb =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    let hbs := fun i hi => hb (i + 1) (by omega)
    let hreg := restrictedFieldRecursion_regular hN S hS n bs vs hbs
    restrictedTailEndpointKernel hN S hS n bs vs hbs ∘ₖ
      vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion S n bs vs) hreg.1

instance restrictedTailEndpointKernel_markov {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) : IsMarkovKernel (restrictedTailEndpointKernel hN S hS n b v hb) := by
  induction n generalizing b v with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    let _ := ih bs vs hbs
    change IsMarkovKernel (_ ∘ₖ _)
    infer_instance

lemma restrictedTailSpinKernel_endpoint {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) :
    restrictedTailSpinKernel hN S hS n b v hb =
      restrictedSpinKernel S ∘ₖ restrictedTailEndpointKernel hN S hS n b v hb := by
  let _ := restrictedSpinKernel_markov S hS
  induction n generalizing b v with
  | zero => simp only [restrictedTailSpinKernel, restrictedTailEndpointKernel, Kernel.comp_id]
  | succ n ih =>
    simp only [restrictedTailSpinKernel, restrictedTailEndpointKernel]
    rw [ih, Kernel.comp_assoc]

def restrictedPairEndpointKernel {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty) :
    (n : ℕ) → (b : ℕ → ℝ) → (v : ℕ → ℝ≥0) → (∀ i < n, 0 < b i) → Fin (n + 1) →
      Kernel (Fin N → ℝ) ((Fin N → ℝ) × (Fin N → ℝ))
  | 0, _, _, _, _ => Kernel.id ×ₖ Kernel.id
  | n + 1, b, v, hb, i =>
    let bs := fun j => b (j + 1)
    let vs := fun j => v (j + 1)
    let hbs := fun j hj => hb (j + 1) (by omega)
    let hreg := restrictedFieldRecursion_regular hN S hS n bs vs hbs
    Fin.cases (restrictedTailEndpointKernel hN S hS (n + 1) b v hb ×ₖ
        restrictedTailEndpointKernel hN S hS (n + 1) b v hb)
      (fun j => restrictedPairEndpointKernel hN S hS n bs vs hbs j ∘ₖ
        vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion S n bs vs) hreg.1) i

instance restrictedPairEndpointKernel_markov {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (i : Fin (n + 1)) :
    IsMarkovKernel (restrictedPairEndpointKernel hN S hS n b v hb i) := by
  induction n generalizing b v with
  | zero => change IsMarkovKernel (Kernel.id ×ₖ Kernel.id); infer_instance
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

lemma restrictedPairSpinKernel_endpoint {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (i : Fin (n + 1)) :
    restrictedPairSpinKernel hN S hS n b v hb i =
      (restrictedSpinKernel S ∥ₖ restrictedSpinKernel S) ∘ₖ
        restrictedPairEndpointKernel hN S hS n b v hb i := by
  let _ := restrictedSpinKernel_markov S hS
  induction n generalizing b v with
  | zero =>
    simp only [restrictedPairSpinKernel, restrictedPairEndpointKernel,
      Kernel.parallelComp_comp_prod, Kernel.comp_id]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [restrictedPairSpinKernel, restrictedPairEndpointKernel, Fin.cases_zero,
        Kernel.parallelComp_comp_prod, restrictedTailSpinKernel_endpoint]
    · simp only [restrictedPairSpinKernel, restrictedPairEndpointKernel, Fin.cases_succ]
      rw [ih, Kernel.comp_assoc]

end InvariantIsing

end

end OAI
