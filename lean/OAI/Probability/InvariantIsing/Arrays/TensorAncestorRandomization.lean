import OAI.Probability.InvariantIsing.Arrays.NSpinTensorAncestorInput
import Mathlib.Probability.Kernel.Representation

namespace OAI

/-! Uniform-seed realizations of the actual tensor ancestor kernels. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem tensorAncestorMarkKernel_seed {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) :
    ∃ ψ : ℕ → (SpinTensorIndex I degree → ℝ) → Set.Icc (0 : ℝ) 1 → (SpinTensorIndex I degree → ℝ),
      (∀ i, Measurable (Function.uncurry (ψ i))) ∧
      ∀ i z, volume.map (ψ i z) =
        tensorAncestorMarkKernel eig U c I degree amplitude n b v i z := by
  have hex i : ∃ ψ : (SpinTensorIndex I degree → ℝ) → Set.Icc (0 : ℝ) 1 → (SpinTensorIndex I degree → ℝ),
      Measurable (Function.uncurry ψ) ∧ ∀ z, volume.map (ψ z) =
        tensorAncestorMarkKernel eig U c I degree amplitude n b v i z := by
    let := tensorAncestorMarkKernel_markov hN eig U c I degree amplitude n b v hb i
    exact (tensorAncestorMarkKernel eig U c I degree amplitude n b v i).exists_measurable_map_eq_unitInterval
  choose ψ hψ hLaw using hex
  exact ⟨ψ, hψ, hLaw⟩

end InvariantIsing

end

end OAI
