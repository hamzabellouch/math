import OAI.Probability.InvariantIsing.Arrays.NSpinFactorization
import OAI.Probability.InvariantIsing.Fields.VectorGaussianTransition
import Mathlib.Probability.Kernel.Representation

namespace OAI

/-! Ancestor kernels for the two finite-dimensional Gaussian field terminals. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal ENNReal
namespace InvariantIsing

def vectorTerminalBackward (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (i : ℕ) : (Fin N → ℝ) → ℝ :=
  backwardValue n b (fun j => vectorGaussianLaw N (v j)) (fun _ p => p.1+p.2) F i

def vectorTerminalUpdate (N n : ℕ) : ℕ → (Fin N → ℝ) × (Fin N → ℝ) → (Fin N → ℝ) :=
  stoppedUpdate n (fun _ p => p.1+p.2)

def vectorTerminalMultiplier (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (i : ℕ) (p : (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  Real.exp (vectorTerminalBackward N n b v F (i+1) (vectorTerminalUpdate N n i p) -
    vectorTerminalBackward N n b v F i p.1)

lemma measurable_vectorTerminalBackward (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (i : ℕ) :
    Measurable (vectorTerminalBackward N n b v F i) :=
  measurable_backwardValue n b _ (fun _ => measurable_fst.add measurable_snd) hF i

lemma measurable_vectorTerminalUpdate (N n i : ℕ) : Measurable (vectorTerminalUpdate N n i) :=
  measurable_stoppedUpdate n (fun _ => measurable_fst.add measurable_snd) i

lemma measurable_vectorTerminalMultiplier (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (i : ℕ) :
    Measurable (vectorTerminalMultiplier N n b v F i) :=
  (((measurable_vectorTerminalBackward N n b v F hF (i+1)).comp
    (measurable_vectorTerminalUpdate N n i)).sub
    ((measurable_vectorTerminalBackward N n b v F hF i).comp measurable_fst)).exp

lemma vectorTerminalMultiplier_moment {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (i : ℕ) (z : Fin N → ℝ) :
    (∫⁻ a, ENNReal.ofReal (vectorTerminalMultiplier N n b v F i (z,a)^b i)
      ∂(vectorGaussianLaw N (v i) : Measure (Fin N → ℝ))) = 1 := by
  have hadm := backwardValue_linearGrowth_moments n b (fun j => vectorGaussianLaw N (v j))
    (fun j _ => vectorGaussianLaw_moments hN (v j)) hF hG (fun j hj => (hb.1 j hj).1)
  exact backwardValue_multiplier_moment_admissible n b (fun j => vectorGaussianLaw N (v j))
    (fun _ p => p.1+p.2) F (fun j hj => (hb.1 j hj).1) hadm i z

def vectorTerminalAncestorKernel (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (i : ℕ) :
    Kernel (Fin N → ℝ) (Fin N → ℝ) :=
  ⟨fun z => (vectorGaussianLaw N (v i) : Measure (Fin N → ℝ)).withDensity
    (fun a => ENNReal.ofReal (vectorTerminalMultiplier N n b v F i (z,a)^b i)),
    measurable_random_withDensity (ν := fun _ => (vectorGaussianLaw N (v i) : Measure (Fin N → ℝ)))
      (W := fun p => ENNReal.ofReal (vectorTerminalMultiplier N n b v F i p^b i))
      measurable_const ((measurable_vectorTerminalMultiplier N n b v F hF i).pow_const (b i)).ennreal_ofReal⟩

lemma vectorTerminalAncestorKernel_markov {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (i : ℕ) :
    IsMarkovKernel (vectorTerminalAncestorKernel N n b v F hF i) := by
  constructor
  intro z
  constructor
  change ((vectorGaussianLaw N (v i) : Measure (Fin N → ℝ)).withDensity _) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ]
  exact vectorTerminalMultiplier_moment hN n b v hb F hF hG i z

lemma vectorTerminalAncestorKernel_seed {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) :
    ∃ ψ : ℕ → (Fin N → ℝ) → unitInterval → (Fin N → ℝ),
      (∀ i, Measurable (Function.uncurry (ψ i))) ∧
      ∀ i z, volume.map (ψ i z) = vectorTerminalAncestorKernel N n b v F hF i z := by
  have hex i : ∃ ψ : (Fin N → ℝ) → unitInterval → (Fin N → ℝ),
      Measurable (Function.uncurry ψ) ∧ ∀ z, volume.map (ψ z) = vectorTerminalAncestorKernel N n b v F hF i z := by
    let := vectorTerminalAncestorKernel_markov hN n b v hb F hF hG i
    exact (vectorTerminalAncestorKernel N n b v F hF i).exists_measurable_map_eq_unitInterval
  choose ψ hψ hLaw using hex
  exact ⟨ψ,hψ,hLaw⟩

end InvariantIsing

end

end OAI
