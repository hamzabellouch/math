import OAI.Probability.InvariantIsing.Arrays.TensorLimitingGG
import OAI.Probability.InvariantIsing.Spectral.SpectralGGGeometry

namespace OAI

/-! Geometry of weak limits of the actual perturbed tensor array laws. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma tensorPerturbedArrayLaw_gram {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (n : ℕ) (b h : ℕ → ℝ) :
    ∀ᵐ x ∂(tensorPerturbedArrayLaw μ eig c I u v t n b h : Measure (SpectralArray (m + 1))),
      SpectralGram x := by
  unfold tensorPerturbedArrayLaw tensorNamespacedArrayLaw
  exact spectralArrayLaw_gram _ _ _ _ _ _ _

lemma tensorPerturbedArrayLaw_reindex {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (n : ℕ) (b h : ℕ → ℝ) (e : ℕ → ℕ) (he : Function.Injective e) :
    (tensorPerturbedArrayLaw μ eig c I u v t n b h : Measure (SpectralArray (m + 1))).map
      (permuteSpectralArray e) = tensorPerturbedArrayLaw μ eig c I u v t n b h := by
  unfold tensorPerturbedArrayLaw tensorNamespacedArrayLaw
  exact spectralArrayLaw_map_reindex _ _ _ _ _ _ _ e he

/-- The geometry is derived from the actual finite Gibbs samples, independently
of the subsequent concentration/minimization argument that enforces GG. -/
theorem tensorPerturbedArrayLaw_limit_geometry (N : ℕ → ℕ) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (v : ℕ → Fin m → ℝ) (t : ℕ → ℝ)
    (b : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k)
      (u k) (v k) (t k) n b (h k)) atTop (𝓝 Q)) :
    (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x) ∧
      ∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q := by
  constructor
  · exact spectralArray_limit_gram hL (fun k => tensorPerturbedArrayLaw_gram
      (μ k) (eig k) (c k) (I k) (u k) (v k) (t k) n b (h k))
  · intro e he
    exact spectralArray_limit_reindex hL e (fun k => tensorPerturbedArrayLaw_reindex
      (μ k) (eig k) (c k) (I k) (u k) (v k) (t k) n b (h k) e he)

end InvariantIsing

end

end OAI
