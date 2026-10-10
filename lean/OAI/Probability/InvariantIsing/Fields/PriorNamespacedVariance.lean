import OAI.Probability.InvariantIsing.Fields.PriorPerturbationVariance
import OAI.Probability.InvariantIsing.Fields.PriorTensorNamespace

namespace OAI

/-! The same uniform bound for the raw, independently namespaced log partition. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

theorem priorNamespacedPerturbation_variance (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 3≤N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m n : ℕ, ∀ ν : Measure (Spin N × LabeledLeaf n), IsProbabilityMeasure ν →
    ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0<K → (∀ i, |eig i|≤K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, |u j|≤2) →
    ∀ v : Fin m → ℝ, (∀ a, |v a|≤2) → ∀ t : ℝ, |t|≤1 →
    ∀ h : ℕ → ℝ, Monotone h → 0≤h 0 → ∀ H : ℝ, h n≤H →
      let d := fun j : Fin N => enumeratedSpectralDegree m j
      let r := fun j : Fin N => enumeratedTreeDegree m j
      let F := priorNamespacedLog ν (diagonalPerturbedEigenvalues eig I v t) c I d
        (tensorPerturbationAmplitude N u) (fun i => tensorPathProfile I d n r h i)
      MemLp F 2 (μ.prod gaussianCoordinates) ∧
        variance F (μ.prod gaussianCoordinates) ≤ N*(H+4+C*(K+4*m+8)^2) := by
  obtain ⟨C,hC,hvar⟩ := priorPerturbation_variance hhaar hgauss
  refine ⟨C,hC,?_⟩
  intro N hN μ hμ hμinv m n ν hν eig c K hK heig I u hu v hv t ht h hh h0 H hH d r F
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure ν := hν
  let G := priorTensorLog ν (diagonalPerturbedEigenvalues eig I v t) c I d
    (tensorPerturbationAmplitude N u) (fun i => tensorPathProfile I d n r h i)
  have hn : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hscaled := hvar N hN μ hμ hμinv m n ν hν eig c K hK heig I u hu v hv t ht h hh h0 H hH
  have heq : (fun p => (N : ℝ)*((N : ℝ)⁻¹*G p))=G := by
    funext p
    simp only [← mul_assoc,mul_inv_cancel₀ hn,one_mul]
  have hg : MemLp G 2 (μ.prod gaussianCoordinates) := by
    rw [← heq]
    exact hscaled.1.const_mul N
  have hvg : variance G (μ.prod gaussianCoordinates)≤N*(H+4+C*(K+4*m+8)^2) := by
    calc
      _ = (N : ℝ)^2 * variance (fun p => (N : ℝ)⁻¹*G p) (μ.prod gaussianCoordinates) := by
        conv_lhs => rw [← heq]
        exact variance_const_mul N _ _
      _ ≤ (N : ℝ)^2*((H+4+C*(K+4*m+8)^2)/N) :=
        mul_le_mul_of_nonneg_left hscaled.2 (sq_nonneg _)
      _ = _ := by field_simp
  have hm := priorNamespacedLog_moments μ ν (diagonalPerturbedEigenvalues eig I v t) c I d
    (tensorPerturbationAmplitude N u) (fun i => tensorPathProfile I d n r h i) hg
  exact ⟨hm.1,hm.2.1.trans_le hvg⟩

end InvariantIsing

end

end OAI
