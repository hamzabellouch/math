import OAI.Probability.InvariantIsing.Fields.PriorMinimumBounds
import OAI.Probability.InvariantIsing.Fields.PriorArrayResidual
import OAI.Probability.InvariantIsing.Arrays.TensorGGRate

namespace OAI

/-! Uniform GG residual bounds for the actual constrained-prior array. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology
namespace InvariantIsing

theorem priorPerturbation_arrayResidual_bound (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 3≤N →
    ∀ μ : Measure (SpecialOrthogonal N), ∀ [IsProbabilityMeasure μ], μ.IsMulLeftInvariant →
    ∀ m n : ℕ, ∀ ν : Measure (Spin N × LabeledLeaf n), ∀ [IsProbabilityMeasure ν],
    ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0<K → (∀ i, |eig i|≤K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, u j∈Set.Icc (1 : ℝ) 2) →
    ∀ v : Fin m → ℝ, (∀ a, v a∈Set.Icc (1 : ℝ) 2) → ∀ t : ℝ, |t|≤1 →
    ∀ h : ℕ → ℝ, Monotone h → 0≤h 0 → ∀ H : ℝ, h n≤H →
      let d := fun j : Fin N => enumeratedSpectralDegree m j
      let r := fun j : Fin N => enumeratedTreeDegree m j
      let L := H+4+C*(K+4*m+8)^2
      perturbationScale N≤1/32 → contactStep N≤1/4 →
      (∀ u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
        priorPerturbationObjective μ ν eig c I t h u v≤priorPerturbationObjective μ ν eig c I t h u' v') →
      ∀ j : Fin N, ∀ q : ℕ, ∀ i : Fin (q+1),
      ∀ D : SpectralBlock (m+1) (q+1) → ℝ, Continuous D →
      ∀ B : ℝ, 0≤B → (∀ x, |D x|≤B) →
      |spectralMonomialResidual
        (priorNamespacedArrayLaw μ ν (diagonalPerturbedEigenvalues eig I v t) c I d
          (tensorPerturbationAmplitude N u) r h)
        (q+1) i D (Fin.lastCases (r j) (d j))|≤tensorContactGGRate N j m L B := by
  obtain ⟨C,hC,hgg⟩ := priorPerturbation_minimum_bounds hhaar hgauss
  refine ⟨C,hC,?_⟩
  intro N hN μ hμ hμinv m n ν hν eig c K hK heig I u hu v hv t ht h hh h0 H hH d r L
    he hs hmin j q i D hD B hB hDb
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure ν := hν
  let e := Equiv.swap 0 i
  have hg := (hgg N hN μ hμ hμinv m n ν hν eig c K hK heig I u hu v hv t ht h hh h0 H hH
    he hs hmin).2 j q B hB (permutedSpectralBlockTest I n e D)
    (measurable_permutedSpectralBlockTest I n e D hD) (fun U σ => hDb _)
  have hr := priorNamespacedArrayLaw_residual μ ν (diagonalPerturbedEigenvalues eig I v t) c I d
    (tensorPerturbationAmplitude N u) r h j e D hD
  have hei : e 0=i := Equiv.swap_apply_left 0 i
  rw [hei] at hr
  rw [hr]
  exact hg

end InvariantIsing

end

end OAI
