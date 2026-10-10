import OAI.Probability.InvariantIsing.Fields.PriorArrayLaw
import OAI.Probability.InvariantIsing.Fields.PriorFiniteGG
import OAI.Probability.InvariantIsing.Arrays.TensorArrayResidual

namespace OAI

/-! Exact equality of the constrained finite-model and spectral-array GG residuals. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology
namespace InvariantIsing

/-- Common rotation is retained in every finite test; arbitrary replica
indices are handled by injective sampling, not by independence of rotations. -/
theorem priorNamespacedArrayLaw_residual {N m k n q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν₀ : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν₀] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (e : Equiv.Perm (Fin (q + 1))) (D : SpectralBlock (m + 1) (q + 1) → ℝ) (hD : Continuous D) :
    spectralMonomialResidual (priorNamespacedArrayLaw μ ν₀ eig c I degree amplitude r h)
      (q + 1) (e 0) D (Fin.lastCases (r j) (degree j)) =
      priorSpectralGGResidual μ ν₀ eig c I degree amplitude r h j
        (permutedSpectralBlockTest I n e D) := by
  classical
  let L := priorNamespacedArrayLaw μ ν₀ eig c I degree amplitude r h
  let d : Fin (m + 1) → ℕ := Fin.lastCases (r j) (degree j)
  let D' := permutedSpectralBlockTest I n e D
  let κ := spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N) I (degree j) n (r j)
  have hcD : Continuous (fun x => D (spectralBlockView (m + 1) (q + 1) x)) :=
    hD.comp (continuous_spectralBlockView _ _)
  have hmono : Continuous (spectralEntryMonomial d) := continuous_spectralEntryMonomial d
  have hnew : (∫ x, D (spectralBlockView (m + 1) (q + 1) x) *
      spectralEntryMonomial d (x (e 0, q + 1)) ∂(L : Measure (SpectralArray (m + 1)))) =
      priorNamespacedReplicaAverage μ ν₀ eig c I degree amplitude r h
        (fun U (τ : Fin (q + 1 + 1) → Spin N × LabeledLeaf n) =>
          D' U (Fin.tail τ) * κ U ((Fin.tail τ) 0) (τ 0)) := by
    apply priorNamespacedArrayLaw_test μ ν₀ eig c I degree amplitude r h
      _ (hcD.mul (hmono.comp (continuous_apply _))) _
      (newReplicaEmbedding (q + 1) e) (newReplicaEmbedding_injective _ e)
    intro U σ
    simp only [Pi.mul_apply, Function.comp_apply, newReplicaEmbedding, Fin.cases_zero, Fin.cases_succ, Fin.tail]
    change D (spectralBlockView (m + 1) (q + 1) (fun ij : ℕ × ℕ =>
        spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2))) *
        spectralEntryMonomial d (spectralJointEntry (specialRotation U) I n (σ (e 0)) (σ (q + 1))) =
      D' U (fun i => σ (e i)) * κ U (σ (e 0)) (σ (q + 1))
    rw [show D' U (fun i => σ ((e i).val)) =
      D (spectralBlockView (m + 1) (q + 1) (fun ij : ℕ × ℕ =>
        spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2))) from
      permutedSpectralBlockTest_embedding I n e D U σ]
    simp only [spectralJointEntry_selectedMonomial, d, κ]
  have hblock : (∫ x, D (spectralBlockView (m + 1) (q + 1) x)
      ∂(L : Measure (SpectralArray (m + 1)))) =
      priorNamespacedReplicaAverage μ ν₀ eig c I degree amplitude r h D' := by
    apply priorNamespacedArrayLaw_test μ ν₀ eig c I degree amplitude r h _ hcD D'
      (fun i => (e i).val) (Fin.val_injective.comp e.injective)
    intro U σ
    exact (permutedSpectralBlockTest_embedding I n e D U σ).symm
  have hpair : (∫ x, spectralEntryMonomial d (x (0, 1))
      ∂(L : Measure (SpectralArray (m + 1)))) =
      priorNamespacedReplicaAverage μ ν₀ eig c I degree amplitude r h
        (fun U (τ : Fin 2 → Spin N × LabeledLeaf n) => κ U (τ 1) (τ 0)) := by
    refine priorNamespacedArrayLaw_test μ ν₀ eig c I degree amplitude r h _
      (hmono.comp (continuous_apply _)) _ ![1, 0] ?_ ?_
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · intro U σ
      exact spectralJointEntry_selectedMonomial U I n (σ 0) (σ 1) (degree j) (r j)
  have hsum : (∑ a ∈ Finset.univ.erase (e 0), ∫ x,
      D (spectralBlockView (m + 1) (q + 1) x) * spectralEntryMonomial d (x (e 0, a))
      ∂(L : Measure (SpectralArray (m + 1)))) =
      priorNamespacedReplicaAverage μ ν₀ eig c I degree amplitude r h
        (fun U σ => D' U σ * ∑ l : Fin q, κ U (σ 0) (σ l.succ)) := by
    have hI (a : Fin (q + 1)) : Integrable
        (fun x : SpectralArray (m + 1) => D (spectralBlockView (m + 1) (q + 1) x) *
          spectralEntryMonomial d (x (e 0, a))) (L : Measure (SpectralArray (m + 1))) :=
      compact_integrable (hcD.mul (hmono.comp (continuous_apply _)))
    rw [← integral_finsetSum _ (fun a _ => hI a)]
    apply priorNamespacedArrayLaw_test μ ν₀ eig c I degree amplitude r h
      _ (continuous_finsetSum _ fun a _ => hcD.mul (hmono.comp (continuous_apply _))) _
      (fun i => (e i).val) (Fin.val_injective.comp e.injective)
    intro U σ
    rw [show D' U (fun i => σ ((e i).val)) =
      D (spectralBlockView (m + 1) (q + 1) (fun ij : ℕ × ℕ =>
        spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2))) from
      permutedSpectralBlockTest_embedding I n e D U σ]
    rw [sum_nonzero_permutation e (fun a => κ U (σ (e 0)) (σ a)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Pi.mul_apply, Function.comp_apply, d, spectralJointEntry_selectedMonomial, κ]
  unfold spectralMonomialResidual
  rw [hnew, hblock, hpair, hsum]
  rfl

end InvariantIsing

end

end OAI
