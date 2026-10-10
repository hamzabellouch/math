import OAI.Probability.InvariantIsing.Arrays.TensorArrayLaw
import OAI.Probability.InvariantIsing.Arrays.TensorFiniteGG
import OAI.Probability.IsingPerceptron.EnrichedGGFinite

namespace OAI

/-! The actual finite tensor GG residual is the spectral-array residual. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

lemma spectralJointEntry_monomial {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (n : ℕ) (x y : Spin N × LabeledLeaf n) (d : Fin (m + 1) → ℕ) :
    spectralEntryMonomial d (spectralJointEntry U I n x y) =
      (∏ a, projectedOverlap U (I a) x.1 y.1 ^ d a.castSucc) *
        treeOverlap n x.2 y.2 ^ d (Fin.last m) := by
  unfold spectralEntryMonomial
  rw [Fin.prod_univ_castSucc]
  simp only [spectralJointEntry_spectral, spectralJointEntry_tree]

lemma spectralJointEntry_selectedMonomial {N m : ℕ} (U : SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (n : ℕ) (x y : Spin N × LabeledLeaf n)
    (d : Fin m → ℕ) (r : ℕ) :
    spectralEntryMonomial (Fin.lastCases r d) (spectralJointEntry (specialRotation U) I n x y) =
      spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N) I d n r U x y := by
  rw [spectralJointEntry_monomial]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, spectralPerturbationKernel, id_eq]

/-- Common rotation is retained in every finite test; arbitrary replica
indices are handled by injective sampling, not by independence of rotations. -/
theorem tensorNamespacedArrayLaw_residual {N m k q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (e : Equiv.Perm (Fin (q + 1))) (D : SpectralBlock (m + 1) (q + 1) → ℝ) (hD : Continuous D) :
    spectralMonomialResidual (tensorNamespacedArrayLaw μ eig c I degree amplitude n b r h)
      (q + 1) (e 0) D (Fin.lastCases (r j) (degree j)) =
      tensorSpectralGGResidual μ eig c I degree amplitude n b r h j
        (permutedSpectralBlockTest I n e D) := by
  classical
  let L := tensorNamespacedArrayLaw μ eig c I degree amplitude n b r h
  let d : Fin (m + 1) → ℕ := Fin.lastCases (r j) (degree j)
  let D' := permutedSpectralBlockTest I n e D
  let κ := spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N) I (degree j) n (r j)
  have hcD : Continuous (fun x => D (spectralBlockView (m + 1) (q + 1) x)) :=
    hD.comp (continuous_spectralBlockView _ _)
  have hmono : Continuous (spectralEntryMonomial d) := continuous_spectralEntryMonomial d
  have hnew : (∫ x, D (spectralBlockView (m + 1) (q + 1) x) *
      spectralEntryMonomial d (x (e 0, q + 1)) ∂(L : Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ eig c I degree amplitude n b r h
        (fun U (τ : Fin (q + 1 + 1) → Spin N × LabeledLeaf n) =>
          D' U (Fin.tail τ) * κ U ((Fin.tail τ) 0) (τ 0)) := by
    apply tensorNamespacedArrayLaw_test μ eig c I degree amplitude n b r h
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
      tensorNamespacedReplicaAverage μ eig c I degree amplitude n b r h D' := by
    apply tensorNamespacedArrayLaw_test μ eig c I degree amplitude n b r h _ hcD D'
      (fun i => (e i).val) (Fin.val_injective.comp e.injective)
    intro U σ
    exact (permutedSpectralBlockTest_embedding I n e D U σ).symm
  have hpair : (∫ x, spectralEntryMonomial d (x (0, 1))
      ∂(L : Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ eig c I degree amplitude n b r h
        (fun U (τ : Fin 2 → Spin N × LabeledLeaf n) => κ U (τ 1) (τ 0)) := by
    refine tensorNamespacedArrayLaw_test μ eig c I degree amplitude n b r h _
      (hmono.comp (continuous_apply _)) _ ![1, 0] ?_ ?_
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · intro U σ
      exact spectralJointEntry_selectedMonomial U I n (σ 0) (σ 1) (degree j) (r j)
  have hsum : (∑ a ∈ Finset.univ.erase (e 0), ∫ x,
      D (spectralBlockView (m + 1) (q + 1) x) * spectralEntryMonomial d (x (e 0, a))
      ∂(L : Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ eig c I degree amplitude n b r h
        (fun U σ => D' U σ * ∑ l : Fin q, κ U (σ 0) (σ l.succ)) := by
    have hI (a : Fin (q + 1)) : Integrable
        (fun x : SpectralArray (m + 1) => D (spectralBlockView (m + 1) (q + 1) x) *
          spectralEntryMonomial d (x (e 0, a))) (L : Measure (SpectralArray (m + 1))) :=
      compact_integrable (hcD.mul (hmono.comp (continuous_apply _)))
    rw [← integral_finsetSum _ (fun a _ => hI a)]
    apply tensorNamespacedArrayLaw_test μ eig c I degree amplitude n b r h
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
