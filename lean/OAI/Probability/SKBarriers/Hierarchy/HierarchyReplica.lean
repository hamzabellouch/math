import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyProbability
import OAI.Probability.SKBarriers.Hierarchy.AverageMeanVariance
import OAI.Probability.SKBarriers.Replicas.ReplicaVarianceSplit

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
open Matrix
section FiniteReplicaBounds
variable {S : Type} [Fintype S]

theorem finiteReplicaMoment_mono (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (g h : S → S → ℝ)
    (hgh : ∀ s t, g s t ≤ h s t) : finiteReplicaMoment p g ≤ finiteReplicaMoment p h := by
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro t _
  exact mul_le_mul_of_nonneg_left (hgh s t) (mul_nonneg (hp s) (hp t))

theorem finiteReplicaMoment_nonneg (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (g : S → S → ℝ)
    (hg : ∀ s t, 0 ≤ g s t) : 0 ≤ finiteReplicaMoment p g :=
  Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun t _ => mul_nonneg (mul_nonneg (hp s) (hp t)) (hg s t)

theorem finiteReplicaMoment_le_const (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1)
    (g : S → S → ℝ) (C : ℝ) (hg : ∀ s t, g s t ≤ C) : finiteReplicaMoment p g ≤ C := by
  exact (finiteReplicaMoment_mono p hp g (fun _ _ => C) hg).trans_eq (finiteReplicaMoment_const p hs C)

theorem finiteReplicaMoment_continuous {Ω : Type} [TopologicalSpace Ω]
    (P : Ω → S → ℝ) (hP : ∀ s, Continuous (fun z => P z s)) (g : S → S → ℝ) :
    Continuous (fun z => finiteReplicaMoment (P z) g) := by
  exact continuous_finsetSum _ (fun s _ => continuous_finsetSum _ (fun t _ => ((hP s).mul (hP t)).mul continuous_const))
end FiniteReplicaBounds

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section HierarchyReplica
variable {S : Type} [Fintype S] [Nonempty S]

def hierarchyOverlapError {N : ℕ} (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (v : S → Fin N → ℝ) (j : Fin (n+1)) : ℝ :=
  ∫ z, finiteReplicaMoment (hierarchySpinWeight n m U j z)
    (fun s t => (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)^2)
    ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0

theorem hierarchyMeanSquare_eq_finiteMean {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) :
    hierarchyMeanSquare n m U (fun i s => v s i) j z = normalizedSquare (finiteMean (hierarchySpinWeight n m U j z) v) := by
  simp only [hierarchyMeanSquare,hierarchySpinMean_eq_sum]
  congr 1
  funext i
  exact (finiteMean_apply _ _ i).symm

theorem hierarchyOverlap_integrand_bounds {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1)
    (j : Fin (n+1)) (z : ParameterSpace n) :
    let r := hierarchyMeanOverlap n m U (fun i s => v s i) j
    let Q := finiteReplicaMoment (hierarchySpinWeight n m U j z) (fun s t => (normalizedDot (v s) (v t)-r)^2)
    0 ≤ Q ∧ Q ≤ 4 := by
  dsimp only
  refine ⟨finiteReplicaMoment_nonneg _ (hierarchySpinWeight_nonneg n m U j z) _ (fun _ _ => sq_nonneg _),?_⟩
  apply finiteReplicaMoment_le_const _ (hierarchySpinWeight_nonneg n m U j z) (hierarchySpinWeight_sum n m U j z)
  intro s t
  have hdot := abs_normalizedDot_le_one (v s) (v t) (hv s) (hv t)
  have hr := hierarchyMeanOverlap_bounds n m U (fun i s => v s i)
    (fun i s => by simpa only [Real.norm_eq_abs] using hv s i) j
  have ha : |normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j| ≤ 2 := by
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hr.1]; linarith [hr.2])
  have hb := abs_nonneg (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)
  nlinarith [sq_abs (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)]

theorem hierarchyOverlapError_bounds {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1) (j : Fin (n+1)) :
    0 ≤ hierarchyOverlapError n m U v j ∧ hierarchyOverlapError n m U v j ≤ 4 := by
  let f := affineLogPartition (fun _ => 0) U
  let := hierarchyPathLaw_probability n m f (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  have hc := finiteReplicaMoment_continuous (hierarchySpinWeight n m U j)
    (fun s => (hierarchySpinWeight_regular n m U j s).1)
    (fun s t => (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)^2)
  have hi := Integrable.of_bound (μ := hierarchyPathLaw n m f 0) hc.aestronglyMeasurable 4
    (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hierarchyOverlap_integrand_bounds n m U v hv j z).1]
      exact (hierarchyOverlap_integrand_bounds n m U v hv j z).2)
  refine ⟨integral_nonneg (fun z => (hierarchyOverlap_integrand_bounds n m U v hv j z).1),?_⟩
  calc
    _ ≤ ∫ _ : ParameterSpace n, (4 : ℝ) ∂hierarchyPathLaw n m f 0 :=
      integral_mono hi (integrable_const 4) (fun z => (hierarchyOverlap_integrand_bounds n m U v hv j z).2)
    _ = 4 := by simp
end HierarchyReplica
end SK.Analytic

end
end

end

end OAI
