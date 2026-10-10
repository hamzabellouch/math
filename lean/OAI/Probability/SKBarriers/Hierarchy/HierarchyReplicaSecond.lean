import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyReplica

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section SecondMoment
variable {S : Type} [Fintype S] [Nonempty S]

def hierarchyReplicaSecond {N : ℕ} (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (v : S → Fin N → ℝ) (j : Fin (n+1)) : ℝ :=
  ∫ z, finiteReplicaMoment (hierarchySpinWeight n m U j z)
    (fun s t => (normalizedDot (v s) (v t))^2)
    ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0

theorem hierarchyReplicaSecond_integrable {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1)
    (j : Fin (n+1)) : Integrable (fun z => finiteReplicaMoment (hierarchySpinWeight n m U j z)
      (fun s t => (normalizedDot (v s) (v t))^2))
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) := by
  apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (finiteReplicaMoment_continuous _ (fun s => (hierarchySpinWeight_regular n m U j s).1) _) (C := 1) _ 0
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (finiteReplicaMoment_nonneg _ (hierarchySpinWeight_nonneg n m U j z) _ (fun _ _ => sq_nonneg _))]
  apply finiteReplicaMoment_le_const _ (hierarchySpinWeight_nonneg n m U j z) (hierarchySpinWeight_sum n m U j z)
  intro s t
  have H := abs_normalizedDot_le_one (v s) (v t) (hv s) (hv t)
  have H0 := abs_nonneg (normalizedDot (v s) (v t))
  nlinarith [sq_abs (normalizedDot (v s) (v t))]

theorem hierarchyOverlapError_eq_second_sub_sq {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1)
    (j : Fin (n+1)) : hierarchyOverlapError n m U v j = hierarchyReplicaSecond n m U v j -
      (hierarchyMeanOverlap n m U (fun i s => v s i) j)^2 := by
  let μ := hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  let r := hierarchyMeanOverlap n m U (fun i s => v s i) j
  have hs := hierarchyReplicaSecond_integrable n m U v hv j
  have hm := hierarchyMeanSquare_integrable n m U (fun i s => v s i)
    (fun i s => by simpa only [Real.norm_eq_abs] using hv s i) j 0
  have he (z : ParameterSpace n) : finiteReplicaMoment (hierarchySpinWeight n m U j z)
      (fun s t => (normalizedDot (v s) (v t)-r)^2) =
      finiteReplicaMoment (hierarchySpinWeight n m U j z) (fun s t => (normalizedDot (v s) (v t))^2)-
        2*r*hierarchyMeanSquare n m U (fun i s => v s i) j z+r^2 := by
    rw [finiteReplicaMoment_sub_square _ (hierarchySpinWeight_sum n m U j z),
      finiteReplicaMoment_normalizedDot,← hierarchyMeanSquare_eq_finiteMean]
  change (∫ z, finiteReplicaMoment (hierarchySpinWeight n m U j z)
    (fun s t => (normalizedDot (v s) (v t)-r)^2) ∂μ) = hierarchyReplicaSecond n m U v j-r^2
  simp_rw [he]
  rw [integral_add (f := fun z => finiteReplicaMoment (hierarchySpinWeight n m U j z)
    (fun s t => (normalizedDot (v s) (v t))^2)-2*r*hierarchyMeanSquare n m U (fun i s => v s i) j z)
    (g := fun _ => r^2) (hs.sub (hm.const_mul (2*r))) (integrable_const (r^2)),
    integral_sub hs (hm.const_mul (2*r)),integral_const_mul]
  have hc : (∫ _ : ParameterSpace n, r^2 ∂μ) = r^2 := by simp [μ]
  rw [hc]
  change hierarchyReplicaSecond n m U v j-2*r*r+r^2 = hierarchyReplicaSecond n m U v j-r^2
  ring
end SecondMoment
end SK.Analytic

end
end

end

end OAI
