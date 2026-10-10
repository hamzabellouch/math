import Mathlib
import OAI.Probability.SKBarriers.Scalar.PrefixAlgebra
import OAI.Probability.SKBarriers.Gaussian.AffineMomentCalculus

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {S : Type} [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem affineMoment_sum {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype I] (c : S → ℝ) (U : S → E →L[ℝ] ℝ) (g : I → S → ℝ) (z : E) :
    affineMoment c U (fun s => ∑ i, g i s) z = ∑ i, affineMoment c U (g i) z := by
  simp only [affineMoment,Finset.mul_sum]
  exact Finset.sum_comm

def weightedHierarchyTerminalMean (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ) : ℝ :=
  ∫ z, affineMoment c U g z ∂hierarchyPathLaw n m (affineLogPartition c U) 0

theorem weightedHierarchyTerminalMean_integrable (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ) :
    Integrable (affineMoment c U g) (hierarchyPathLaw n m (affineLogPartition c U) 0) := by
  classical
  exact hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs c U)
    (affineMoment_continuous c U g)
    (affineMoment_norm_le c U g (fun s => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ s))) 0

theorem weightedHierarchyTerminalMean_const (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (a : ℝ) :
    weightedHierarchyTerminalMean n m c U (fun _ => a) = a := by
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs c U) 0
  simp only [weightedHierarchyTerminalMean,affineMoment,← Finset.sum_mul,affineGibbs_sum,one_mul]
  simp

theorem weightedHierarchyTerminalMean_mono (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) {g h : S → ℝ} (hgh : ∀ s, g s ≤ h s) :
    weightedHierarchyTerminalMean n m c U g ≤ weightedHierarchyTerminalMean n m c U h := by
  apply integral_mono (weightedHierarchyTerminalMean_integrable n m c U g)
    (weightedHierarchyTerminalMean_integrable n m c U h)
  intro z
  exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hgh s) (affineGibbs_pos c U z s).le)

theorem weightedHierarchyTerminalMean_sum {I : Type} [Fintype I] (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : I → S → ℝ) :
    weightedHierarchyTerminalMean n m c U (fun s => ∑ i, g i s) =
      ∑ i, weightedHierarchyTerminalMean n m c U (g i) := by
  simp only [weightedHierarchyTerminalMean,affineMoment_sum]
  exact integral_finsetSum _ (fun i _ => weightedHierarchyTerminalMean_integrable n m c U (g i))

omit [Nonempty S] in
theorem weightedHierarchyTerminalMean_const_mul (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ) (a : ℝ) :
    weightedHierarchyTerminalMean n m c U (fun s => a*g s) =
      a*weightedHierarchyTerminalMean n m c U g := by
  simp only [weightedHierarchyTerminalMean,affineMoment_const_mul,integral_const_mul]

end
end SK.Analytic

end
end

end OAI
