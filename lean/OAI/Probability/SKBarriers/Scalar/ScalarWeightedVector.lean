import Mathlib
import OAI.Probability.SKBarriers.Scalar.VectorAverage
import OAI.Probability.SKBarriers.SpinGlass.FinitePenalty
import OAI.Probability.SKBarriers.Replicas.TripleRecursiveExpansion

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def scalarWeightedAverage (n : ℕ) (m v a : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  vectorHierarchyAverage n m (fun i => (v i,a i))
    (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (x,0)

theorem scalarWeightedAverage_integral (n : ℕ) (m v a : Fin n → ℝ)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (x : ℝ) :
    scalarWeightedAverage n m v a f x=
      ∫ z, (coordinateLinear n a z)^2 ∂hierarchyPathLaw n m (f ∘ scalarSpinField n v) x := by
  have he (z : ParameterSpace n) :
      (parameter n z, (0:ℝ)) + ∑ i, coordinateProjection n i z • (v i,a i)=
        (scalarSpinField n v z,coordinateLinear n a z) := by
    have hfst := map_sum (ContinuousLinearMap.fst ℝ ℝ ℝ) (fun i => coordinateProjection n i z • (v i,a i)) Finset.univ
    have hsnd := map_sum (ContinuousLinearMap.snd ℝ ℝ ℝ) (fun i => coordinateProjection n i z • (v i,a i)) Finset.univ
    have heq : (∑ i, coordinateProjection n i z • (v i,a i)) =
        (∑ i, v i*coordinateProjection n i z, ∑ i, a i*coordinateProjection n i z) := by
      apply Prod.ext
      · simpa only [ContinuousLinearMap.coe_fst',Prod.smul_fst,smul_eq_mul,mul_comm] using hfst
      · simpa only [ContinuousLinearMap.coe_snd',Prod.smul_snd,smul_eq_mul,mul_comm] using hsnd
    rw [heq]
    simp [scalarSpinField,coordinateLinear_apply]
  have H := congrFun (hierarchyAverage_vector_linear n m (fun i => (v i,a i))
    (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (fun x => (x,0))) x
  simp only [he] at H
  unfold scalarWeightedAverage
  rw [← H]
  exact hierarchyAverage_eq_integral_exp n m _ (hf.compCLM (scalarSpinField n v))
    _ ((coordinateLinear n a).continuous.pow 2) ((HasExpGrowth.linear _).pow 2) x

theorem scalarWeightedAverage_nonneg (n : ℕ) (m v a : Fin n → ℝ)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (x : ℝ) :
    0 ≤ scalarWeightedAverage n m v a f x := by
  rw [scalarWeightedAverage_integral n m v a hf x]
  exact integral_nonneg (fun z => sq_nonneg _)

theorem scalarWeightedAverage_le (n : ℕ) (m v a : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hL : LipschitzWith 1 f) (x : ℝ) :
    scalarWeightedAverage n m v a f x ≤
      2*(∑ i, (a i)^2)+(2*∑ i, |a i| * |v i|)^2 := by
  rw [scalarWeightedAverage_integral n m v a hf x]
  apply hierarchy_square_bound n m hm hmono _ (hf.compCLM (scalarSpinField n v))
    (fun i => |v i|) (fun i => abs_nonneg _) _ x a
  intro z i
  have H := scalar_composition_coordinate_bound hf hL (scalarSpinField n v) z (coordinateAxis n i)
  simpa only [Function.comp_def,scalarSpinField,add_apply,parameter_coordinateAxis,coordinateLinear_coordinateAxis,zero_add] using H

theorem scalarWeightedAverage_spin_le (n : ℕ) (m v k : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hk : ∀ i,0 ≤ k i) (x R : ℝ)
    (hR : ∀ i,k i≠0 → scalarFiniteResponse n m v i x ≤ R) :
    scalarWeightedAverage n m v (fun i => k i*v i) scalarSpinTerminal x ≤
      (∑ i, (k i)^2*(v i)^2)+R*finiteClockPenalty n m (fun i => k i*(v i)^2) := by
  rw [scalarWeightedAverage_integral n m v _ scalarSpinTerminal_regular x]
  have he : scalarSpinTerminal ∘ scalarSpinField n v=
      affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v) := by
    simpa only [Function.comp_def,scalarSpinField,add_apply,coordinateLinear_apply] using scalarSpinTerminal_affine n v
  rw [he]
  exact scalarHierarchy_weighted_increment_square_le n m v k hm hk x R hR

end SK.Analytic

end
end

end OAI
