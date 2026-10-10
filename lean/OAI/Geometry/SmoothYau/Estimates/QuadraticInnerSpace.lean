import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
namespace YauCounterexamples

def QuadraticInnerSpace {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (_hA : A.PosDef) := ι → ℝ

namespace QuadraticInnerSpace
variable {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (hA : A.PosDef)
instance : NormedAddCommGroup (QuadraticInnerSpace A hA) := Matrix.toNormedAddCommGroup A hA
instance : InnerProductSpace ℝ (QuadraticInnerSpace A hA) := Matrix.toInnerProductSpace A hA.posSemidef
instance : FiniteDimensional ℝ (QuadraticInnerSpace A hA) :=
  inferInstanceAs (FiniteDimensional ℝ (ι → ℝ))

lemma norm_sq (x : QuadraticInnerSpace A hA) : ‖x‖ ^ 2 = x ⬝ᵥ (A *ᵥ x) := by
  rw [← real_inner_self_eq_norm_sq]
  change (A *ᵥ x) ⬝ᵥ x = _
  exact dotProduct_comm _ _

end QuadraticInnerSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) (hA : A.PosDef)

def quadraticNormEquiv : E ≃L[ℝ] QuadraticInnerSpace A hA := by
  classical
  exact LinearEquiv.toContinuousLinearEquiv <|
    ((InnerProductSpace.toDual ℝ E).toLinearEquiv.trans LinearMap.toContinuousLinearMap.symm).trans
      b.dualBasis.equivFun

lemma quadraticNormEquiv_apply (x : E) (i : ι) :
    quadraticNormEquiv b A hA x i = ⟪b i, x⟫_ℝ := by
  classical
  change b.dualBasis.equivFun ((InnerProductSpace.toDual ℝ E x).toLinearMap) i = _
  rw [Module.Basis.dualBasis_equivFun]
  change ⟪x, b i⟫_ℝ = ⟪b i, x⟫_ℝ
  exact real_inner_comm (b i) x

lemma quadraticNormEquiv_norm_sq (x : E) :
    ‖quadraticNormEquiv b A hA x‖ ^ 2 =
      ∑ i, ∑ j, A i j * ⟪b i, x⟫_ℝ * ⟪b j, x⟫_ℝ := by
  rw [QuadraticInnerSpace.norm_sq]
  simp only [dotProduct, Matrix.mulVec, quadraticNormEquiv_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end YauCounterexamples

open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real

end

end OAI
