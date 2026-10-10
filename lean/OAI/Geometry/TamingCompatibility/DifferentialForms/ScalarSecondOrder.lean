import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.NormalSymbol
import OAI.Geometry.TamingCompatibility.Charts.LocalFormalAdjoint

namespace OAI


noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open EuclideanEnergy
open scoped RealInnerProductSpace

lemma normalSymbol_second_sum {ι : Type*} [Fintype ι]
    (ξ : ι → V) (w : ι → ι → Pair) (hw : ∀ i j, w i j = w j i) :
    (∑ i, ∑ j, (normalSymbol (ξ i)).adjoint (normalSymbol (ξ j) (w i j))) =
      ∑ i, ∑ j, ⟪ξ i,ξ j⟫ • w i j := by
  let S := ∑ i, ∑ j, (normalSymbol (ξ i)).adjoint (normalSymbol (ξ j) (w i j))
  have hs : S = ∑ i, ∑ j, (normalSymbol (ξ j)).adjoint (normalSymbol (ξ i) (w i j)) := by
    dsimp only [S]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hw]
  have he : S+S = (2:ℝ) • (∑ i, ∑ j, ⟪ξ i,ξ j⟫ • w i j) := by
    conv_lhs => rhs; rw [hs]
    dsimp only [S]
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib]
    simp only [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hh := congrArg (fun L : Pair →L[ℝ] Pair => L (w i j))
      (normalSymbol_adjoint_polarized (ξ i) (ξ j))
    simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,_root_.smul_apply,
      ContinuousLinearMap.id_apply,smul_smul] using hh
  change S = _
  calc
    S = (1/2:ℝ) • (S+S) := by module
    _ = _ := by rw [he]; module

end TamingCompatibility.LocalMatrixOperator

namespace TamingCompatibility.LocalFormalAdjoint
open MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {D E F : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
  [CompleteSpace E] in
lemma schwartz_derivatives_commute (v w : D) (u : 𝓢(D,E)) :
    ∂_{v} (∂_{w} u) = ∂_{w} (∂_{v} u) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hf : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((u.smooth 2).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  change fderiv ℝ (fun y => fderiv ℝ u y w) x v =
    fderiv ℝ (fun y => fderiv ℝ u y v) x w
  rw [fderiv_clm_apply hf (differentiableAt_const _),
    fderiv_clm_apply hf (differentiableAt_const _)]
  simp only [fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add,
    ContinuousLinearMap.flip_apply]
  exact (u.smooth 2).contDiffAt.isSymmSndFDerivAt (by norm_num) _ _

variable {ι : Type*} [Fintype ι]
omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
  [CompleteSpace E] [CompleteSpace F] in
lemma firstOrder_derivative (e : ι → D) (a : ι → 𝓢(D,E →L[ℝ] F))
    (b : 𝓢(D,E →L[ℝ] F)) (u : 𝓢(D,E)) (v : D) :
    ∂_{v} (firstOrder e a b u) =
      (∑ j, multiply (∂_{v} (a j) : 𝓢(D,E →L[ℝ] F)) (∂_{v} (a j)).hasTemperateGrowth (∂_{e j} u)) +
      (∑ j, multiply (a j) (a j).hasTemperateGrowth (∂_{v} (∂_{e j} u))) +
      multiply (∂_{v} b : 𝓢(D,E →L[ℝ] F)) (∂_{v} b).hasTemperateGrowth u +
      multiply b b.hasTemperateGrowth (∂_{v} u) := by
  simp only [firstOrder,_root_.add_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    lineDerivOpCLM_apply,lineDerivOp_add,lineDerivOp_sum,lineDeriv_multiply,
    Finset.sum_add_distrib]
  abel

def squareRemainder (e : ι → D) (a : ι → 𝓢(D,E →L[ℝ] F))
    (b : 𝓢(D,E →L[ℝ] F)) (u : 𝓢(D,E)) : 𝓢(D,E) :=
  -(∑ i, multiply (∂_{e i} (adjointCoefficient (a i)) : 𝓢(D,F →L[ℝ] E))
      (∂_{e i} (adjointCoefficient (a i))).hasTemperateGrowth (firstOrder e a b u)) -
    (∑ i, multiply (adjointCoefficient (a i)) (adjointCoefficient (a i)).hasTemperateGrowth
      ((∑ j, multiply (∂_{e i} (a j) : 𝓢(D,E →L[ℝ] F)) (∂_{e i} (a j)).hasTemperateGrowth (∂_{e j} u)) +
        multiply (∂_{e i} b : 𝓢(D,E →L[ℝ] F)) (∂_{e i} b).hasTemperateGrowth u +
        multiply b b.hasTemperateGrowth (∂_{e i} u))) +
    multiply (adjointCoefficient b) (adjointCoefficient b).hasTemperateGrowth (firstOrder e a b u)

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
lemma square_expansion (e : ι → D) (a : ι → 𝓢(D,E →L[ℝ] F))
    (b : 𝓢(D,E →L[ℝ] F)) (u : 𝓢(D,E)) :
    formalAdjoint e a b (firstOrder e a b u) =
      -(∑ i, ∑ j, multiply (adjointCoefficient (a i)) (adjointCoefficient (a i)).hasTemperateGrowth
        (multiply (a j) (a j).hasTemperateGrowth (∂_{e i} (∂_{e j} u)))) +
      squareRemainder e a b u := by
  rw [formalAdjoint_expanded]
  simp only [firstOrder_derivative,squareRemainder,map_add,map_sum,
    Finset.sum_add_distrib]
  abel

end TamingCompatibility.LocalFormalAdjoint

end

end OAI
