import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeFrameTest

namespace OAI

noncomputable section
namespace TamingCompatibility.HodgeNormalSymbol
open EuclideanEnergy
open scoped RealInnerProductSpace

lemma normalSymbol_add_covector (ξ η : V) :
    normalSymbol (ξ+η) = normalSymbol ξ + normalSymbol η := by
  apply ContinuousLinearMap.ext
  intro a
  ext i
  fin_cases i <;> simp [normalSymbol_apply,symbol,UnitaryFrame.interior,UnitaryFrame.star] <;> ring

lemma normalSymbol_smul_covector (c : ℝ) (ξ : V) :
    normalSymbol (c • ξ) = c • normalSymbol ξ := by
  apply ContinuousLinearMap.ext
  intro a
  ext i
  fin_cases i <;> simp [normalSymbol_apply,symbol,UnitaryFrame.interior,UnitaryFrame.star] <;> ring

def symbolMap : V →L[ℝ] (W →L[ℝ] Q) :=
  LinearMap.toContinuousLinearMap {
    toFun := normalSymbol
    map_add' := normalSymbol_add_covector
    map_smul' := normalSymbol_smul_covector }

@[simp] lemma symbolMap_apply (ξ : V) : symbolMap ξ = normalSymbol ξ := rfl
end TamingCompatibility.HodgeNormalSymbol

namespace TamingCompatibility.GeometricHilbert.CoordinateOperator
open HodgeNormalSymbol EuclideanEnergy
open scoped RealInnerProductSpace ContDiff
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def firstOrder (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (u : V → W) (x : V) : Q :=
  (∑ i, a i x (fderiv ℝ u x (e i))) + b x (u x)

def pullCoefficient (a : Fin 4 → W →L[ℝ] Q) (C : V →L[ℝ] V) (j : Fin 4) :
    W →L[ℝ] Q := ∑ i, (C (e i) j) • a i

lemma basis_expansion (v : V) : v = ∑ i, v i • e i := by
  simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,e]
    using ((EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v).symm

lemma firstOrder_pull (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (u : V → W) (ψ : V → V) (x : V) (C : V →L[ℝ] V)
    (hψ : HasFDerivAt ψ C x) (hu : DifferentiableAt ℝ u (ψ x)) :
    firstOrder a b (u ∘ ψ) x =
      (∑ j, pullCoefficient (fun i => a i x) C j (fderiv ℝ u (ψ x) (e j))) +
        b x (u (ψ x)) := by
  rw [firstOrder,(hu.hasFDerivAt.comp x hψ).fderiv]
  congr 1
  simp only [ContinuousLinearMap.comp_apply]
  conv_lhs => arg 2; ext i; rw [basis_expansion (C (e i))]
  simp only [map_sum,map_smul,smul_apply,pullCoefficient,
    sum_apply]
  exact Finset.sum_comm

lemma pullCoefficient_symbol (b : Fin 4 → V) (C : V →L[ℝ] V) (j : Fin 4) :
    pullCoefficient (HodgeFrozenEnergy.coefficient b) C j =
      normalSymbol (WithLp.toLp 2 (fun k => C (b k) j)) := by
  have hξ : (WithLp.toLp 2 (fun k => C (b k) j) : V) =
      ∑ i, (C (e i) j) • LocalMatrixOperator.frameCovector b i := by
    ext k
    change C (b k) j = _
    conv_lhs => rw [basis_expansion (b k)]
    simp [LocalMatrixOperator.frameCovector,map_sum,map_smul,
      mul_comm]
  rw [hξ]
  change _ = symbolMap _
  simp only [map_sum,map_smul,symbolMap_apply]
  rfl

lemma pullCoefficient_polarized (b : Fin 4 → V) (C : V →L[ℝ] V) (i j : Fin 4) :
    (pullCoefficient (HodgeFrozenEnergy.coefficient b) C i).adjoint ∘L
        pullCoefficient (HodgeFrozenEnergy.coefficient b) C j +
      (pullCoefficient (HodgeFrozenEnergy.coefficient b) C j).adjoint ∘L
        pullCoefficient (HodgeFrozenEnergy.coefficient b) C i =
      (2 * ⟪(WithLp.toLp 2 (fun k => C (b k) i) : V),
        WithLp.toLp 2 (fun k => C (b k) j)⟫) • ContinuousLinearMap.id ℝ W := by
  simp only [pullCoefficient_symbol]
  exact normalSymbol_adjoint_polarized _ _

lemma pullCoefficient_contDiff (a : Fin 4 → V → W →L[ℝ] Q) (C : V → V →L[ℝ] V)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (hC : ContDiff ℝ ∞ C) (j : Fin 4) :
    ContDiff ℝ ∞ (fun x => pullCoefficient (fun i => a i x) (C x) j) := by
  apply ContDiff.sum
  intro i _
  exact ((EuclideanSpace.proj j).contDiff.comp (hC.clm_apply contDiff_const)).smul (ha i)

lemma intrinsic_firstOrder_pull
    {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
    (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p)
    (u : V → W) (ψ : V → V) (x : V) (C : V →L[ℝ] V)
    (hψ : HasFDerivAt ψ C x) (hu : DifferentiableAt ℝ u (ψ x)) :
    HodgeChart.normalOperator J α ht p D (u ∘ ψ) x =
      (∑ j, normalSymbol (WithLp.toLp 2 (fun k => C (D.frame k x) j))
          (fderiv ℝ u (ψ x) (e j))) + HodgeChart.normalB J α ht p D x (u (ψ x)) := by
  have h := firstOrder_pull (HodgeChart.normalA J α ht p D)
    (HodgeChart.normalB J α ht p D) u ψ x C hψ hu
  change HodgeChart.normalOperator J α ht p D (u ∘ ψ) x = _ at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [show (fun i => HodgeChart.normalA J α ht p D i x) =
    HodgeFrozenEnergy.coefficient (fun k => D.frame k x) from rfl,pullCoefficient_symbol]

end TamingCompatibility.GeometricHilbert.CoordinateOperator

namespace TamingCompatibility.GeometricHilbert.OrthogonalJets
open scoped RealInnerProductSpace ContDiff
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

abbrev End := W →L[ℝ] W

def gauge (A : V →L[ℝ] End (W := W)) (z : V) : End (W := W) := NormedSpace.exp (A z)

omit [CompleteSpace W] in
@[simp] lemma gauge_zero (A : V →L[ℝ] End (W := W)) : gauge A 0 = 1 := by
  simp [gauge]

lemma gauge_contDiff (A : V →L[ℝ] End (W := W)) : ContDiff ℝ ∞ (gauge A) := by
  apply ContDiff.comp _ A.contDiff
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (NormedSpace.exp_analytic (𝕂 := ℝ) z).contDiffAt

lemma gauge_hasFDerivAt_zero (A : V →L[ℝ] End (W := W)) :
    HasFDerivAt (gauge A) A 0 := by
  have he : HasFDerivAt (NormedSpace.exp : End (W := W) → End (W := W)) (ContinuousLinearMap.id ℝ _) (A 0) := by
    simpa using! (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := End (W := W)))
  simpa [gauge] using! he.comp 0 A.hasFDerivAt

lemma gauge_unitary (A : V →L[ℝ] End (W := W))
    (hA : ∀ z, (A z).adjoint = - A z) (z : V) : gauge A z ∈ unitary (End (W := W)) := by
  let _ : NormedAlgebra ℚ (End (W := W)) := NormedAlgebra.restrictScalars ℚ ℝ _
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  exact (skewAdjoint.mem_iff).mpr (hA z)

lemma gauge_inner (A : V →L[ℝ] End (W := W))
    (hA : ∀ z, (A z).adjoint = - A z) (z : V) (u v : W) :
    ⟪gauge A z u, gauge A z v⟫ = ⟪u,v⟫ := by
  exact ContinuousLinearMap.inner_map_map_of_mem_unitary (gauge_unitary A hA z) u v

lemma gauge_norm (A : V →L[ℝ] End (W := W))
    (hA : ∀ z, (A z).adjoint = - A z) (z : V) (u : W) : ‖gauge A z u‖ = ‖u‖ := by
  have h := gauge_inner A hA z u u
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (gauge A z u), norm_nonneg u]

end TamingCompatibility.GeometricHilbert.OrthogonalJets


end

end OAI
