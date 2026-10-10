import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ComplexSquare
import OAI.Geometry.TamingCompatibility.Elliptic.SquarePrincipal
import OAI.Geometry.TamingCompatibility.Functional.NormalPatch

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
variable {ι : Type*} [Fintype ι] {m : ℕ}

def weightedAdj (ρ : 𝓢(D,ℝ)) (a : 𝓢(D,R 2 →L[ℝ] R m)) :
    Fin 2 → Fin m → 𝓢(D,ℂ) :=
  coefficient (LocalFormalAdjoint.adjointCoefficient (LocalFormalAdjoint.weightedCoefficient ρ a))

lemma square_scalar_expansion (e : ι → D) (a : ι → 𝓢(D,R 2 →L[ℝ] R m))
    (b : 𝓢(D,R 2 →L[ℝ] R m)) (ρ : 𝓢(D,ℝ)) (g : ι → ι → D → ℝ)
    (h : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 2)) (u : 𝓢'(D,C 2)) :
    square e a b ρ u =
      -(∑ i, ∑ j, smulLeftCLM (C 2) (principalScalar a ρ i j) (∂_{e i} (∂_{e j} u))) +
      (∑ j, multiply (squareFirst e (fun i => coefficient (a i)) (coefficient b)
        (fun i => weightedAdj ρ (a i)) (weightedAdj ρ b) j) (∂_{e j} u)) +
      multiply (squareZero e (coefficient b) (fun i => weightedAdj ρ (a i)) (weightedAdj ρ b)) u := by
  simp only [square,formalAdjoint,firstOrder,_root_.add_apply,_root_.neg_apply,
    _root_.sum_apply,ContinuousLinearMap.comp_apply,lineDerivOpCLM_apply]
  rw [divergence_square_expansion]
  have hp := symmetrized_principal e (principalMatrix a ρ) (principalScalar a ρ)
    (principalMatrix_scalar a ρ g h) u
  simp only [principalMatrix] at hp
  rw [hp]
  rfl

end TamingCompatibility.ComplexMatrix

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge LocalMatrixOperator ComplexMatrix
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : Data J α ht p)
variable {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

lemma patchA_polarized (ρ : 𝓢(Space,ℝ)) (i j : Fin 4) (z : Space) :
    (ρ z • patchA J α ht p D hφ hc hφD i z).adjoint ∘L patchA J α ht p D hφ hc hφD j z +
      (ρ z • patchA J α ht p D hφ hc hφD j z).adjoint ∘L patchA J α ht p D hφ hc hφD i z =
    (2*(ρ z*φ z*φ z*normalMetric J α ht p D i j z)) • ContinuousLinearMap.id ℝ EuclideanEnergy.Pair :=
  normalSymbol_weighted_polarized (ρ z) (φ z) _ _

lemma patch_principal_apply (ρ : 𝓢(Space,ℝ)) (i j : Fin 4) (z : Space) :
    principalScalar (patchA J α ht p D hφ hc hφD) ρ i j z =
      (ρ z*φ z*φ z*normalMetric J α ht p D i j z : ℝ) :=
  principalScalar_apply _ _ _ (patchA_polarized J α ht p D hφ hc hφD ρ) i j z

end TamingCompatibility.GeometricChart

end

end OAI
