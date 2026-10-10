import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ComplexSquare
import OAI.Geometry.TamingCompatibility.Elliptic.SquarePrincipal
import OAI.Geometry.TamingCompatibility.Functional.NormalPatch
import OAI.Geometry.TamingCompatibility.Hodge.HodgeFrameTest

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
variable {ι : Type*} {m : ℕ}
def fullPrincipalScalar (a : ι → 𝓢(D,R 6 →L[ℝ] R m)) (ρ : 𝓢(D,ℝ))
    (i j : ι) : 𝓢(D,ℂ) :=
  (1/2:ℂ) • (principalMatrix a ρ i j 0 0 + principalMatrix a ρ j i 0 0)

lemma fullPrincipalScalar_apply (a : ι → 𝓢(D,R 6 →L[ℝ] R m)) (ρ : 𝓢(D,ℝ))
    (g : ι → ι → D → ℝ)
    (h : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (i j : ι) (x : D) :
    fullPrincipalScalar a ρ i j x = (g i j x : ℂ) := by
  have he := entry_polarized (h i j x) (0 : Fin 6) (0 : Fin 6)
  simp only [ite_true,mul_one] at he
  simp only [fullPrincipalScalar,_root_.smul_apply,_root_.add_apply,principalMatrix_apply,
    smul_eq_mul,← Complex.ofReal_add,he,Complex.ofReal_mul,Complex.ofReal_ofNat]
  ring

lemma fullPrincipalMatrix_scalar (a : ι → 𝓢(D,R 6 →L[ℝ] R m)) (ρ : 𝓢(D,ℝ))
    (g : ι → ι → D → ℝ)
    (h : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (i j : ι) (k l : Fin 6) :
    principalMatrix a ρ i j k l + principalMatrix a ρ j i k l =
      scalarMatrix 6 (fullPrincipalScalar a ρ i j + fullPrincipalScalar a ρ i j) k l := by
  ext x
  have he := entry_polarized (h i j x) k l
  simp only [_root_.add_apply,principalMatrix_apply,← Complex.ofReal_add]
  rw [show entry k l ((ρ x • a i x).adjoint ∘L a j x) +
    entry k l ((ρ x • a j x).adjoint ∘L a i x) = (2*g i j x)*(if k=l then 1 else 0) from he]
  by_cases hkl : k=l
  · simp only [scalarMatrix,ite_eq_left hkl,_root_.add_apply,fullPrincipalScalar_apply a ρ g h,
      mul_one,Complex.ofReal_mul,Complex.ofReal_ofNat]
    ring
  · simp only [scalarMatrix,ite_eq_right hkl,_root_.zero_apply,mul_zero,Complex.ofReal_zero]

variable [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] [Fintype ι]
def fullWeightedAdj (ρ : 𝓢(D,ℝ)) (a : 𝓢(D,R 6 →L[ℝ] R m)) :
    Fin 6 → Fin m → 𝓢(D,ℂ) :=
  coefficient (LocalFormalAdjoint.adjointCoefficient (LocalFormalAdjoint.weightedCoefficient ρ a))

lemma full_square_scalar_expansion (e : ι → D) (a : ι → 𝓢(D,R 6 →L[ℝ] R m))
    (b : 𝓢(D,R 6 →L[ℝ] R m)) (ρ : 𝓢(D,ℝ)) (g : ι → ι → D → ℝ)
    (h : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (u : 𝓢'(D,C 6)) :
    square e a b ρ u =
      -(∑ i, ∑ j, smulLeftCLM (C 6) (fullPrincipalScalar a ρ i j) (∂_{e i} (∂_{e j} u))) +
      (∑ j, multiply (squareFirst e (fun i => coefficient (a i)) (coefficient b)
        (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b) j) (∂_{e j} u)) +
      multiply (squareZero e (coefficient b) (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b)) u := by
  simp only [square,formalAdjoint,firstOrder,_root_.add_apply,_root_.neg_apply,
    _root_.sum_apply,ContinuousLinearMap.comp_apply,lineDerivOpCLM_apply]
  rw [divergence_square_expansion]
  have hp := symmetrized_principal e (principalMatrix a ρ) (fullPrincipalScalar a ρ)
    (fullPrincipalMatrix_scalar a ρ g h) u
  simp only [principalMatrix] at hp
  rw [hp]
  rfl

end TamingCompatibility.ComplexMatrix

end
end

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge LocalMatrixOperator Set Filter LocalFormalAdjoint LineDeriv
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
variable {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

def patchA (i : Fin 4) : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q) :=
  SchwartzCutoff.schwartz D.domain_open (normalA_smooth J α ht p D i) hφ hc hφD

def patchB : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q) :=
  SchwartzCutoff.schwartz D.domain_open (normalB_smooth J α hs ht p D) hφ hc hφD

lemma patch_normal (q : 𝓢(Space,HodgeNormalSymbol.W))
    (hq : ∀ z ∈ tsupport q, φ z = 1) (z : Space) :
    firstOrder EuclideanEnergy.e (patchA J α ht p D hφ hc hφD)
      (patchB J α hs ht p D hφ hc hφD) q z = normalOperator J α ht p D q z := by
  by_cases hz : z ∈ tsupport q
  · simp only [firstOrder,_root_.add_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
      multiply_apply,patchA,patchB,SchwartzCutoff.schwartz_apply,hq z hz,one_smul,
      lineDerivOpCLM_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,normalOperator]
  · rw [normalOperator_zero_off J α ht p D q hz]
    have hd (i : Fin 4) : (∂_{EuclideanEnergy.e i} q : 𝓢(Space,HodgeNormalSymbol.W)) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz (SchwartzMap.tsupport_lineDerivOp_subset _ _ h))
    simp only [firstOrder,_root_.add_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
      multiply_apply,lineDerivOpCLM_apply,hd,image_eq_zero_of_notMem_tsupport hz,map_zero,
      Finset.sum_const_zero,add_zero]
end TamingCompatibility.HodgeChart

namespace TamingCompatibility.HodgeNormalSymbol
open EuclideanEnergy
open scoped RealInnerProductSpace
lemma normalSymbol_weighted_polarized (ρ c : ℝ) (ξ η : V) :
    (ρ • (c • normalSymbol ξ)).adjoint ∘L (c • normalSymbol η) +
      (ρ • (c • normalSymbol η)).adjoint ∘L (c • normalSymbol ξ) =
        (2 * (ρ*c*c*⟪ξ,η⟫)) • ContinuousLinearMap.id ℝ W := by
  apply ContinuousLinearMap.ext
  intro q
  apply ext_inner_left ℝ
  intro r
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,inner_add_right,
    ContinuousLinearMap.adjoint_inner_right,_root_.smul_apply,real_inner_smul_left,
    real_inner_smul_right,ContinuousLinearMap.id_apply]
  calc
    _ = (ρ*c*c) * (⟪normalSymbol ξ r,normalSymbol η q⟫ +
        ⟪normalSymbol η r,normalSymbol ξ q⟫) := by ring
    _ = _ := by rw [normalSymbol_polarized]; ring
end TamingCompatibility.HodgeNormalSymbol

namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge LocalMatrixOperator ComplexMatrix
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
variable {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

lemma patchA_polarized (ρ : 𝓢(Space,ℝ)) (i j : Fin 4) (z : Space) :
    (ρ z • patchA J α ht p D hφ hc hφD i z).adjoint ∘L patchA J α ht p D hφ hc hφD j z +
      (ρ z • patchA J α ht p D hφ hc hφD j z).adjoint ∘L patchA J α ht p D hφ hc hφD i z =
    (2*(ρ z*φ z*φ z*GeometricChart.normalMetric J α ht p D i j z)) • ContinuousLinearMap.id ℝ HodgeNormalSymbol.W :=
  HodgeNormalSymbol.normalSymbol_weighted_polarized (ρ z) (φ z) _ _

lemma patch_principal_apply (ρ : 𝓢(Space,ℝ)) (i j : Fin 4) (z : Space) :
    fullPrincipalScalar (patchA J α ht p D hφ hc hφD) ρ i j z =
      (ρ z*φ z*φ z*GeometricChart.normalMetric J α ht p D i j z : ℝ) :=
  fullPrincipalScalar_apply _ _ _ (patchA_polarized J α ht p D hφ hc hφD ρ) i j z

end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
