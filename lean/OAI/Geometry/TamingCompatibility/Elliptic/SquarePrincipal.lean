import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.ComplexScalarPrincipal

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
variable {ι : Type*} {m n : ℕ}

def principalMatrix (a : ι → 𝓢(D,R n →L[ℝ] R m)) (ρ : 𝓢(D,ℝ))
    (i j : ι) : Fin n → Fin n → 𝓢(D,ℂ) :=
  matProduct (coefficient (LocalFormalAdjoint.adjointCoefficient
    (LocalFormalAdjoint.weightedCoefficient ρ (a i)))) (coefficient (a j))

lemma principalMatrix_apply (a : ι → 𝓢(D,R n →L[ℝ] R m)) (ρ : 𝓢(D,ℝ))
    (i j : ι) (k l : Fin n) (x : D) :
    principalMatrix a ρ i j k l x =
      (entry k l ((ρ x • a i x).adjoint ∘L a j x) : ℂ) := by
  rw [principalMatrix,matProduct_coefficient_apply,LocalFormalAdjoint.adjointCoefficient_apply,
    LocalFormalAdjoint.weightedCoefficient_apply ρ ρ.hasTemperateGrowth]

def principalScalar (a : ι → 𝓢(D,R 2 →L[ℝ] R m)) (ρ : 𝓢(D,ℝ))
    (i j : ι) : 𝓢(D,ℂ) :=
  (1/2:ℂ) • (principalMatrix a ρ i j 0 0 + principalMatrix a ρ j i 0 0)

lemma entry_polarized {S T : R n →L[ℝ] R n} {q : ℝ}
    (h : S+T = q • ContinuousLinearMap.id ℝ (R n)) (k l : Fin n) :
    entry k l S + entry k l T = q * (if k=l then 1 else 0) := by
  rw [← (entry k l).map_add,h,(entry k l).map_smul]
  congr 1
  simp only [entry_apply,ContinuousLinearMap.id_apply,PiLp.single_apply]

lemma principalScalar_apply (a : ι → 𝓢(D,R 2 →L[ℝ] R m)) (ρ : 𝓢(D,ℝ))
    (g : ι → ι → D → ℝ)
    (h : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 2)) (i j : ι) (x : D) :
    principalScalar a ρ i j x = (g i j x : ℂ) := by
  have he := entry_polarized (h i j x) (0 : Fin 2) (0 : Fin 2)
  simp only [ite_true,mul_one] at he
  simp only [principalScalar,_root_.smul_apply,_root_.add_apply,principalMatrix_apply,
    smul_eq_mul,← Complex.ofReal_add,he,Complex.ofReal_mul,Complex.ofReal_ofNat]
  ring

lemma principalMatrix_scalar (a : ι → 𝓢(D,R 2 →L[ℝ] R m)) (ρ : 𝓢(D,ℝ))
    (g : ι → ι → D → ℝ)
    (h : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 2)) (i j : ι) (k l : Fin 2) :
    principalMatrix a ρ i j k l + principalMatrix a ρ j i k l =
      scalarMatrix 2 (principalScalar a ρ i j + principalScalar a ρ i j) k l := by
  ext x
  have he := entry_polarized (h i j x) k l
  simp only [_root_.add_apply,principalMatrix_apply,← Complex.ofReal_add]
  rw [show entry k l ((ρ x • a i x).adjoint ∘L a j x) +
    entry k l ((ρ x • a j x).adjoint ∘L a i x) = (2*g i j x)*(if k=l then 1 else 0) from he]
  by_cases hkl : k=l
  · simp only [scalarMatrix,ite_eq_left hkl,_root_.add_apply,principalScalar_apply a ρ g h,
      mul_one,Complex.ofReal_mul,Complex.ofReal_ofNat]
    ring
  · simp only [scalarMatrix,ite_eq_right hkl,_root_.zero_apply,mul_zero,Complex.ofReal_zero]

variable [Fintype ι]

lemma first_zero_is_matrixLower (e : ι → D) (b : ι → Fin n → Fin n → 𝓢(D,ℂ))
    (c : Fin n → Fin n → 𝓢(D,ℂ)) (u : 𝓢'(D,C n)) :
    (∑ i, multiply (b i) (∂_{e i} u)) + multiply c u =
      matrixLowerOrder (fun t : ι × Fin n × Fin n => b t.1 t.2.1 t.2.2)
        (fun t => unit n n t.2.1 t.2.2) (fun t => e t.1)
        (fun t : Fin n × Fin n => c t.1 t.2) (fun t => unit n n t.1 t.2) u := by
  simp only [matrixLowerOrder,Fintype.sum_prod_type,multiply,_root_.sum_apply,
    ContinuousLinearMap.comp_apply]

end TamingCompatibility.ComplexMatrix

namespace TamingCompatibility.LocalMatrixOperator
open EuclideanEnergy
open scoped RealInnerProductSpace
lemma normalSymbol_weighted_polarized (ρ c : ℝ) (ξ η : V) :
    (ρ • (c • normalSymbol ξ)).adjoint ∘L (c • normalSymbol η) +
      (ρ • (c • normalSymbol η)).adjoint ∘L (c • normalSymbol ξ) =
        (2 * (ρ*c*c*⟪ξ,η⟫)) • ContinuousLinearMap.id ℝ Pair := by
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
end TamingCompatibility.LocalMatrixOperator

end

end OAI
