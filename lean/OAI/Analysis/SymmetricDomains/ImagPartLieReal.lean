import Mathlib
import OAI.Analysis.SymmetricDomains.ComplexTensorNormalForm

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
namespace Complexification
section Linear
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def realPart : (ℂ ⊗[ℝ] V) →ₗ[ℝ] V :=
  (TensorProduct.lid ℝ V).toLinearMap.comp
    (TensorProduct.map Complex.reLm (LinearMap.id : V →ₗ[ℝ] V))
def imagPart : (ℂ ⊗[ℝ] V) →ₗ[ℝ] V :=
  (TensorProduct.lid ℝ V).toLinearMap.comp
    (TensorProduct.map Complex.imLm (LinearMap.id : V →ₗ[ℝ] V))
def ofReal : V →ₗ[ℝ] (ℂ ⊗[ℝ] V) := TensorProduct.mk ℝ ℂ V 1

@[simp] theorem realPart_tmul (z : ℂ) (X : V) : realPart (z ⊗ₜ[ℝ] X)=z.re • X := rfl
@[simp] theorem imagPart_tmul (z : ℂ) (X : V) : imagPart (z ⊗ₜ[ℝ] X)=z.im • X := rfl
@[simp] theorem ofReal_apply (X : V) : ofReal X=1 ⊗ₜ[ℝ] X := rfl
@[simp] theorem realPart_ofReal (X : V) : realPart (ofReal X)=X := by simp
@[simp] theorem imagPart_ofReal (X : V) : imagPart (ofReal X)=0 := by simp

theorem ofReal_injective : Function.Injective (ofReal : V →ₗ[ℝ] _) :=
  Function.LeftInverse.injective realPart_ofReal

theorem normalForm (Z : ℂ ⊗[ℝ] V) : Z=ofReal (realPart Z)+Complex.I • ofReal (imagPart Z) := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp [TensorProduct.smul_tmul']

@[ext] theorem ext {Z W : ℂ ⊗[ℝ] V} (hr : realPart Z=realPart W)
    (hi : imagPart Z=imagPart W) : Z=W := by
  rw [normalForm Z,normalForm W,hr,hi]

@[simp] theorem realPart_I_smul (Z : ℂ ⊗[ℝ] V) : realPart (Complex.I • Z) = -imagPart Z := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp [smul_add,TensorProduct.smul_tmul']
@[simp] theorem imagPart_I_smul (Z : ℂ ⊗[ℝ] V) : imagPart (Complex.I • Z) = realPart Z := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp [smul_add,TensorProduct.smul_tmul']

@[simp] theorem realPart_real_smul (c : ℝ) (Z : ℂ ⊗[ℝ] V) :
    realPart ((c : ℂ) • Z)=c • realPart Z := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp [smul_add,TensorProduct.smul_tmul',Complex.mul_re]
@[simp] theorem imagPart_real_smul (c : ℝ) (Z : ℂ ⊗[ℝ] V) :
    imagPart ((c : ℂ) • Z)=c • imagPart Z := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp [smul_add,TensorProduct.smul_tmul',Complex.mul_im]

end Linear
variable {V : Type*} [LieRing V] [LieAlgebra ℝ V]
@[simp] theorem ofReal_lie (X Y : V) : ofReal ⁅X,Y⁆=⁅ofReal X,ofReal Y⁆ := by
  simp [ofReal,LieAlgebra.ExtendScalars.bracket_tmul]

theorem ad_ofReal_baseChange (X : V) :
    LieAlgebra.ad ℂ (ℂ ⊗[ℝ] V) (ofReal X)=
    (LieAlgebra.ad ℝ V X).baseChange ℂ := by
  exact LieModule.toEnd_baseChange ℝ ℂ V V X

theorem ad_ofReal_nilpotent (X : V) (hX : IsNilpotent (LieAlgebra.ad ℝ V X)) :
    IsNilpotent (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] V) (ofReal X)) := by
  rw [ad_ofReal_baseChange]
  exact hX.map (Module.End.baseChangeHom ℝ ℂ V)

@[simp] theorem realPart_lie_ofReal (X : V) (Z : ℂ ⊗[ℝ] V) :
    realPart ⁅ofReal X,Z⁆=⁅X,realPart Z⁆ := by
  obtain ⟨Y,W,rfl⟩ := complex_tensor_normalForm Z
  simp [ofReal,LieRing.lie_add,LieAlgebra.ExtendScalars.bracket_tmul]
@[simp] theorem imagPart_lie_ofReal (X : V) (Z : ℂ ⊗[ℝ] V) :
    imagPart ⁅ofReal X,Z⁆=⁅X,imagPart Z⁆ := by
  obtain ⟨Y,W,rfl⟩ := complex_tensor_normalForm Z
  simp [ofReal,LieRing.lie_add,LieAlgebra.ExtendScalars.bracket_tmul]

 theorem realPart_eigen (E : V) (μ : ℝ) {Z : ℂ ⊗[ℝ] V}
    (hZ : ⁅ofReal E,Z⁆=(μ : ℂ) • Z) : ⁅E,realPart Z⁆=μ • realPart Z := by
  simpa only [realPart_lie_ofReal,realPart_real_smul] using congrArg realPart hZ
 theorem imagPart_eigen (E : V) (μ : ℝ) {Z : ℂ ⊗[ℝ] V}
    (hZ : ⁅ofReal E,Z⁆=(μ : ℂ) • Z) : ⁅E,imagPart Z⁆=μ • imagPart Z := by
  simpa only [imagPart_lie_ofReal,imagPart_real_smul] using congrArg imagPart hZ

 theorem eigen_eq_zero_of_imaginary_bracket (E H : V) (μ : ℝ)
    (h : ∀ Z : ℂ ⊗[ℝ] V, ⁅ofReal E,Z⁆=(μ : ℂ) • Z →
      ⁅ofReal H,Z⁆=Complex.I • Z) {Z : ℂ ⊗[ℝ] V}
    (hZ : ⁅ofReal E,Z⁆=(μ : ℂ) • Z) : Z=0 := by
  have hz (X : V) (hX : ⁅E,X⁆=μ • X) : X=0 := by
    have he : ⁅ofReal E,ofReal X⁆=(μ : ℂ) • ofReal X := by
      rw [←ofReal_lie,hX,map_smul]
      exact (IsScalarTower.algebraMap_smul ℂ μ (ofReal X)).symm
    have hh := congrArg imagPart (h (ofReal X) he)
    simpa using hh.symm
  have hr := hz (realPart Z) (realPart_eigen E μ hZ)
  have hi := hz (imagPart Z) (imagPart_eigen E μ hZ)
  rw [normalForm Z,hr,hi,map_zero,smul_zero,add_zero]
end Complexification

open Filter Topology

end

end OAI
