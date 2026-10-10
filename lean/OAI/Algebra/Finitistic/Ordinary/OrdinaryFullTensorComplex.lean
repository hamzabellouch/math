import OAI.Algebra.Finitistic.Ordinary.OrdinaryFullTensorTerms
import Mathlib.Algebra.Homology.Embedding.Restriction

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.FullTensorTerm
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)
attribute [local instance] VertexTensor.termScalar VertexTensor.termTower

def differential (n : ℕ) : FullTensorTerm P a l n →ₗ[Enveloping k B] FullTensorTerm P a l (n+1) :=
  TwoSidedTensor.map (T := Bᵐᵒᵖ) (N := BimoduleO P a l)
    (TensorResolution.differential k B l n) (TensorResolution.differential_left k B l n)

theorem differential_square (n : ℕ) : (differential P a l (n+1)).comp (differential P a l n) = 0 := by
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro m v
  change BalancedTensor.mk k (B ⊗[k] ChainAlgebra k l) (TensorResolution.term k B l (n+2))
    (BimoduleO P a l) (TensorResolution.differential k B l (n+1)
      (TensorResolution.differential k B l n m)) v = 0
  have h := congrArg (fun f => f m) (TensorResolution.differential_square k B l n)
  change TensorResolution.differential k B l (n+1) (TensorResolution.differential k B l n m) = 0 at h
  rw [h,map_zero,LinearMap.zero_apply]

/-- Actual tensor complex, with both B-actions and the actual extended arrow maps. -/
def complex : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of _ (FullTensorTerm P a l n))
    (fun n => ModuleCat.ofHom (differential P a l n))
    (fun n => ModuleCat.hom_ext (differential_square P a l n))

/-- Supported evaluation is the product action followed by the source coordinate projection. -/
theorem supportedEquiv_mk (n : ℕ) (hn : n ≤ l) (m : TensorResolution.term k B l n) (v : BimoduleO P a l) :
    supportedEquiv P a l n hn
      (TwoSidedTensor.mk k (B ⊗[k] ChainAlgebra k l) B Bᵐᵒᵖ (TensorResolution.term k B l n) (BimoduleO P a l) m v) =
        (m.val • v : BimoduleO P a l) ⟨n,by omega⟩ := rfl

theorem supported_differential (n : ℕ) (hn : n+1 ≤ l) (z : FullTensorTerm P a l n) :
    supportedEquiv P a l (n+1) hn (differential P a l n z) =
      (P.d (a+(n:ℤ)) (a+((n+1:ℕ):ℤ))).hom (supportedEquiv P a l n (by omega) z) := by
  have h : (supportedEquiv P a l (n+1) hn).toLinearMap.comp (differential P a l n) =
      (P.d (a+(n:ℤ)) (a+((n+1:ℕ):ℤ))).hom.comp
        (supportedEquiv P a l n (by omega)).toLinearMap := by
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro m v
    change ((((1:B) ⊗ₜ[k] ChainAlgebra.extendedArrow k l n) * m.val) • v : BimoduleO P a l) ⟨n+1,by omega⟩ =
      (P.d (a+(n:ℤ)) (a+((n+1:ℕ):ℤ))).hom ((m.val • v : BimoduleO P a l) ⟨n,by omega⟩)
    have hv : (((1:B) ⊗ₜ[k] ChainAlgebra.extendedArrow k l n) * m.val) • v =
        ChainAlgebra.arrow k l ⟨n,by omega⟩ • (m.val • v) := by
      rw [mul_smul,BimoduleO.tensor_smul,one_smul,ChainAlgebra.extendedArrow,dite_eq_left (by omega)]
    exact (congrArg (fun w : BimoduleO P a l => w ⟨n+1,by omega⟩) hv).trans
      (VertexTensor.arrow_coordinate P a l ⟨n,by omega⟩ (m.val • v))
  exact congrArg (fun f => f z) h

variable (hP : ∀ n : ℕ, l < n → IsZero (P.X (a+(n:ℤ))))

theorem termEquiv_differential (n : ℕ) (z : FullTensorTerm P a l n) :
    termEquiv P a l hP (n+1) (differential P a l n z) =
      (P.d (a+(n:ℤ)) (a+((n+1:ℕ):ℤ))).hom (termEquiv P a l hP n z) := by
  by_cases hn : n+1 ≤ l
  · simp only [termEquiv,dite_eq_left hn,dite_eq_left (show n ≤ l by omega)]
    exact supported_differential P a l n hn z
  · let : Subsingleton (P.X (a+((n+1:ℕ):ℤ))) :=
      ModuleCat.isZero_iff_subsingleton.mp (hP (n+1) (by omega))
    exact Subsingleton.elim _ _

/-- The entire actual tensor complex identifies with P on degrees a,a+1,... . -/
def complexIso : complex P a l ≅ P.restriction (ComplexShape.embeddingUpIntGE a) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (termEquiv P a l hP n).toModuleIso) (by
    intro n m hnm
    change n+1=m at hnm
    subst m
    change (termEquiv P a l hP n).toModuleIso.hom ≫ P.d (a+(n:ℤ)) (a+((n+1:ℕ):ℤ)) =
      CochainComplex.of.d (fun j => ModuleCat.of (Enveloping k B) (FullTensorTerm P a l j))
        (fun j => ModuleCat.ofHom (differential P a l j)) n (n+1) ≫ (termEquiv P a l hP (n+1)).toModuleIso.hom
    rw [CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (termEquiv_differential P a l hP n z).symm)
end LittleFinitistic.OrdinarySimulation.FullTensorTerm

end

end OAI
