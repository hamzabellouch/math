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
namespace Release061
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

abbrev ComplexGenerators := ℂ ⊗[ℝ] completeGeneratorSpace hU hc hbd Γ hhol

def complexGeneratorField : ComplexGenerators hU hc hbd Γ hhol →ₗ[ℂ] (Affine n → Affine n) :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ _ (completeGeneratorSpace hU hc hbd Γ hhol).subtype)

@[simp] theorem complexGeneratorField_tmul (z : ℂ) (X : completeGeneratorSpace hU hc hbd Γ hhol) :
    complexGeneratorField hU hc hbd Γ hhol (z ⊗ₜ[ℝ] X)=z • X.val := rfl

 theorem complexGeneratorField_analytic (Z : ComplexGenerators hU hc hbd Γ hhol) :
    AnalyticOnNhd ℂ (complexGeneratorField hU hc hbd Γ hhol Z) U := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp only [map_add,complexGeneratorField_tmul,one_smul]
  intro p hp
  exact (X.property.analyticOnNhd hU hbd p hp).add (Y.property.analyticOnNhd hU hbd p hp).const_smul

 theorem complexGeneratorField_zero_outside (Z : ComplexGenerators hU hc hbd Γ hhol)
    {x : Affine n} (hx : x∉U) : complexGeneratorField hU hc hbd Γ hhol Z x=0 := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp only [map_add,complexGeneratorField_tmul,one_smul,Pi.add_apply,Pi.smul_apply,
    X.property.eq_zero_of_not_mem hx,Y.property.eq_zero_of_not_mem hx,smul_zero,add_zero]

 theorem complexGeneratorField_secondJet_injective (Z : ComplexGenerators hU hc hbd Γ hhol)
    (p : U) (h0 : complexGeneratorField hU hc hbd Γ hhol Z p.val=0)
    (h1 : fderiv ℂ (complexGeneratorField hU hc hbd Γ hhol Z) p.val=0)
    (h2 : fderiv ℂ (fderiv ℂ (complexGeneratorField hU hc hbd Γ hhol Z)) p.val=0) : Z=0 := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp only [map_add,complexGeneratorField_tmul,one_smul] at h0 h1 h2
  obtain ⟨hX,hY⟩ := complex_complete_generators_secondJet_zero hU hc hbd Γ hhol
    X.property Y.property p h0 h1 h2
  have hx : X=0 := Subtype.ext hX
  have hy : Y=0 := Subtype.ext hY
  simp [hx,hy]

 theorem complexGeneratorField_injective :
    Function.Injective (complexGeneratorField hU hc hbd Γ hhol) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro Z hZ
  obtain ⟨p,hp⟩ := hc.nonempty
  apply complexGeneratorField_secondJet_injective hU hc hbd Γ hhol Z ⟨p,hp⟩
  · rw [hZ]; rfl
  · rw [hZ,fderiv_zero]; rfl
  · rw [hZ,fderiv_zero,fderiv_zero]; rfl

end Biholomorph
end Release061

open scoped TensorProduct
namespace LieAlgebra
open scoped _root_.LieAlgebra
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

def leftInner (T : L) : LieDerivation ℂ L L where
  toLinearMap := LieAlgebra.ad ℂ L T
  leibniz' a b := by
    change ⁅T,⁅a,b⁆⁆=⁅a,⁅T,b⁆⁆-⁅b,⁅T,a⁆⁆
    rw [leibniz_lie,←lie_skew ⁅T,a⁆ b]
    abel

@[simp] theorem leftInner_apply (T X : L) : leftInner T X=⁅T,X⁆ := rfl

@[simp] theorem leftInner_toLinearMap (T : L) :
    (leftInner T).toLinearMap=LieAlgebra.ad ℂ L T := rfl

variable [LieAlgebra ℚ L]

def innerExp (T : L) (hT : IsNilpotent (LieAlgebra.ad ℂ L T)) (c : ℂ) : L ≃ₗ⁅ℂ⁆ L :=
  (c • leftInner T).exp (hT.smul c)

 theorem innerExp_apply_of_square_zero (T : L) (hT : IsNilpotent (LieAlgebra.ad ℂ L T))
    (c : ℂ) (X : L) (hX : ⁅T,⁅T,X⁆⁆=0) : innerExp T hT c X=X+c • ⁅T,X⁆ := by
  let A := c • LieAlgebra.ad ℂ L T
  have hn : IsNilpotent A := hT.smul c
  have hs : (A^2) • X=0 := by
    change A (A X)=0
    simp [A,hX]
  change IsNilpotent.exp A X=_
  have he := IsNilpotent.exp_smul_eq_sum hs hn
  change IsNilpotent.exp A X= _ at he
  rw [he]
  simp [Finset.sum_range_succ,A,Module.End.smul_def]

 theorem innerExp_euler (T E : L) (hT : IsNilpotent (LieAlgebra.ad ℂ L T))
    (hTE : ⁅T,E⁆=T) (c : ℂ) : innerExp T hT c E=E+c • T := by
  rw [innerExp_apply_of_square_zero T hT c E (by rw [hTE,lie_self]),hTE]

 theorem innerExp_fixed (T : L) (hT : IsNilpotent (LieAlgebra.ad ℂ L T))
    (c : ℂ) (X : L) (hTX : ⁅T,X⁆=0) : innerExp T hT c X=X := by
  rw [innerExp_apply_of_square_zero T hT c X (by rw [hTX,lie_zero]),hTX,smul_zero,add_zero]

end LieAlgebra

open scoped TensorProduct

end

end OAI
