import Mathlib
import OAI.Analysis.SymmetricDomains.CoordinateFieldLinear
import OAI.Analysis.SymmetricDomains.InnerExp

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
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology
open scoped TensorProduct
namespace Biholomorph

section
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

def coordinateFieldComplexLinear (e : Biholomorph U D) :
    (Affine n → Affine n) →ₗ[ℂ] (Affine m → Affine m) where
  toFun := coordinateField e
  map_add' X Y := (coordinateFieldLinear e).map_add X Y
  map_smul' c X := by
    funext x
    by_cases hx : x∈D
    · simp only [coordinateField,dite_eq_left hx,Pi.smul_apply,map_smul,RingHom.id_apply]
    · simp only [coordinateField,dite_eq_right hx,Pi.smul_apply,smul_zero,RingHom.id_apply]

variable (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

 theorem complexGeneratorField_lie (Z W : ComplexGenerators hU hc hbd Γ hhol) :
    complexGeneratorField hU hc hbd Γ hhol ⁅Z,W⁆ =
      VectorField.lieBracket ℂ (complexGeneratorField hU hc hbd Γ hhol Z)
        (complexGeneratorField hU hc hbd Γ hhol W) := by
  let F := complexGeneratorField hU hc hbd Γ hhol
  funext x
  by_cases hx : x∈U
  · have hd (Y : ComplexGenerators hU hc hbd Γ hhol) : DifferentiableAt ℂ (F Y) x :=
      (complexGeneratorField_analytic hU hc hbd Γ hhol Y x hx).differentiableAt
    change F ⁅Z,W⁆ x=VectorField.lieBracket ℂ (F Z) (F W) x
    induction Z using TensorProduct.inductionOn with
    | tmul z X =>
      induction W using TensorProduct.inductionOn with
      | tmul w Y =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul,F,complexGeneratorField_tmul,Pi.smul_apply]
        rw [VectorField.lieBracket_const_smul_left (X.property.analyticOnNhd hU hbd x hx).differentiableAt,
          VectorField.lieBracket_const_smul_right (Y.property.analyticOnNhd hU hbd x hx).differentiableAt]
        exact mul_smul z w (VectorField.lieBracket ℂ X.val Y.val x)
      | add W₁ W₂ ih₁ ih₂ =>
        rw [LieRing.lie_add,map_add,Pi.add_apply,ih₁,ih₂,map_add,VectorField.lieBracket_add_right (hd W₁) (hd W₂)]
    | add Z₁ Z₂ ih₁ ih₂ =>
      rw [add_lie,map_add,Pi.add_apply,ih₁,ih₂,map_add,VectorField.lieBracket_add_left (hd Z₁) (hd Z₂)]
  · simp only [VectorField.lieBracket,complexGeneratorField_zero_outside hU hc hbd Γ hhol _ hx,
      map_zero,sub_zero]

end

open scoped Classical
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

 theorem coordinateField_zeroSecondJet (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) {X : Affine n → Affine n} (hX : AnalyticOnNhd ℂ X U)
    (p : D) (hz : ZeroSecondJet X (e.toHomeomorph.symm p).val) :
    ZeroSecondJet (coordinateField e X) p.val := by
  let g := e.symm.ambientMap
  have hg : AnalyticAt ℂ g p.val := e.symm.ambientMap_analytic hD p.val p.property
  have he : g p.val=(e.toHomeomorph.symm p).val := ambientMap_apply e.symm p
  have hh : AnalyticAt ℂ e.ambientMap (g p.val) := by
    rw [he]; exact e.ambientMap_analytic hU _ (e.toHomeomorph.symm p).property
  have hx : AnalyticAt ℂ X (g p.val) := by
    rw [he]; exact hX _ (e.toHomeomorph.symm p).property
  rw [←he] at hz
  have hjet := ZeroSecondJet.clm_apply (hh.fderiv.comp hg) (hx.comp hg) (hz.comp hx hg)
  apply hjet.congr
  filter_upwards [hD.mem_nhds p.property] with x hx
  change (fderiv ℂ e.ambientMap (g x)) (X (g x))=coordinateField e X x
  rw [coordinateField_apply e X ⟨x,hx⟩]
  dsimp only [g]
  rw [ambientMap_apply e.symm ⟨x,hx⟩]
  rfl

variable (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

def modelComplexField (e : Biholomorph U D) :
    ComplexGenerators hU hc hbd Γ hhol →ₗ[ℂ] (Affine m → Affine m) :=
  (coordinateFieldComplexLinear e).comp (complexGeneratorField hU hc hbd Γ hhol)

 theorem modelComplexField_analytic (hD : IsOpen D) (e : Biholomorph U D)
    (Z : ComplexGenerators hU hc hbd Γ hhol) :
    AnalyticOnNhd ℂ (modelComplexField hU hc hbd Γ hhol e Z) D :=
  coordinateField_analytic hU hD e (complexGeneratorField_analytic hU hc hbd Γ hhol Z)

 theorem modelComplexField_lie (hD : IsOpen D) (e : Biholomorph U D)
    (Z W : ComplexGenerators hU hc hbd Γ hhol) :
    modelComplexField hU hc hbd Γ hhol e ⁅Z,W⁆ =
      VectorField.lieBracket ℂ (modelComplexField hU hc hbd Γ hhol e Z)
        (modelComplexField hU hc hbd Γ hhol e W) := by
  change coordinateField e (complexGeneratorField hU hc hbd Γ hhol ⁅Z,W⁆)=_
  rw [complexGeneratorField_lie]
  exact coordinateField_lieBracket hU hD e
    (complexGeneratorField_analytic hU hc hbd Γ hhol Z)
    (complexGeneratorField_analytic hU hc hbd Γ hhol W)

 theorem modelComplexField_secondJet_injective (hD : IsOpen D) (e : Biholomorph U D)
    (Z : ComplexGenerators hU hc hbd Γ hhol) (p : D)
    (hz : ZeroSecondJet (modelComplexField hU hc hbd Γ hhol e Z) p.val) : Z=0 := by
  have hjet := coordinateField_zeroSecondJet hD hU e.symm
    (modelComplexField_analytic hU hc hbd Γ hhol hD e Z) (e.toHomeomorph.symm p)
    (by
      change ZeroSecondJet _ (e.toHomeomorph (e.toHomeomorph.symm p)).val
      rwa [e.toHomeomorph.apply_symm_apply])
  change ZeroSecondJet (coordinateField e.symm
    (coordinateField e (complexGeneratorField hU hc hbd Γ hhol Z))) _ at hjet
  rw [coordinateField_symm_cancel hU hD e _
    (fun x hx => complexGeneratorField_zero_outside hU hc hbd Γ hhol Z hx)] at hjet
  exact complexGeneratorField_secondJet_injective hU hc hbd Γ hhol Z
    (e.toHomeomorph.symm p) hjet.1 hjet.2.1 hjet.2.2

end Biholomorph
end Release061

end

end OAI
