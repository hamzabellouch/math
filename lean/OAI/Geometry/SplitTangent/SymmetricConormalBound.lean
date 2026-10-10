import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.GlobalTensorVanishing
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.FormalBoxes
import OAI.Geometry.SplitTangent.TensorSectionSpace
import OAI.Geometry.SplitTangent.TensorSpanning

namespace OAI

/-! Symmetric Conormal Bound. -/

noncomputable section
open Set Filter Topology Bundle
open scoped Manifold ContDiff
universe u
namespace SplitTangent
namespace symmetricSupportedTensors
open DiagonalRationality
variable {X : ComplexManifold.{u}} {g : RationalCurve X} {S : TangentSplitting X}
  {d m r : ℕ}

 
def contractionJet (σ : Fin r → CurveTangentSection g) :
    symmetricSupportedTensors g S (d : ℤ) m →ₗ[ℂ]
      (SymmetricIndex.Sorted r m → Fin (d+1) → ℂ) :=
  LinearMap.pi fun j => (sectionJet (d : ℤ) d).comp
    ((tensorSectionSpace.contract (σ ∘ j.val)).comp
      (symmetricSupportedTensors g S (d : ℤ) m).subtype)

theorem contractionJet_injective (σ : Fin r → CurveTangentSection g)
    (hσ : ∀j z,(σ j).finite z∈S.first (g.finite z))
    (hspan : ∀v∈S.first (g.finite 1),∃a : Fin r → ℂ,∑j,a j • (σ j).finite 1=v) :
    Function.Injective (contractionJet (S := S) (d := d) (m := m) σ) := by
  let : AddCommGroup (symmetricSupportedTensors g S (d : ℤ) m) :=
    Module.addCommMonoidToAddCommGroup ℂ
  apply (injective_iff_map_eq_zero (contractionJet (S := S) (d := d) (m := m) σ)).mpr
  intro A hA
  have hc : ∀j : SymmetricIndex.Sorted r m,(tensorSectionSpace.toTensor A.val).contract (σ ∘ j.val)=0 := by
    intro j
    apply sectionJet_injective d
    have he := congrFun hA j
    simpa only [contractionJet,LinearMap.pi_apply,LinearMap.comp_apply,
      Submodule.subtype_apply,tensorSectionSpace.contract,map_zero,Pi.zero_apply,LinearMap.coe_mk,AddHom.coe_mk] using he
  have hc' : ∀j : Fin m → Fin r,(tensorSectionSpace.toTensor A.val).contract (σ ∘ j)=0 := by
    intro j
    apply lineSections_ext
    funext z
    apply SymmetricIndex.zero_of_sorted (fun v => A.val.val.1 z v)
      (fun j => (σ j).finite z) (A.property.2.2.1 z) _ j
    intro k
    exact congrArg (fun s : lineSections (d : ℤ) => s.val.1 z) (hc k)
  have hf := (tensorSectionSpace.toTensor A.val).finite_zero_of_spanning_sections S σ hσ hspan A.property.1 hc'
  have hi := (tensorSectionSpace.toTensor A.val).infinity_zero_of_finite_zero hf
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (funext hf) (funext hi)

 

theorem finite_and_finrank_le (hg : PointedGenerated g S.first) (d m : ℕ) :
    Module.Finite ℂ (symmetricSupportedTensors g S (d : ℤ) m) ∧
    Module.finrank ℂ (symmetricSupportedTensors g S (d : ℤ) m) ≤
      (Module.finrank ℂ (S.first (g.finite 1))+m-1).choose m * (d+1) := by
  obtain ⟨σ,hσ,hσi,hσ0,hspan⟩ := hg.exists_basis_sections
  have hj := contractionJet_injective (d := d) (m := m) σ hσ hspan
  let : Module.Finite ℂ (symmetricSupportedTensors g S (d : ℤ) m) :=
    Module.Finite.of_injective _ hj
  refine ⟨inferInstance,?_⟩
  have hb := LinearMap.finrank_le_finrank_of_injective hj
  have hcard := SymmetricIndex.card_le (Module.finrank ℂ (S.first (g.finite 1))) m
  exact hb.trans (by
    simpa only [Module.finrank_pi_fintype,Module.finrank_fin_fun,Module.finrank_self,Nat.mul_one,Finset.sum_const,Finset.card_univ,smul_eq_mul,Fintype.card_fin]
      using Nat.mul_le_mul_right (d+1) hcard)

 
theorem eq_zero_of_degree_lt_order (hg : PointedGenerated g S.first) (hdm : d < m)
    (A : symmetricSupportedTensors g S (d : ℤ) m) : A=0 := by
  have hf := (tensorSectionSpace.toTensor A.val).finite_zero_of_pointedGenerated S hg hdm A.property.1
  have hi := (tensorSectionSpace.toTensor A.val).infinity_zero_of_finite_zero hf
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (funext hf) (funext hi)

end symmetricSupportedTensors
end SplitTangent

end

end OAI
