import Mathlib
import OAI.Analysis.SymmetricDomains.ImagPartLieReal

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
namespace Module.End
open scoped _root_.Module _root_.Module.End
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

 theorem trace_eq_sum_eigenspace_finrank (A : Module.End ℂ V) (hA : A.IsSemisimple)
    (s : Finset ℂ) (hs : ∀ μ, A.HasEigenvalue μ → μ∈s) :
    LinearMap.trace ℂ V A=∑ μ∈s, μ*(Module.finrank ℂ (A.eigenspace μ) : ℂ) := by
  classical
  let N : s → Submodule ℂ V := fun μ => A.eigenspace μ.val
  have hi : iSupIndep N := (_root_.Module.End.eigenspaces_iSupIndep A).comp Subtype.val_injective
  have htop : iSup N=⊤ := by
    rw [←hA.iSup_eigenspace_eq_top]
    apply le_antisymm
    · exact iSup_le fun μ => le_iSup (A.eigenspace) μ.val
    · apply iSup_le
      intro μ
      by_cases hm : μ∈s
      · exact le_iSup N ⟨μ,hm⟩
      · have hz : A.eigenspace μ=⊥ := by
          by_contra hn
          exact hm (hs μ hn)
        simp [hz]
  have hint : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N).mpr ⟨hi,htop⟩
  have hmaps (μ : s) : Set.MapsTo A (N μ) (N μ) := by
    intro x hx
    change x∈A.eigenspace μ.val at hx
    change A x∈A.eigenspace μ.val
    rw [_root_.Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hx,map_smul,hx]
  rw [←Finset.sum_coe_sort,LinearMap.trace_eq_sum_trace_restrict hint hmaps]
  apply Finset.sum_congr rfl
  intro μ _
  have he : A.restrict (hmaps μ)=μ.val • (LinearMap.id : N μ →ₗ[ℂ] N μ) := by
    ext x
    exact _root_.Module.End.mem_eigenspace_iff.mp x.property
  rw [he,map_smul,LinearMap.trace_id,smul_eq_mul]

 theorem five_weight_trace_balance (A : Module.End ℂ V) (hA : A.IsSemisimple)
    (hs : ∀ μ, A.HasEigenvalue μ → μ∈({-1,-(1/2),0,1/2,1} : Finset ℂ))
    (hz : LinearMap.trace ℂ V A=0)
    (hhalf : Module.finrank ℂ (A.eigenspace (1/2)) ≤ Module.finrank ℂ (A.eigenspace (-(1/2))))
    (hone : Module.finrank ℂ (A.eigenspace 1) ≤ Module.finrank ℂ (A.eigenspace (-1))) :
    Module.finrank ℂ (A.eigenspace (1/2)) = Module.finrank ℂ (A.eigenspace (-(1/2))) ∧
    Module.finrank ℂ (A.eigenspace 1) = Module.finrank ℂ (A.eigenspace (-1)) := by
  have he := trace_eq_sum_eigenspace_finrank A hA _ hs
  rw [hz] at he
  have hr := congrArg Complex.re he
  norm_num [Finset.sum_insert,Complex.mul_re,Complex.div_re] at hr
  have hh : (Module.finrank ℂ (A.eigenspace (1/2)) : ℝ) ≤ Module.finrank ℂ (A.eigenspace (-(1/2))) := by exact_mod_cast hhalf
  have ho : (Module.finrank ℂ (A.eigenspace 1) : ℝ) ≤ Module.finrank ℂ (A.eigenspace (-1)) := by exact_mod_cast hone
  constructor
  · have heq : (Module.finrank ℂ (A.eigenspace (1/2)) : ℝ)=Module.finrank ℂ (A.eigenspace (-(1/2))) := by linarith
    exact_mod_cast heq
  · have heq : (Module.finrank ℂ (A.eigenspace 1) : ℝ)=Module.finrank ℂ (A.eigenspace (-1)) := by linarith
    exact_mod_cast heq
end Module.End

open Filter Topology
open scoped TensorProduct

instance Complexification.ratLieAlgebra {G : Type*} [LieRing G] [LieAlgebra ℝ G] :
    LieAlgebra ℚ (ℂ ⊗[ℝ] G) where
  lie_smul t x y := by
    rw [←IsScalarTower.algebraMap_smul ℂ t y]
    exact (LieAlgebra.lie_smul (R := ℂ) ((algebraMap ℚ ℂ) t) x y).trans
      (IsScalarTower.algebraMap_smul ℂ t ⁅x,y⁆)

end

end OAI
