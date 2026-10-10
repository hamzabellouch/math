import Mathlib
import OAI.Analysis.SymmetricDomains.RatLieAlgebra
import OAI.Analysis.SymmetricDomains.OneKernel

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
namespace Release061.Biholomorph.WeightedLieModel
variable {r k : ℕ} {G : Type*} [LieRing G] [LieAlgebra ℝ G]
    (M : WeightedLieModel r k G)

abbrev grade (μ : ℂ) := (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] G) M.E).eigenspace μ

def lowerHalf : M.grade (1/2) →ₗ[ℂ] M.grade (-(1/2)) where
  toFun X := ⟨⁅M.T,X.val⁆,by
    rw [Module.End.mem_eigenspace_iff]
    have he := M.bracket_translation_eigen (Module.End.mem_eigenspace_iff.mp X.property)
    convert he using 1 <;> norm_num⟩
  map_add' X Y := Subtype.ext (by simp [LieRing.lie_add])
  map_smul' c X := Subtype.ext (by
    change ⁅M.T,c • X.val⁆=c • ⁅M.T,X.val⁆
    exact LieAlgebra.lie_smul c M.T X.val)

def lowerOneSquared : M.grade 1 →ₗ[ℂ] M.grade (-1) where
  toFun X := ⟨⁅M.T,⁅M.T,X.val⁆⁆,by
    rw [Module.End.mem_eigenspace_iff]
    have he := M.bracket_translation_eigen
      (M.bracket_translation_eigen (Module.End.mem_eigenspace_iff.mp X.property))
    convert he using 1 <;> norm_num⟩
  map_add' X Y := Subtype.ext (by simp [LieRing.lie_add])
  map_smul' c X := Subtype.ext (by
    change ⁅M.T,⁅M.T,c • X.val⁆⁆=c • ⁅M.T,⁅M.T,X.val⁆⁆
    rw [LieAlgebra.lie_smul c M.T X.val,LieAlgebra.lie_smul c M.T ⁅M.T,X.val⁆])

theorem lowerHalf_injective : Function.Injective M.lowerHalf := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro X hX
  apply Subtype.ext
  exact M.half_kernel (Module.End.mem_eigenspace_iff.mp X.property) (congrArg Subtype.val hX)

theorem lowerOneSquared_injective : Function.Injective M.lowerOneSquared := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro X hX
  apply Subtype.ext
  exact M.one_kernel (Module.End.mem_eigenspace_iff.mp X.property) (congrArg Subtype.val hX)

variable [FiniteDimensional ℝ G]

theorem complex_euler_trace_zero (htrace : LinearMap.trace ℝ G (LieAlgebra.ad ℝ G M.euler)=0) :
    LinearMap.trace ℂ (ℂ ⊗[ℝ] G) (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] G) M.E)=0 := by
  rw [Complexification.ad_ofReal_baseChange,LinearMap.trace_baseChange,htrace,map_zero]

theorem grading_balance (htrace : LinearMap.trace ℝ G (LieAlgebra.ad ℝ G M.euler)=0) :
    Module.finrank ℂ (M.grade (1/2))=Module.finrank ℂ (M.grade (-(1/2))) ∧
    Module.finrank ℂ (M.grade 1)=Module.finrank ℂ (M.grade (-1)) := by
  apply Module.End.five_weight_trace_balance _ M.euler_semisimple M.euler_spectrum
    (M.complex_euler_trace_zero htrace)
  · exact LinearMap.finrank_le_finrank_of_injective M.lowerHalf_injective
  · exact LinearMap.finrank_le_finrank_of_injective M.lowerOneSquared_injective

theorem lowerOneSquared_surjective (htrace : LinearMap.trace ℝ G (LieAlgebra.ad ℝ G M.euler)=0) :
    Function.Surjective M.lowerOneSquared :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (M.grading_balance htrace).2).mp
    M.lowerOneSquared_injective

theorem exists_positive_real (htrace : LinearMap.trace ℝ G (LieAlgebra.ad ℝ G M.euler)=0) :
    ∃ V : G, ⁅M.euler,V⁆=V ∧ ⁅M.translation,⁅M.translation,V⁆⁆=(-2 : ℝ) • M.translation := by
  have ht : (-2 : ℂ) • M.T∈M.grade (-1) := by
    rw [Module.End.mem_eigenspace_iff]
    change ⁅M.E,(-2 : ℂ) • M.T⁆= -1 • ((-2 : ℂ) • M.T)
    rw [LieAlgebra.lie_smul (-2 : ℂ) M.E M.T,←lie_skew M.E M.T,M.translation_euler]
    module
  obtain ⟨V,hV⟩ := M.lowerOneSquared_surjective htrace ⟨_,ht⟩
  refine ⟨Complexification.realPart V.val,?_,?_⟩
  · have he := Complexification.realPart_eigen M.euler 1
      (by simpa using (Module.End.mem_eigenspace_iff.mp V.property))
    simpa using he
  · have he : ⁅M.T,⁅M.T,V.val⁆⁆=(-2 : ℂ) • M.T := congrArg Subtype.val hV
    have hr := congrArg Complexification.realPart he
    rw [show (-2 : ℂ)=((-2 : ℝ) : ℂ) by norm_num] at hr
    simpa only [T,Complexification.realPart_lie_ofReal,Complexification.realPart_real_smul,
      Complexification.realPart_ofReal] using hr
end Release061.Biholomorph.WeightedLieModel

open scoped TensorProduct

end

end OAI
