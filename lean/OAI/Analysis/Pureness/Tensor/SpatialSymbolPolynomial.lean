import OAI.Analysis.Pureness.Tensor.SpatialSubgroupPolynomial

namespace OAI
noncomputable section
namespace CuntzPureness
local instance spatialSymbolPolynomialDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
open scoped InnerProductSpace
variable {A H V G : Type*} [Group G] [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

def groupPolynomialWeight (c : G → ℂ) : (G →₀ A) →ₗ[ℂ] (G →₀ A) :=
  Finsupp.lsum ℂ (fun g => c g • Finsupp.lsingle g)

omit [Group G] in
lemma groupPolynomialWeight_apply (c : G → ℂ) (a : G →₀ A) (g : G) :
    groupPolynomialWeight c a g = c g • a g := by
  classical
  simp only [groupPolynomialWeight, Finsupp.lsum_apply, Finsupp.sum,
    LinearMap.smul_apply, Finsupp.lsingle_apply, Finsupp.smul_single,
    Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single g]
  · simp
  · intro h hh hne
    exact Finsupp.single_eq_of_ne hne.symm
  · intro hg
    simp [Finsupp.notMem_support_iff.mp hg]

omit [Group G] in
lemma groupPolynomialWeight_single (c : G → ℂ) (g : G) (a : A) :
    groupPolynomialWeight c (Finsupp.single g a) = Finsupp.single g (c g • a) := by
  simp [groupPolynomialWeight, Finsupp.lsum_single, Finsupp.smul_single]

omit [CompleteSpace V] in
include hα in
theorem spatialGroupPolynomialWeight_norm_le (c : G → ℂ) (v w : G → V)
    (hv : ∀ g, ‖v g‖ ≤ 1) (hw : ∀ g, ‖w g‖ ≤ 1)
    (hc : ∀ g h, c (g*h⁻¹) = ⟪v g, w h⟫_ℂ) (a : G →₀ A) :
    ‖spatialGroupPolynomialMap (G := G) α (groupPolynomialWeight c a)‖ ≤
      ‖spatialGroupPolynomialMap (G := G) α a‖ := by
  apply spatialSchur_norm_le v w hv hw
    (spatialGroupPolynomialMap (G := G) α (groupPolynomialWeight c a)).val
    (spatialGroupPolynomialMap (G := G) α a).val
  intro g h
  refine (spatialGroupPolynomialMap_compression α hα (groupPolynomialWeight c a) g h).symm.trans ?_
  calc
    _ = α (c (g*h⁻¹) • a (g*h⁻¹)) := congrArg α (groupPolynomialWeight_apply c a (g*h⁻¹))
    _ = c (g*h⁻¹) • α (a (g*h⁻¹)) := map_smul α _ _
    _ = _ := congrArg₂ (fun (z : ℂ) (T : H →L[ℂ] H) => z • T)
      (hc g h) (spatialGroupPolynomialMap_compression α hα a g h)
end CuntzPureness

end

end OAI
