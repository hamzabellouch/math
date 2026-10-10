import OAI.Geometry.CylinderCovering.Radial.UniformApproximationDefinitions
import OAI.Geometry.CylinderCovering.Radial.CollarRate
import OAI.Geometry.CylinderCovering.Radial.UniformTags

namespace OAI

noncomputable section
namespace CylinderCovering.RadialUniformApproximation
open RadialSweep

lemma triangleCost_eq_totalArea (D : Data) (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) :
    triangleCost D N tag = TriangularCovering.totalArea (frozenCylinder D N tag htag) := by
  unfold triangleCost TriangularCovering.totalArea
  apply Finset.sum_congr rfl
  intro i _
  rw [frozenCylinder_base]

lemma triangleCost_eq_formula (D : Data) (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) :
    triangleCost D N tag = ∑ i : Fin N, frozenArea D N tag i := by
  rw [triangleCost_eq_totalArea D N tag htag]
  simp only [TriangularCovering.totalArea, frozenCylinder_area]

theorem uniform_approximation : Statement where
  collarUniform := by
    intro D
    obtain ⟨C, hC, h⟩ := frozenCylinder_collar_uniform D
    refine ⟨C, hC, ?_⟩
    intro N hN tag htag
    simpa only [collarError, leadingCost, triangleCost_eq_totalArea D N tag htag]
      using h N hN tag htag
  collarExplicit := by
    intro D M hM N hN tag htag
    have h := frozenCylinder_collar_bounds D hM hN tag htag
    have hd := frozenCylinder_collar_le_div D hM hN tag htag
    simpa only [collarError, leadingCost, triangleCost_eq_totalArea D N tag htag]
      using And.intro h.1 (And.intro h.2 hd)
  tagsUniform := by
    intro D ε hε
    obtain ⟨N₁, hN₁, h₁⟩ := exists_count_frozenArea_uniform_tags D hε
    obtain ⟨N₂, _, h₂⟩ := exists_count_actualCost_uniform_tags D hε
    refine ⟨max N₁ N₂, lt_of_lt_of_le hN₁ (le_max_left _ _), ?_⟩
    intro N hN tag htag
    rw [triangleCost_eq_formula D N tag htag]
    exact ⟨h₁ N ((le_max_left _ _).trans hN) tag htag,
      h₂ N ((le_max_right _ _).trans hN) tag htag⟩

end CylinderCovering.RadialUniformApproximation

end

end OAI
