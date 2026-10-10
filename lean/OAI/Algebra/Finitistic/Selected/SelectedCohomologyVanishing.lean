import OAI.Algebra.Finitistic.Selected.SelectedCohomologyAssembly

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedCohomologyVanishing
open QuadraticEncoding
section General
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The three actual vertex functors jointly detect a zero module. -/
theorem module_isZero (M : ModuleCat.{u} (B P))
    (h : ∀ i : Fin 3, IsZero
      ((LeftVertexHomology.vertex k (B P) (ThreeVertexAlgebra.vertex (composition P) i)).obj M)) :
    IsZero M := by
  let M' := (ModuleCat.restrictScalars (algebraMap k (B P))).obj M
  have (i : Fin 3) : Subsingleton
      (VertexDecomposition.Space (EncodingModuleAssembly.system P) M' i) := by
    let := ModuleCat.subsingleton_of_isZero (h i)
    exact (LeftVertexHomology.spaceEquiv k (B P) (ThreeVertexAlgebra.vertex (composition P) i) M).symm.injective.subsingleton
  have : Subsingleton M' := (VertexDecomposition.equiv (EncodingModuleAssembly.system P) M').injective.subsingleton
  have : Subsingleton M := inferInstanceAs (Subsingleton M')
  exact ModuleCat.isZero_of_subsingleton M
end General

open SelectedFixedDiagram
variable (N : Type) [AddCommGroup N] [Module ℂ N] [Module (B P) N]

/-- Vanishing on all three evaluated representatives gives actual cohomology
vanishing of the fixed selecting tensor as a B-module. -/
theorem cohomology_isZero (n : ℤ)
    (h : ∀ v : Fin 3, IsZero ((SelectedTensor.source N v).homology n)) :
    IsZero ((SelectedTensor.complex N).homology n) := by
  apply module_isZero P
  intro v
  exact (SelectedTensor.comparisonIso N v n).isZero_iff.mp (h v)
end LittleFinitistic.SelectedCohomologyVanishing

end

end OAI
