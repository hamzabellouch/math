import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

/-- The actual native mapping cone detects quasi-isomorphisms. -/
theorem quasiIso_iff_mappingCone_acyclic : QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f) (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)
end LittleFinitistic

end

end OAI
