import Mathlib.Algebra.Homology.HomotopyCategory.Shift

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.OrdinarySimulation
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Reindex P by b, retaining the original differential. This is what the resolution computes. -/
def unsignedShift (P : CochainComplex C ℤ) (b : ℤ) : CochainComplex C ℤ where
  X n := P.X (n+b)
  d n m := P.d (n+b) (m+b)
  shape n m h := P.shape _ _ (by
    change ¬ (n+b)+1 = m+b
    change ¬ n+1=m at h
    omega)
  d_comp_d' n m q _ _ := P.d_comp_d _ _ _

/-- Multiplication by an integer unit is an actual isomorphism in any additive category. -/
def integerUnitIso (X : C) (u : ℤˣ) : X ≅ X where
  hom := u • 𝟙 X
  inv := u⁻¹ • 𝟙 X
  hom_inv_id := by
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.id_comp,
      smul_smul, inv_mul_cancel, one_smul]
  inv_hom_id := by
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.id_comp,
      smul_smul, mul_inv_cancel, one_smul]

/-- The source's degree-n sign (-1)^(b*n), for all integers b and n. -/
def shiftSignIso (P : CochainComplex C ℤ) (b : ℤ) : unsignedShift P b ≅ P⟦b⟧ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => integerUnitIso (P.X (n+b)) (b*n).negOnePow) (by
      intro n m h
      change n+1=m at h
      subst m
      change ((b*n).negOnePow • 𝟙 _) ≫ (b.negOnePow • P.d (n+b) (n+1+b)) =
        P.d (n+b) (n+1+b) ≫ ((b*(n+1)).negOnePow • 𝟙 _)
      simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.id_comp,
        Category.comp_id, smul_smul]
      rw [← Int.negOnePow_add]
      congr 2
      simp [mul_add, add_comm])
end LittleFinitistic.OrdinarySimulation

end

end OAI
