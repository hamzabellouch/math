import Mathlib

namespace OAI

/-! A nonzero kernel morphism obstructs a retraction. -/

namespace KernelObstruction

open CategoryTheory CategoryTheory.Limits

theorem no_retraction_of_nonzero_kernel
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {D U V : C} (f : U ⟶ V) (z : D ⟶ U) (hz : z ≠ 0) (hk : z ≫ f = 0) :
    ¬ ∃ r : V ⟶ U, f ≫ r = 𝟙 U := by
  rintro ⟨r, hr⟩
  apply hz
  calc
    z = z ≫ (f ≫ r) := by rw [hr, Category.comp_id]
    _ = (z ≫ f) ≫ r := (Category.assoc z f r).symm
    _ = 0 := by rw [hk, zero_comp]

end KernelObstruction

end OAI
