import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyRankOneLimit
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegerExtensionHomology

namespace OAI

/-! # A nonzero top kernel preserves rank-one homology finiteness -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] ModuleCat.isModule

theorem rankOne_module_finite_of_nonzero_kernel {M V : ModuleCat ℤ}
    (htorsion : ∀ (z : ℤ) (x : M), z • x = 0 → z = 0 ∨ x = 0)
    (hcomm : ∀ x y : M, x ≠ 0 → y ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y)
    (f : M ⟶ M) (e : V ≅ kernel f) [Module.Finite ℤ V]
    (x : V) (hx : x ≠ 0) : Module.Finite ℤ M := by
  let j : V ⟶ M := e.hom ≫ kernel.ι f
  have hj : Function.Injective j := (ModuleCat.mono_iff_injective j).mp inferInstance
  have hjx : j x ≠ 0 := by
    intro h
    exact hx (hj (h.trans (map_zero j.hom).symm))
  have hfx : f (j x) = 0 := by
    have h : j ≫ f = 0 := by simp only [j, Category.assoc, kernel.condition, comp_zero]
    exact congrArg (fun g : V ⟶ M => g x) h
  have hf : f = 0 := rankOne_homology_map_eq_zero_of_nonzero_kernel htorsion hcomm f _ hjx hfx
  have hfinite : Module.Finite ℤ (kernel f : ModuleCat ℤ) :=
    Module.Finite.of_surjective e.hom.hom ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance)
  let := hfinite
  have hs : Function.Surjective (kernel.ι f) := by
    intro y
    refine ⟨kernel.lift f (𝟙 M) (by rw [hf, comp_zero]) y, ?_⟩
    exact congrArg (fun g => g y) (kernel.lift_ι f (𝟙 M) (by rw [hf, comp_zero]))
  exact Module.Finite.of_surjective (kernel.ι f).hom hs

end PolycyclicRecognition

end

end OAI
