import Mathlib

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

open MonoidAlgebra MulOpposite
namespace ArnoldCounterexample.Nondegenerate.FiltrationObstruction
noncomputable section

abbrev A5Power (k : ℕ) := Fin k → alternatingGroup (Fin 5)

def aug (G : Type*) [Group G] : MonoidAlgebra ℤ G →ₐ[ℤ] ℤ :=
  MonoidAlgebra.lift ℤ ℤ G 1

@[simp] lemma aug_single {G : Type*} [Group G] (g : G) (a : ℤ) :
    aug G (single g a) = a := by
  simp [aug, MonoidAlgebra.lift_single]

def ideal (G : Type*) [Group G] :
    Submodule (MonoidAlgebra ℤ G)ᵐᵒᵖ (MonoidAlgebra ℤ G) where
  carrier := {x | aug G x = 0}
  zero_mem' := map_zero _
  add_mem' hx hy := by simp_all
  smul_mem' r x hx := by
    change aug G (x * unop r) = 0
    change aug G x = 0 at hx
    rw [map_mul, hx, zero_mul]

lemma delta_nonzero {G : Type*} [Group G] {g : G} (hg : g ≠ 1) :
    (single g 1 - 1 : MonoidAlgebra ℤ G) ≠ 0 := by
  intro h
  have h' := congrArg (fun x : MonoidAlgebra ℤ G => x.coeff g) (sub_eq_zero.mp h)
  simp [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, hg] at h'

lemma delta_aug_zero {G : Type*} [Group G] (g : G) :
    aug G (single g 1 - 1) = 0 := by simp

theorem nonzero_killed_by_homology_projection (k : ℕ) (hk : 0 < k) :
    ∃ c : MonoidAlgebra ℤ (A5Power k), c ≠ 0 ∧
      (ideal (A5Power k)).mkQ c = 0 := by
  let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  have : Nontrivial (alternatingGroup (Fin 5)) := inferInstance
  obtain ⟨g,hg⟩ := exists_ne (1 : A5Power k)
  refine ⟨single g 1 - 1, delta_nonzero hg, ?_⟩
  apply (Submodule.Quotient.mk_eq_zero (ideal (A5Power k))).mpr
  exact delta_aug_zero g

theorem homology_projection_not_injective (k : ℕ) (hk : 0 < k) :
    ¬ Function.Injective (ideal (A5Power k)).mkQ := by
  obtain ⟨c,hc,hq⟩ := nonzero_killed_by_homology_projection k hk
  intro hi
  exact hc (hi (hq.trans (map_zero _).symm))

end
end ArnoldCounterexample.Nondegenerate.FiltrationObstruction

end

end OAI
