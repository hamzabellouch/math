import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteGeneratorNoJordan
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI

/-! # Dimension of a generator with only the three physical symmetry eigenvalues -/

namespace DefocusingNLS

theorem finite_symmetry_dimension_le {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] (G : V →L[ℂ] V)
    (hspec : ∀ (lam : ℂ) (v : V), v ≠ 0 → G v = lam • v → lam = 0 ∨ lam = 1 ∨ lam = 1 / 2)
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤)
    (h0 : Module.finrank ℂ (Module.End.eigenspace G.toLinearMap 0) ≤ 1)
    (h1 : Module.finrank ℂ (Module.End.eigenspace G.toLinearMap 1) ≤ 1)
    (hh : Module.finrank ℂ (Module.End.eigenspace G.toLinearMap (1 / 2)) ≤ 12) :
    Module.finrank ℂ V ≤ 14 := by
  let S := Module.End.eigenspace G.toLinearMap
  have htop : S 0 ⊔ S 1 ⊔ S (1 / 2) = ⊤ := by
    apply le_antisymm le_top
    rw [← hspan]
    apply iSup_le
    intro lam v hv
    by_cases hz : v = 0
    · simpa only [hz] using (zero_mem (S 0 ⊔ S 1 ⊔ S (1 / 2)))
    rcases hspec lam v hz (Module.End.mem_eigenspace_iff.mp hv) with rfl | rfl | rfl
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left hv)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right hv)
    · exact Submodule.mem_sup_right hv
  have h01 := Submodule.finrank_sup_add_finrank_inf_eq (S 0) (S 1)
  have hall := Submodule.finrank_sup_add_finrank_inf_eq (S 0 ⊔ S 1) (S (1 / 2))
  rw [htop, finrank_top] at hall
  dsimp only [S] at h01 hall
  omega

end DefocusingNLS

end OAI
