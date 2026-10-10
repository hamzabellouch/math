import Mathlib.Algebra.Lie.Engel
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # A common product bound for nilpotent Lie representations

Engel's theorem supplies a terminating lower central series for the module.
Every product of represented operators of sufficient length is therefore zero.
-/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L V : Type*} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem exists_vanishing_products_of_pointwise_nilpotent
    (j : L →ₗ⁅ℝ⁆ Module.End ℝ V) (hj : ∀ x, IsNilpotent (j x)) :
    ∃ c : ℕ, ∀ l : List L, c ≤ l.length → (l.map j).prod = 0 := by
  let := LieRingModule.compLieHom V j
  let := LieModule.compLieHom V j
  have hn : LieModule.IsNilpotent L V :=
    (LieModule.isNilpotent_iff_forall' (R := ℝ)).mpr hj
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ L V).mp hn
  have hmem (l : List L) (v : V) :
      (l.map j).prod v ∈ LieModule.lowerCentralSeries ℝ L V l.length := by
    induction l with
    | nil => simp
    | cons x l hl =>
      rw [List.map_cons, List.prod_cons, List.length_cons, LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hl
  refine ⟨c, fun l hl => ?_⟩
  ext v
  have h := (LieModule.antitone_lowerCentralSeries ℝ L V hl) (hmem l v)
  rw [hc] at h
  exact (LieSubmodule.mem_bot _).mp h

end PolycyclicRecognition

end

end OAI
