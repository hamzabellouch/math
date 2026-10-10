import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI

/-! # Splitting off one dimension from a nilpotent Lie algebra

The kernel of a nonzero character is a smaller nilpotent ideal. Choosing a
vector of character one gives the concrete coordinates for the inductive
semidirect-product construction.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule Module

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]

structure LieCodimensionOneData where
  character : L →ₗ[ℝ] ℝ
  unit : L
  character_unit : character unit = 1
  character_lie : ∀ (x y : L), character ⁅x, y⁆ = 0

variable {L}

namespace LieCodimensionOneData

variable (D : LieCodimensionOneData L)

def ideal : LieIdeal ℝ L where
  toSubmodule := D.character.ker
  lie_mem := by
    intro x y _
    exact D.character_lie x y

theorem ideal_lt_top : D.ideal < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h
  have hu : D.unit ∈ D.ideal := by rw [h]; exact LieSubmodule.mem_top _
  change D.character D.unit = 0 at hu
  rw [D.character_unit] at hu
  exact one_ne_zero hu

theorem finrank_ideal_lt [FiniteDimensional ℝ L] : finrank ℝ D.ideal < finrank ℝ L := by
  have hh := Submodule.finrank_lt_finrank_of_lt (s := D.ideal.toSubmodule)
    (t := ⊤) D.ideal_lt_top
  let e : D.ideal ≃ₗ[ℝ] D.ideal.toSubmodule :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [e.finrank_eq]
  simpa using hh

def split : (D.ideal × ℝ) ≃ₗ[ℝ] L where
  toFun p := p.1 + p.2 • D.unit
  invFun x := (⟨x - D.character x • D.unit, by
    change D.character (x - D.character x • D.unit) = 0
    simp [D.character_unit]⟩, D.character x)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      have hp : D.character p.1 = 0 := p.1.2
      simp [hp, D.character_unit]
    · have hp : D.character p.1 = 0 := p.1.2
      simp [hp, D.character_unit]
  right_inv x := sub_add_cancel _ _
  map_add' p q := by
    change ((p.1 : L) + (q.1 : L)) + (p.2 + q.2) • D.unit =
      ((p.1 : L) + p.2 • D.unit) + ((q.1 : L) + q.2 • D.unit)
    rw [add_smul]
    abel
  map_smul' a p := by simp [smul_add, smul_smul]

end LieCodimensionOneData

theorem exists_nilpotentCodimensionOneData [FiniteDimensional ℝ L]
    [LieRing.IsNilpotent L] [Nontrivial L] : Nonempty (LieCodimensionOneData L) := by
  have hp : (LieAlgebra.derivedSeries ℝ L 1).toSubmodule < ⊤ :=
    LieAlgebra.derivedSeries_lt_top_of_solvable ℝ L
  obtain ⟨f, hf, hker⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hp inferInstance
  have hex : ∃ x, f x ≠ 0 := by
    by_contra! h
    exact hf (LinearMap.ext h)
  obtain ⟨x, hx⟩ := hex
  refine ⟨⟨f, (f x)⁻¹ • x, ?_, ?_⟩⟩
  · simp [hx]
  · intro y z
    have hb : ⁅y, z⁆ ∈ LieAlgebra.derivedSeries ℝ L 1 := by
      change ⁅y, z⁆ ∈ ⁅(⊤ : LieIdeal ℝ L), ⊤⁆
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
    have hm : f ⁅y, z⁆ ∈ (LieAlgebra.derivedSeries ℝ L 1).toSubmodule.map f :=
      Submodule.mem_map_of_mem hb
    rw [hker] at hm
    exact hm

end PolycyclicRecognition

end

end OAI
