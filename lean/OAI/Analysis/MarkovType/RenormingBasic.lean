import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Tactic.Linarith

namespace OAI

namespace MarkovSuperreflexivity

universe u

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

structure EquivalentNorm where
  p : Seminorm ℝ X
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  lower_bound : ∀ x, lower * ‖x‖ ≤ p x
  upper_bound : ∀ x, p x ≤ upper * ‖x‖

variable {X}

namespace EquivalentNorm

@[simp] theorem eq_zero_iff (N : EquivalentNorm X) (x : X) : N.p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hlow := N.lower_bound x
    have hn := norm_nonneg x
    have he : ‖x‖ = 0 := by nlinarith [N.lower_pos]
    exact norm_eq_zero.mp he
  · rintro rfl
    exact map_zero N.p

noncomputable def original (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] : EquivalentNorm X where
  p := normSeminorm ℝ X
  lower := 1
  upper := 1
  lower_pos := zero_lt_one
  upper_pos := zero_lt_one
  lower_bound x := by simp
  upper_bound x := by simp

@[simp] theorem original_apply (x : X) : (original X).p x = ‖x‖ := rfl

end EquivalentNorm

def UniformConvex (p : Seminorm ℝ X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 2 → ∃ δ : ℝ, 0 < δ ∧
    ∀ x y : X, p x ≤ 1 → p y ≤ 1 → ε ≤ p (x - y) →
      p ((1 / 2 : ℝ) • (x + y)) ≤ 1 - δ

def UniformSmooth (p : Seminorm ℝ X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ t : ℝ, 0 < t → t < δ → ∀ x y : X, p x = 1 → p y = 1 →
      (p (x + t • y) + p (x - t • y)) / 2 ≤ 1 + ε * t

def HasEquivalentUCNorm (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∃ N : EquivalentNorm X, UniformConvex N.p

def HasEquivalentUSNorm (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∃ N : EquivalentNorm X, UniformSmooth N.p

theorem uniformConvex_of_subsingleton [Subsingleton X] (p : Seminorm ℝ X) :
    UniformConvex p := by
  intro ε hε _
  refine ⟨1, zero_lt_one, ?_⟩
  intro x y _ _ hsep
  have hxy : x - y = 0 := Subsingleton.elim _ _
  have he : ε ≤ 0 := by simpa only [hxy, map_zero] using hsep
  exact False.elim (not_le_of_gt hε he)

theorem uniformSmooth_of_subsingleton [Subsingleton X] (p : Seminorm ℝ X) :
    UniformSmooth p := by
  intro ε _
  refine ⟨1, zero_lt_one, ?_⟩
  intro t _ _ x y hx _
  have hx0 : x = 0 := Subsingleton.elim _ _
  have he : (0 : ℝ) = 1 := by simpa only [hx0, map_zero] using hx
  exact False.elim (zero_ne_one he)

theorem hasEquivalentUCNorm_of_subsingleton [Subsingleton X] : HasEquivalentUCNorm X :=
  ⟨EquivalentNorm.original X, uniformConvex_of_subsingleton _⟩

theorem hasEquivalentUSNorm_of_subsingleton [Subsingleton X] : HasEquivalentUSNorm X :=
  ⟨EquivalentNorm.original X, uniformSmooth_of_subsingleton _⟩

end MarkovSuperreflexivity

end OAI
