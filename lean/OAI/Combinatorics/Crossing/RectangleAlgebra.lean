import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def edgePairing (J : Matrix ι ι ℝ) (z y : ι → ℝ) : ℝ :=
  ∑ e, ∑ f, z e * J e f * y f

theorem edgePairing_single (J : Matrix ι ι ℝ) (e f : ι) :
    edgePairing J (Pi.single e 1) (Pi.single f 1) = J e f := by
  simp [edgePairing, Pi.single_apply]

theorem edgePairing_add_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (z z' y : ι → ℝ) :
    edgePairing J (z+z') y = edgePairing J z y + edgePairing J z' y := by
  simp [edgePairing, add_mul, Finset.sum_add_distrib]

theorem edgePairing_add_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (z y y' : ι → ℝ) :
    edgePairing J z (y+y') = edgePairing J z y + edgePairing J z y' := by
  simp [edgePairing, mul_add, Finset.sum_add_distrib]

theorem edgePairing_sub_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (z z' y : ι → ℝ) :
    edgePairing J (z-z') y = edgePairing J z y - edgePairing J z' y := by
  simp [edgePairing, sub_mul, Finset.sum_sub_distrib]

theorem edgePairing_sub_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (z y y' : ι → ℝ) :
    edgePairing J z (y-y') = edgePairing J z y - edgePairing J z y' := by
  simp [edgePairing, mul_sub, Finset.sum_sub_distrib]

theorem rectangle_additive
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (H : Matrix ι κ ℝ) (i₀ : ι) (j₀ : κ)
    (hrect : ∀ i i' j j', H i j-H i j'-H i' j+H i' j' = 0) :
    ∃ r : ι → ℝ, ∃ c : κ → ℝ, ∀ i j, H i j = r i+c j := by
  refine ⟨fun i => H i j₀, fun j => H i₀ j-H i₀ j₀, ?_⟩
  intro i j
  have hh := hrect i i₀ j j₀
  linarith

end Zarankiewicz

end

end OAI
