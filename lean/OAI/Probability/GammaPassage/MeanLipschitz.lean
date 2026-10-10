import OAI.Probability.GammaPassage.MeanAlgebra
import OAI.Probability.FirstPassage.CoordinateTails
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- The horizontal-then-vertical coordinate path has exactly the lattice `L¹` length. -/
private theorem coordinate_path_length_l1 (p q : Vertex) :
    (coordinatePath p q).length = latticeDistance p q := by
  have hh (a : ℤ) : (horizontal a).length = a.natAbs := by
    unfold horizontal
    split_ifs <;> simp only [List.length_replicate] <;> omega
  have hv (a : ℤ) : (vertical a).length = a.natAbs := by
    unfold vertical
    split_ifs <;> simp only [List.length_replicate] <;> omega
  simp [coordinatePath, latticeDistance, hh, hv]

/-- The finite first-moment path bound controls the actual Fekete constant. -/
theorem GammaEnvironment.directionalMeanConstant_le_l1
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) :
    directionalMeanConstant h hs hr z ≤
      (shape / rate) * ((z.1.natAbs + z.2.natAbs : ℕ) : ℝ) := by
  have hb := h.directionalMeanConstant_le_path_length hs hr z
    (coordinatePath 0 z) (coordinatePath_endpoint 0 z)
  rw [coordinate_path_length_l1] at hb
  simpa [latticeDistance, mul_comm] using hb

/-- Reverse triangle inequality for the actual lattice mean constants. -/
theorem GammaEnvironment.abs_directionalMeanConstant_sub_le
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (x y : Vertex) :
    |directionalMeanConstant h hs hr x - directionalMeanConstant h hs hr y| ≤
      directionalMeanConstant h hs hr (x - y) := by
  have hx := h.directionalMeanConstant_add_le hs hr (x-y) y
  rw [sub_add_cancel] at hx
  have hy := h.directionalMeanConstant_add_le hs hr (y-x) x
  rw [sub_add_cancel] at hy
  have he : directionalMeanConstant h hs hr (y-x) =
      directionalMeanConstant h hs hr (x-y) := by
    rw [show y-x = -(x-y) by exact (neg_sub x y).symm,
      h.directionalMeanConstant_neg hs hr]
  rw [he] at hy
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- L1-Lipschitz estimate, with the true Gamma mean shape/rate, all lattice
vertices, and no time-norm, positivity-of-limit or almost-sure premise. -/
theorem GammaEnvironment.directionalMeanConstant_l1_lipschitz
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (x y : Vertex) :
    |directionalMeanConstant h hs hr x - directionalMeanConstant h hs hr y| ≤
      (shape / rate) * (((x.1-y.1).natAbs + (x.2-y.2).natAbs : ℕ) : ℝ) := by
  exact (h.abs_directionalMeanConstant_sub_le hs hr x y).trans
    (h.directionalMeanConstant_le_l1 hs hr (x-y))

end GammaFPP

end OAI
