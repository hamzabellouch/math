import OAI.MeasureTheory.Falconer.Graphs.ProductGraphIntegral
import OAI.MeasureTheory.Falconer.Graphs.GraphProfileCoefficient

namespace OAI

namespace PlanarFalconer
open MeasureTheory

theorem product_outer_norm (a p v c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    ‖((2:ℝ)^(2*(v-a))) • (c • z)‖ =
      ((2:ℝ)^(2*(p-a)))*c*‖((2:ℝ)^(2*(v-p))) • z‖ := by
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc,
    abs_of_pos (by positivity : 0 < (2:ℝ)^(2*(v-a))),
    abs_of_pos (by positivity : 0 < (2:ℝ)^(2*(v-p)))]
  have he : (2:ℝ)^(2*(v-a)) = (2:ℝ)^(2*(p-a))*(2:ℝ)^(2*(v-p)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  rw [he]
  ring

theorem product_energy_transfer (a p v c x E ε : ℝ) (hc : 0 ≤ c) (hx : 0 ≤ x) (z : ℂ)
    (herror : ‖(x:ℂ) - ((2:ℝ)^(2*(v-a))) • (c • z)‖ ≤ ε)
    (hgraph : ‖((2:ℝ)^(2*(v-p))) • z‖ ≤ E) :
    x ≤ ((2:ℝ)^(2*(p-a)))*c*E+ε := by
  have hnorm := norm_add_le ((x:ℂ)-((2:ℝ)^(2*(v-a))) • (c • z))
    (((2:ℝ)^(2*(v-a))) • (c • z))
  rw [sub_add_cancel,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx,
    product_outer_norm a p v c hc z] at hnorm
  have hh := mul_le_mul_of_nonneg_left hgraph
    (mul_nonneg (by positivity : 0 ≤ (2:ℝ)^(2*(p-a))) hc)
  linarith

end PlanarFalconer

end OAI
