import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.EnergyIdentity

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem integral_squared_difference (μ : Measure X) (w v : X → ℝ)
    (hww : Integrable (fun x => w x ^ 2) μ)
    (hwv : Integrable (fun x => w x * v x) μ)
    (hvv : Integrable (fun x => v x ^ 2) μ) :
    (∫ x, (w x - v x) ^ 2 ∂μ) =
      (∫ x, w x ^ 2 ∂μ) - 2 * (∫ x, w x * v x ∂μ) + (∫ x, v x ^ 2 ∂μ) := by
  have h : (fun x => (w x - v x) ^ 2) =
      (fun x => w x ^ 2 - 2 * (w x * v x) + v x ^ 2) := by
    funext x
    ring
  have hadd := integral_add (hww.sub (hwv.const_mul 2)) hvv
  have hsub := integral_sub hww (hwv.const_mul 2)
  simp only [Pi.sub_apply] at hadd hsub
  rw [h, hadd, hsub, integral_const_mul]

theorem squared_error_tendsto_zero_of_moments
    (μ : ℕ → Measure X) (w : ℕ → X → ℝ) (v : X → ℝ) (a : ℝ)
    (hww : ∀ j, Integrable (fun x => w j x ^ 2) (μ j))
    (hwv : ∀ j, Integrable (fun x => w j x * v x) (μ j))
    (hvv : ∀ j, Integrable (fun x => v x ^ 2) (μ j))
    (lim_ww : Tendsto (fun j => ∫ x, w j x ^ 2 ∂μ j) atTop (𝓝 a))
    (lim_wv : Tendsto (fun j => ∫ x, w j x * v x ∂μ j) atTop (𝓝 a))
    (lim_vv : Tendsto (fun j => ∫ x, v x ^ 2 ∂μ j) atTop (𝓝 a)) :
    Tendsto (fun j => ∫ x, (w j x - v x) ^ 2 ∂μ j) atTop (𝓝 0) := by
  have hfun : (fun j => ∫ x, (w j x - v x) ^ 2 ∂μ j) =
      (fun j => (∫ x, w j x ^ 2 ∂μ j) -
        2 * (∫ x, w j x * v x ∂μ j) + (∫ x, v x ^ 2 ∂μ j)) := by
    funext j
    exact integral_squared_difference (μ j) (w j) v (hww j) (hwv j) (hvv j)
  rw [hfun]
  have h := (lim_ww.sub (lim_wv.const_mul 2)).add lim_vv
  simpa only [show a - 2 * a + a = 0 by ring] using! h

end

end RieszRectifiability

end OAI
