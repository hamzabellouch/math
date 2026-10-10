import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

theorem euclidean_sub_sq_three_point_bound {q : ℕ} (x y z : Ambient q) :
    ‖x - z‖ ^ 2 ≤ 2 * (‖x - y‖ ^ 2 + ‖y - z‖ ^ 2) := by
  have hn := norm_add_le (x - y) (y - z)
  rw [sub_add_sub_cancel] at hn
  have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
  nlinarith [sq_nonneg (‖x - y‖ - ‖y - z‖)]

theorem vector_error_integrable_and_bound {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (w v g : X → Ambient q) (hw : Measurable w) (hg : Measurable g)
    (h₁ : Integrable (fun x => ‖w x - v x‖ ^ 2) μ)
    (h₂ : Integrable (fun x => ‖v x - g x‖ ^ 2) μ) :
    Integrable (fun x => ‖w x - g x‖ ^ 2) μ ∧
      (∫ x, ‖w x - g x‖ ^ 2 ∂μ) ≤
        2 * ((∫ x, ‖w x - v x‖ ^ 2 ∂μ) + (∫ x, ‖v x - g x‖ ^ 2 ∂μ)) := by
  have hb := fun x => euclidean_sub_sq_three_point_bound (w x) (v x) (g x)
  have hi := ((h₁.add h₂).const_mul 2).mono'
    (((hw.sub hg).norm.pow_const 2).aestronglyMeasurable)
    (Eventually.of_forall fun x => by
      simpa only [Pi.sub_apply, Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖w x - g x‖)] using! hb x)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, 2 * (‖w x - v x‖ ^ 2 + ‖v x - g x‖ ^ 2) ∂μ :=
      integral_mono hi ((h₁.add h₂).const_mul 2) hb
    _ = _ := by rw [integral_const_mul, integral_add h₁ h₂]

theorem vector_strong_limit_trans {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : ℕ → Measure X) (w v g : ℕ → X → Ambient q)
    (hw : ∀ j, Measurable (w j)) (hg : ∀ j, Measurable (g j))
    (h₁ : ∀ j, Integrable (fun x => ‖w j x - v j x‖ ^ 2) (μ j))
    (h₂ : ∀ j, Integrable (fun x => ‖v j x - g j x‖ ^ 2) (μ j))
    (hlim₁ : Tendsto (fun j => ∫ x, ‖w j x - v j x‖ ^ 2 ∂μ j) atTop (𝓝 0))
    (hlim₂ : Tendsto (fun j => ∫ x, ‖v j x - g j x‖ ^ 2 ∂μ j) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, ‖w j x - g j x‖ ^ 2 ∂μ j) atTop (𝓝 0) := by
  have hlim : Tendsto (fun j => 2 * ((∫ x, ‖w j x - v j x‖ ^ 2 ∂μ j) +
      (∫ x, ‖v j x - g j x‖ ^ 2 ∂μ j))) atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using! (hlim₁.add hlim₂).const_mul 2
  exact squeeze_zero (fun j => integral_nonneg fun x => sq_nonneg ‖w j x - g j x‖)
    (fun j => (vector_error_integrable_and_bound (μ j) (w j) (v j) (g j)
      (hw j) (hg j) (h₁ j) (h₂ j)).2) hlim

end

end RieszRectifiability

end OAI
