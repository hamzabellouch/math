import OAI.Probability.BenjaminiSchramm.TiltedGhost

namespace OAI

noncomputable section
open MeasureTheory

namespace Percolation.BenjaminiSchramm

lemma one_sub_exp_le_single_add_two_ghost {u : ℝ} (hu : 0 ≤ u) :
    1 - Real.exp (-u) ≤ u * Real.exp (-u) + 2 * (1 - Real.exp (-(u / 2))) ^ 2 := by
  let F (r : ℝ) := Real.exp r - 4 * Real.exp (r / 2) + 3 + r
  have hF (r : ℝ) : HasDerivAt F (Real.exp r - 2 * Real.exp (r / 2) + 1) r := by
    have hh : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (r / 2) / 2) r := by
      convert (Real.hasDerivAt_exp (r / 2)).comp (h := fun s : ℝ => s / 2) r
        ((hasDerivAt_id r).div_const 2) using 1
      · funext s
        rfl
      · ring
    convert (((Real.hasDerivAt_exp r).sub (hh.const_mul 4)).add_const 3).add
      (hasDerivAt_id r) using 1
    · funext s
      rfl
    · ring
  have hmono : Monotone F := by
    apply monotone_of_deriv_nonneg (fun r => (hF r).differentiableAt)
    intro r
    rw [(hF r).deriv]
    have he : Real.exp (r / 2) ^ 2 = Real.exp r := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    nlinarith [sq_nonneg (Real.exp (r / 2) - 1)]
  have hnonneg : 0 ≤ F u := by
    have hm := hmono hu
    norm_num [F] at hm ⊢
    exact hm
  have hp := mul_nonneg (Real.exp_pos (-u)).le hnonneg
  have h1 : Real.exp (-u) * Real.exp u = 1 := by
    rw [← Real.exp_add]
    simp
  have h2 : Real.exp (-u) * Real.exp (u / 2) = Real.exp (-(u / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (-(u / 2)) ^ 2 = Real.exp (-u) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  dsimp [F] at hp
  nlinarith

lemma ghostKernel_le_derivative_add_two_ghost {h x : ℝ} (hh : 0 ≤ h) (hx : 0 ≤ x) :
    ghostKernel h x ≤ h * (x * Real.exp (-h * x)) + 2 * ghostKernel (h / 2) x ^ 2 := by
  have he := one_sub_exp_le_single_add_two_ghost (mul_nonneg hh hx)
  have hhalf : -(h / 2) * x = -(h * x / 2) := by ring
  dsimp [ghostKernel]
  rw [hhalf]
  simpa only [neg_mul, mul_assoc] using he

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ)

lemma integrable_ghostKernel_sq (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {h : ℝ} (hh : 0 ≤ h) : Integrable (fun ω => ghostKernel h (X ω) ^ 2) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_ghostKernel X hX h).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [ghostKernel_nonneg hh (hX0 ω), ghostKernel_le_one h (X ω)]

theorem ghostMagnetization_le_derivative_add_two_ghost
    (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) {h : ℝ} (hh : 0 < h) :
    ghostMagnetization μ X h ≤ h * ghostMagnetizationDerivative μ X h +
      2 * ∫ ω, ghostKernel (h / 2) (X ω) ^ 2 ∂μ := by
  calc
    _ ≤ ∫ ω, h * (X ω * Real.exp (-h * X ω)) +
        2 * ghostKernel (h / 2) (X ω) ^ 2 ∂μ := by
      apply integral_mono (integrable_ghostKernel μ X hX hX0 hh.le)
        (((hasDerivAt_ghostMagnetization μ X hX hX0 hh).1.const_mul h).add
          ((integrable_ghostKernel_sq μ X hX hX0 (by positivity : 0 ≤ h / 2)).const_mul 2))
      intro ω
      exact ghostKernel_le_derivative_add_two_ghost hh.le (hX0 ω)
    _ = _ := by
      rw [integral_add ((hasDerivAt_ghostMagnetization μ X hX hX0 hh).1.const_mul h)
        ((integrable_ghostKernel_sq μ X hX hX0 (by positivity : 0 ≤ h / 2)).const_mul 2),
        integral_const_mul, integral_const_mul]
      rfl

end Percolation.BenjaminiSchramm

end

end OAI
