import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.HeightTemperedDistribution
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSchwartzKernel

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter

theorem bounded_measurable_integrableOn_finite {d : ℕ}
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f)
    (M : ℝ) (hb : ∀ x, |f x| ≤ M) (s : Set (Ambient d)) (hs : μ s ≠ ⊤) :
    IntegrableOn f s μ := by
  have hI : IntegrableOn (fun _ : Ambient d => M) s μ := integrableOn_const hs
  apply hI.mono' hf.aestronglyMeasurable
  exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hb x

theorem bounded_measurable_locallyIntegrable {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (f : Ambient d → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ x, |f x| ≤ M) :
    LocallyIntegrable f μ := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  exact bounded_measurable_integrableOn_finite μ f hf M hb K hK.measure_ne_top

theorem bounded_density_exterior_integrable (d : ℕ)
    (f : Ambient d → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ x, |f x| ≤ M) :
    IntegrableOn (fun x => |f x| * inverseDistancePow (d + 2) 0 x)
      (closedExterior 0 1) volume := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hb 0)
  have hi := (inverseDistancePow_closedExterior_integrable_and_bound (d := d) d _ volume
    (volume_global_upper_growth d) 0 1 zero_lt_one).1
  apply (hi.const_mul M).mono'
    ((hf.abs.mul (inverseDistancePow_measurable (d + 2) 0)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (closedExterior_measurable (0 : Ambient d) 1)] with x hx
  have hp : dist (0 : Ambient d) x ^ (d + 1) ≤ dist 0 x ^ (d + 2) := by
    calc
      _ = dist (0 : Ambient d) x ^ (d + 1) * 1 := (mul_one _).symm
      _ ≤ dist (0 : Ambient d) x ^ (d + 1) * dist 0 x :=
        mul_le_mul_of_nonneg_left hx (pow_nonneg dist_nonneg _)
      _ = _ := (pow_succ _ _).symm
  have hinv : inverseDistancePow (d + 2) 0 x ≤ inverseDistancePow (d + 1) 0 x :=
    inv_anti₀ (pow_pos (zero_lt_one.trans_le hx) _) hp
  rw [Pi.mul_apply, Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (inverseDistancePow_nonneg _ _ _))]
  exact (mul_le_mul_of_nonneg_right (hb x) (inverseDistancePow_nonneg _ _ _)).trans
    (mul_le_mul_of_nonneg_left hinv hM)

theorem bounded_density_polynomial_weight_integrable (d : ℕ)
    (f : Ambient d → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ x, |f x| ≤ M) :
    Integrable (fun x => |f x| * polynomialDecay (d + 2) x) volume := by
  exact polynomial_weight_integrable_from_height_tail (d + 2) volume f hf 0 1 zero_lt_one
    (bounded_measurable_integrableOn_finite volume f hf M hb (ball 0 1) measure_ball_lt_top.ne)
    (bounded_density_exterior_integrable d f hf M hb)

end

end RieszRectifiability

end OAI
