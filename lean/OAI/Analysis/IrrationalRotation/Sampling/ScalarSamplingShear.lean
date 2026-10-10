import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingVariation
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

lemma integrableOn_unitSquare_of_bound {F : ℝ → ℝ → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F)) (hC : ∀ x y, ‖F x y‖ ≤ C) :
    IntegrableOn (Function.uncurry F) (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) := by
  have hfinite : volume (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) < ⊤ := by
    apply lt_of_le_of_lt (measure_mono (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc))
    exact (isCompact_uIcc.prod isCompact_uIcc).measure_lt_top
  exact IntegrableOn.of_bound hfinite hF.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun p => hC p.1 p.2))

theorem double_interval_integral_shear {F : ℝ → ℝ → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F)) (hC : ∀ x y, ‖F x y‖ ≤ C)
    (hperiodic : ∀ y, Function.Periodic (fun x => F x y) 1) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, F (x - y) y) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, F x y := by
  have hG : Measurable (fun p : ℝ × ℝ => F (p.1 - p.2) p.2) :=
    hF.comp ((measurable_fst.sub measurable_snd).prodMk measurable_snd)
  have hFi := integrableOn_unitSquare_of_bound hF hC
  have hGi := integrableOn_unitSquare_of_bound (F := fun x y => F (x - y) y) hG (fun x y => hC (x - y) y)
  rw [intervalIntegral_intervalIntegral_swap hGi, intervalIntegral_intervalIntegral_swap hFi]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  calc
    (∫ x in (0 : ℝ)..1, F (x - y) y) = ∫ x in (-y)..(-y + 1), F x y := by
      rw [intervalIntegral.integral_comp_sub_right (fun x => F x y) y]
      congr 1 <;> ring
    _ = ∫ x in (0 : ℝ)..1, F x y := by
      simpa only [zero_add] using (hperiodic y).intervalIntegral_add_eq (-y) 0

theorem measurable_circleKernel (h α : ℝ) :
    Measurable (Function.uncurry (circleKernel h α)) := by
  have hz : Measurable (fun p : ℝ × ℝ => Int.fract p.1) :=
    measurable_fract.comp measurable_fst
  have hv : Measurable (fun p : ℝ × ℝ => Int.fract p.2) :=
    measurable_fract.comp measurable_snd
  have hd : Measurable (fun p : ℝ × ℝ => delta (Int.fract p.1)) :=
    hz.min (measurable_const.sub hz)
  change Measurable (fun p : ℝ × ℝ => circleKernel h α p.1 p.2)
  simp only [circleKernel, rawKernel, Set.indicator_apply]
  apply Measurable.ite (measurableSet_le measurable_const hd)
  · apply Measurable.ite
    · exact (measurableSet_lt measurable_const hv).inter
        (measurableSet_lt hv (measurable_const.mul hd))
    · exact (measurable_const.mul hd).inv
    · exact measurable_const
  · exact measurable_const

lemma circleKernel_periodic_left (h α v : ℝ) :
    Function.Periodic (fun z => circleKernel h α z v) 1 := by
  intro z
  simp only [circleKernel, Int.fract_add_one]

lemma circleKernel_norm_le {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (z v : ℝ) :
    ‖circleKernel h α z v‖ ≤ (h * α)⁻¹ := by
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact rawKernel_le_height hh hα _ _
  · exact rawKernel_nonneg hh.le ⟨Int.fract_nonneg z, (Int.fract_lt_one z).le⟩

theorem endpoint_circleKernel_mass {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α (z - v) v) =
      1 - 2 * α := by
  rw [double_interval_integral_shear (measurable_circleKernel h α)
    (circleKernel_norm_le hh hα) (circleKernel_periodic_left h α)]
  exact double_interval_integral_circleKernel hh hhone hα hαhalf

theorem endpoint_circleKernel_secondMoment {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α (z - v) v ^ 2) =
      (2 / h) * Real.log (1 / (2 * α)) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => circleKernel h α p.1 p.2 ^ 2) :=
    (measurable_circleKernel h α).pow_const 2
  have hbound (z v : ℝ) : ‖circleKernel h α z v ^ 2‖ ≤ ((h * α)⁻¹)^2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (circleKernel_norm_le hh hα z v) 2
  have hper (v : ℝ) : Function.Periodic (fun z => circleKernel h α z v ^ 2) 1 := by
    intro z
    exact congrArg (fun x : ℝ => x^2) (circleKernel_periodic_left h α v z)
  rw [double_interval_integral_shear (F := fun z v => circleKernel h α z v ^ 2) hmeas hbound hper]
  exact double_interval_integral_sq_circleKernel hh hhone hα hαhalf

theorem manuscriptEndpointKernel_mass {m : ℕ} (hm : 200 ≤ m) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m z v) =
      1 - 2 / (m : ℝ)^2 := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  simpa only [manuscriptEndpointKernel, manuscriptKernel, mul_one_div] using
    endpoint_circleKernel_mass hh hhone hα hαhalf

theorem manuscriptEndpointKernel_secondMoment {m : ℕ} (hm : 200 ≤ m) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m z v ^ 2) =
      (2 / (m : ℝ) ^ (-(3 / 5 : ℝ))) * Real.log ((m : ℝ)^2 / 2) := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have heq : 1 / (2 * (1 / (m : ℝ)^2)) = (m : ℝ)^2 / 2 := by
    field_simp [hmR.ne']
  simpa only [manuscriptEndpointKernel, manuscriptKernel, heq] using
    endpoint_circleKernel_secondMoment hh hhone hα hαhalf

end Invariant233.ScalarSampling

end OAI
