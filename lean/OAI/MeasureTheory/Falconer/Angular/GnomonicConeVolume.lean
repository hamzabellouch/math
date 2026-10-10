import OAI.MeasureTheory.Falconer.Estimates.ConeSections
import OAI.MeasureTheory.Falconer.Radial.ConeRadialIntegral

namespace OAI

/-! # The Euclidean volume of a gnomonic cone -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem gnomonicCone_volume {n : ℕ} {A : Set (Space n)} (hA : MeasurableSet A) :
    volume (gnomonicCone A) = ∫⁻ x : Space n in A,
      ENNReal.ofReal (gnomonicDensity x/((n+1:ℕ):ℝ)) := by
  classical
  let b : Space n → ℝ := fun x => ‖northLift x‖⁻¹
  have hb : Continuous b := (northLift_continuous n).norm.inv₀
    (fun x => norm_ne_zero_iff.mpr (northLift_ne_zero x))
  let F : ℝ × Space n → ℝ≥0∞ := fun z =>
    if z.2 ∈ A ∧ 0 < z.1 ∧ z.1 < b z.2 then ENNReal.ofReal (z.1^n) else 0
  have hreg : MeasurableSet {z : ℝ × Space n | z.2 ∈ A ∧ 0 < z.1 ∧ z.1 < b z.2} :=
    (hA.preimage measurable_snd).inter ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst (hb.measurable.comp measurable_snd)))
  have hF : Measurable F := Measurable.ite hreg
    (measurable_fst.pow_const n).ennreal_ofReal measurable_const
  have hslice (r : ℝ) : volume {y : Space n | euclideanCons r y ∈ gnomonicCone A} =
      ∫⁻ x : Space n, F (r,x) := by
    by_cases hr : 0 < r
    · rw [gnomonicCone_section_volume A r hr]
      have hset : MeasurableSet {x : Space n | x ∈ A ∧ r < b x} :=
        hA.inter (measurableSet_lt measurable_const hb.measurable)
      have he : (fun x : Space n => F (r,x)) =
          fun x => ENNReal.ofReal (r^n)*{x : Space n | x ∈ A ∧ r < b x}.indicator (fun _ => (1 : ℝ≥0∞)) x := by
        funext x
        by_cases hx : x ∈ A ∧ r < b x <;> simp [F,hr,hx]
      rw [he,lintegral_const_mul _ (measurable_const.indicator hset),lintegral_indicator_fun_one hset]
    · rw [gnomonicCone_section_nonpositive A r (le_of_not_gt hr),measure_empty]
      simp [F,hr]
  have hinner (x : Space n) : (∫⁻ r : ℝ, F (r,x)) =
      A.indicator (fun x => ENNReal.ofReal (gnomonicDensity x/((n+1:ℕ):ℝ))) x := by
    by_cases hx : x ∈ A
    · have he : (fun r : ℝ => F (r,x)) =
          (Ioo 0 (b x)).indicator (fun r : ℝ => ENNReal.ofReal (r^n)) := by
        funext r
        by_cases hr : 0 < r ∧ r < b x <;> simp [F,hx,Set.mem_Ioo,hr]
      rw [he,lintegral_indicator measurableSet_Ioo]
      rw [Set.indicator_of_mem hx]
      exact gnomonic_radial_integral x
    · simp [F,hx]
  calc
    volume (gnomonicCone A) = ∫⁻ r : ℝ, ∫⁻ x : Space n, F (r,x) := by
      rw [gnomonicCone_volume_slices hA]
      exact lintegral_congr_ae (Filter.Eventually.of_forall hslice)
    _ = ∫⁻ x : Space n, ∫⁻ r : ℝ, F (r,x) := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ x : Space n, A.indicator (fun x => ENNReal.ofReal (gnomonicDensity x/((n+1:ℕ):ℝ))) x :=
      lintegral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = _ := lintegral_indicator hA _

end Falconer

end OAI
