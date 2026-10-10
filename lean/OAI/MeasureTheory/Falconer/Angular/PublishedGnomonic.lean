import OAI.MeasureTheory.Falconer.Angular.GnomonicChart
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-!
# The published surface-measure formula used for angular integration

Besau, Hack, Pivovarov, Schuster, *Spherical centroid bodies*,
American Journal of Mathematics **145** (2023), 515–542,
DOI 10.1353/ajm.2023.0012, Lemma 2.3(a), with the inverse chart of
Lemma 2.2(a). The authors assume sphere dimension at least two.

Only the exact density of ordinary spherical Lebesgue measure under the
gnomonic chart is assumed. This input contains no incidence or oscillatory
estimate. The resulting integral formulas retain the actual sphere measure
used in `independentAngularEnergy`.
-/

namespace Falconer
open Set MeasureTheory

def PublishedGnomonicSurface : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    Measure.map (@gnomonicChart n)
      ((volume : Measure (Space n)).withDensity (fun x => ENNReal.ofReal (gnomonicDensity x))) =
        (sphereMeasure (n+1)).restrict (northHemisphere n)

theorem gnomonic_integrable (hpublished : PublishedGnomonicSurface)
    {n : ℕ} (hn : 2 ≤ n) {f : Sphere (n+1) → ℂ}
    (hf : Integrable f (sphereMeasure (n+1))) :
    Integrable (fun x : Space n => gnomonicDensity x • f (gnomonicChart x)) := by
  have hm : MeasurePreserving (@gnomonicChart n)
      ((volume : Measure (Space n)).withDensity (fun x => ENNReal.ofReal (gnomonicDensity x)))
      ((sphereMeasure (n+1)).restrict (northHemisphere n)) :=
    ⟨(gnomonicChart_continuous n).measurable,hpublished n hn⟩
  have hi : Integrable (fun x : Space n => f (gnomonicChart x))
      ((volume : Measure (Space n)).withDensity (fun x => ENNReal.ofReal (gnomonicDensity x))) :=
    hm.integrable_comp_of_integrable hf.restrict
  have hh := (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure (Space n)))
    ((gnomonicDensity_continuous n).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hi
  simpa only [ENNReal.toReal_ofReal (gnomonicDensity_pos _).le] using hh

theorem gnomonic_sphere_integral (hpublished : PublishedGnomonicSurface)
    {n : ℕ} (hn : 2 ≤ n) (f : Sphere (n+1) → ℂ) (hf : Measurable f)
    (hs : ∀ w, w ∉ northHemisphere n → f w = 0) :
    (∫ w, f w ∂sphereMeasure (n+1)) =
      ∫ x : Space n, gnomonicDensity x • f (gnomonicChart x) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs,← hpublished n hn,
    integral_map_of_stronglyMeasurable (gnomonicChart_continuous n).measurable hf.stronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      ((gnomonicDensity_continuous n).measurable.ennreal_ofReal)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (gnomonicDensity_pos x).le]

theorem rotated_gnomonic_sphere_integral (hpublished : PublishedGnomonicSurface)
    {n : ℕ} (hn : 2 ≤ n) (e : Space (n+1) ≃ₗᵢ[ℝ] Space (n+1))
    (f : Sphere (n+1) → ℂ) (hf : Measurable f)
    (hs : ∀ w, sphereMap e.symm w ∉ northHemisphere n → f w = 0) :
    (∫ w, f w ∂sphereMeasure (n+1)) =
      ∫ x : Space n, gnomonicDensity x • f (sphereMap e (gnomonicChart x)) := by
  rw [← sphere_integral_rotation e f]
  apply gnomonic_sphere_integral hpublished hn _ (hf.comp (continuous_sphereMap e).measurable)
  intro w hw
  apply hs
  have he : sphereMap e.symm (sphereMap e w) = w := (sphereHomeomorph e).left_inv w
  rw [he]
  exact hw

end Falconer

end OAI
