import OAI.Dynamics.EntropyCounterexample.SphereDoubling
import OAI.Dynamics.EntropyCounterexample.SphereCharts

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340

lemma doubling_north_eq_chartNorthPole : SphereDoubling.north = chartNorthPole := by
  symm
  apply (SphereDoubling.eq_north_iff chartNorthPole).mpr
  simp [chartNorthPole, chartNorthVector]

lemma stereoCoordinate_sphereOfComplex (z : ℂ) :
    SphereDoubling.stereoCoordinate (sphereOfComplex z).val = z := by
  unfold SphereDoubling.stereoCoordinate
  simp only [sphereOfComplex_val_zero, sphereOfComplex_val_one, sphereOfComplex_val_two]
  push_cast
  have hd : ((‖z‖ : ℝ) : ℂ) ^ 2 + 1 ≠ 0 := by
    have h : (‖z‖ ^ 2 + 1 : ℝ) ≠ 0 := by positivity
    simpa using Complex.ofReal_ne_zero.mpr h
  have hden : (1 : ℂ) - (((‖z‖ : ℝ) : ℂ) ^ 2 - 1) /
      (((‖z‖ : ℝ) : ℂ) ^ 2 + 1) =
      2 / (((‖z‖ : ℝ) : ℂ) ^ 2 + 1) := by
    field_simp
    ring
  rw [hden]
  field_simp
  have hz := Complex.re_add_im z
  linear_combination hz

lemma stereoCoordinate_eq_sphereToComplex {x : StandardSphere2} (hx : x ≠ chartNorthPole) :
    SphereDoubling.stereoCoordinate x.val = sphereToComplex x := by
  rw [← sphereOfComplex_sphereToComplex hx, stereoCoordinate_sphereOfComplex]
  simp

lemma sphereDoubling_sphereOfComplex (z : ℂ) :
    SphereDoubling.sphereMap (sphereOfComplex z) = sphereOfComplex (z ^ 2) := by
  have hz : sphereOfComplex z ≠ SphereDoubling.north := by
    rw [doubling_north_eq_chartNorthPole]
    exact sphereOfComplex_ne_north z
  have hq : SphereDoubling.sphereMap (sphereOfComplex z) ≠ chartNorthPole := by
    rw [← doubling_north_eq_chartNorthPole]
    exact mt (SphereDoubling.sphereMap_eq_north_iff _).mp hz
  rw [← sphereOfComplex_sphereToComplex hq]
  congr 1
  rw [← stereoCoordinate_eq_sphereToComplex hq]
  rw [SphereDoubling.stereoCoordinate_sphereMap hz, stereoCoordinate_sphereOfComplex]

lemma sphereDoubling_complexSphereHomeomorph (z : OnePoint ℂ) :
    SphereDoubling.sphereMap (complexSphereHomeomorph z) =
      complexSphereHomeomorph (OnePoint.map (fun w : ℂ => w ^ 2) z) := by
  induction z using OnePoint.rec with
  | infty =>
    simp [← doubling_north_eq_chartNorthPole]
  | coe z =>
    simpa using sphereDoubling_sphereOfComplex z

lemma sphereDoubling_conjugate :
    SphereDoubling.sphereMap =
      complexSphereHomeomorph ∘ OnePoint.map (fun w : ℂ => w ^ 2) ∘
        complexSphereHomeomorph.symm := by
  funext x
  simpa using sphereDoubling_complexSphereHomeomorph (complexSphereHomeomorph.symm x)

lemma continuous_onePointSquare : Continuous (OnePoint.map (fun w : ℂ => w ^ 2)) := by
  apply complexSphereHomeomorph.isEmbedding.continuous_iff.mpr
  have h := SphereDoubling.continuous_sphereMap.comp complexSphereHomeomorph.continuous
  convert h using 1
  funext z
  exact (sphereDoubling_complexSphereHomeomorph z).symm

end Problem340

end

end OAI
