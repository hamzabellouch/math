import OAI.Dynamics.EntropyCounterexample.Saturation
import OAI.Dynamics.EntropyCounterexample.SphereCompactSupport
import OAI.Dynamics.EntropyCounterexample.SphereCharts

namespace OAI

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace Problem340

def saturationOnEquator (R : ℝ) (hR : 1 ≤ R)
    (w : (ℝ ∙ chartNorthVector)ᗮ) : ℂ :=
  saturation R hR ((1 / 2 : ℝ) • chartEquatorEquiv.symm w)

theorem saturationOnEquator_contDiff (R : ℝ) (hR : 1 ≤ R) :
    ContDiff ℝ ∞ (saturationOnEquator R hR) :=
  (saturation_contDiff R hR).comp
    (chartEquatorEquiv.symm.contDiff.const_smul (1 / 2 : ℝ))

theorem saturationOnEquator_hasCompactSupport (R : ℝ) (hR : 1 ≤ R) :
    HasCompactSupport (saturationOnEquator R hR) := by
  convert (saturation_hasCompactSupport R hR).comp_homeomorph scaledChartEquator.symm using 1
  funext w
  simp [saturationOnEquator, scaledChartEquator, div_eq_mul_inv]

def standardSphereSaturation (R : ℝ) (hR : 1 ≤ R) : StandardSphere2 → ℂ :=
  SphereCompactSupport.extension (saturationOnEquator R hR)

@[simp] theorem standardSphereSaturation_north (R : ℝ) (hR : 1 ≤ R) :
    standardSphereSaturation R hR chartNorthPole = 0 := by
  exact SphereCompactSupport.extension_pole norm_chartNorthVector _

@[simp] theorem standardSphereSaturation_affine (R : ℝ) (hR : 1 ≤ R) (z : ℂ) :
    standardSphereSaturation R hR (sphereOfComplex z) = saturation R hR z := by
  unfold standardSphereSaturation
  rw [SphereCompactSupport.extension_of_ne]
  · change saturation R hR (sphereToComplex (sphereOfComplex z)) = _
    rw [sphereToComplex_sphereOfComplex]
  · intro h
    exact sphereOfComplex_ne_north z (Subtype.ext h)

theorem standardSphereSaturation_eq_transport (R : ℝ) (hR : 1 ≤ R) (x : StandardSphere2) :
    standardSphereSaturation R hR x = sphereSaturation R hR (complexSphereHomeomorph.symm x) := by
  obtain ⟨z, rfl⟩ := complexSphereHomeomorph.surjective x
  induction z using OnePoint.rec with
  | infty => simp
  | coe z => simp

theorem standardSphereSaturation_continuous (R : ℝ) (hR : 1 ≤ R) :
    Continuous (standardSphereSaturation R hR) :=
  SphereCompactSupport.continuous_extension norm_chartNorthVector
    (saturationOnEquator_contDiff R hR) (saturationOnEquator_hasCompactSupport R hR)

theorem standardSphereSaturation_local_ambient (R : ℝ) (hR : 1 ≤ R)
    (x : StandardSphere2) :
    ∃ U : Set SphereAmbient, IsOpen U ∧ (x : SphereAmbient) ∈ U ∧
      ∃ A : SphereAmbient → ℂ, ContDiffOn ℝ ∞ A U ∧
        ∀ y : StandardSphere2, (y : SphereAmbient) ∈ U →
          standardSphereSaturation R hR y = A y :=
  SphereCompactSupport.exists_local_ambient_extension norm_chartNorthVector
    (saturationOnEquator_contDiff R hR) (saturationOnEquator_hasCompactSupport R hR) x

theorem norm_standardSphereSaturation_le_two (R : ℝ) (hR : 1 ≤ R) (x : StandardSphere2) :
    ‖standardSphereSaturation R hR x‖ ≤ 2 := by
  rw [standardSphereSaturation_eq_transport]
  exact norm_sphereSaturation_le_two R hR _

end Problem340

end

end OAI
