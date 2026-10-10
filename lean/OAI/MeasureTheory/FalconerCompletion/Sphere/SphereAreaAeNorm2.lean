import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Fourier.SchwartzNormMonomialIntegrable2
import OAI.MeasureTheory.FalconerCompletion.Fourier.SphereConeToLp2

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set Metric
open scoped ContDiff SchwartzMap FourierTransform RealInnerProductSpace Topology
variable {n : ℕ}

lemma sphereAreaND_ae_norm :
    ∀ᵐ w ∂sphereAreaND n, ‖w‖ = 1 := by
  rw [sphereAreaND, ae_map_iff measurable_subtype_coe.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet]
  exact Filter.Eventually.of_forall (fun w => by simp)

lemma sphereChartND_mem_image_ball {w : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)}
    (hw : ‖w‖ = 1) (ht : -1 < (WithLp.ofLp w).2) :
    w ∈ sphereChartND '' ball (0 : EuclideanSpace ℝ (Fin n)) 2 :=
  ⟨sphereChartInvND w, sphereChartInvND_mem_ball hw ht, sphereChartND_right_inv hw ht⟩

lemma integral_sphereAreaND_eq_quadratic
    {b : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hr2 : r < 2) (hb : StronglyMeasurable b)
    (hsupp : ∀ w, ‖w‖ = 1 → (WithLp.ofLp w).2 ≤ 1-r^2/2 → b w = 0) (Λ : ℝ) :
    (∫ w, Complex.exp (Complex.I * Λ *
      (inner ℝ w (WithLp.toLp 2 (0,(1:ℝ))) : ℂ)) * b w ∂sphereAreaND n) =
      Complex.exp (Complex.I * Λ) * ∫ u : EuclideanSpace ℝ (Fin n),
        Complex.exp (-(((Λ/2:ℝ) : ℂ)*Complex.I)*(‖u‖:ℂ)^2) * sphereChartAmplitudeND b u := by
  have hleft : (∫ w in sphereChartND '' ball (0 : EuclideanSpace ℝ (Fin n)) 2,
        Complex.exp (Complex.I * Λ *
          (inner ℝ w (WithLp.toLp 2 (0,(1:ℝ))) : ℂ)) * b w ∂sphereAreaND n) =
      ∫ w, Complex.exp (Complex.I * Λ *
          (inner ℝ w (WithLp.toLp 2 (0,(1:ℝ))) : ℂ)) * b w ∂sphereAreaND n := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [sphereAreaND_ae_norm] with w hw hwi
    have ht : (WithLp.ofLp w).2 ≤ -1 :=
      le_of_not_gt (fun ht => hwi (sphereChartND_mem_image_ball hw ht))
    rw [hsupp w hw (by nlinarith), mul_zero]
  rw [← hleft, integral_sphereAreaND_quadratic hb measurableSet_ball Subset.rfl]
  congr 1
  simp only [← neg_mul, sphereChartAmplitudeND]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  have hu' : 2 ≤ ‖u‖ := by simpa using hu
  rw [sphereChartWeightND_zero hu']
  simp

lemma norm_exp_I_mul_real (Λ : ℝ) : ‖Complex.exp (Complex.I * (Λ:ℂ))‖ = 1 := by
  simp [Complex.norm_exp,Complex.mul_re]

theorem sphere_stationaryND_chart
    {b : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hr2 : r < 2) (hb : ContDiff ℝ ∞ b)
    (hsupp : ∀ w, ‖w‖ = 1 → (WithLp.ofLp w).2 ≤ 1-r^2/2 → b w = 0)
    {Λ : ℝ} (hΛ : 0 < Λ) (J : ℕ) :
    let φ := sphereChartSchwartzND b r hr hr2 hb hsupp
    ‖(∫ w, Complex.exp (Complex.I * Λ *
      (inner ℝ w (WithLp.toLp 2 (0,(1:ℝ))) : ℂ)) * b w ∂sphereAreaND n) -
      Complex.exp (Complex.I * Λ) *
        (fresnelCoefficientND (EuclideanSpace ℝ (Fin n)) (Λ/2) * quadraticExpansionND φ J (Λ/2))‖ ≤
      (Real.pi/(Λ/2))^((n:ℝ)/2) * ((Real.pi^2/(Λ/2))^(J+1)/(J.factorial:ℝ)) *
        ∫ ξ : EuclideanSpace ℝ (Fin n), ‖ξ‖^(2*(J+1))*‖𝓕⁻ φ ξ‖ := by
  dsimp only
  rw [integral_sphereAreaND_eq_quadratic hr hr2 hb.continuous.stronglyMeasurable hsupp,
    ← mul_sub, norm_mul, norm_exp_I_mul_real, one_mul]
  simpa [sphereChartSchwartzND] using quadratic_stationaryND_expansion (show 0 < Λ/2 by positivity)
    (sphereChartSchwartzND b r hr hr2 hb hsupp) J

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
