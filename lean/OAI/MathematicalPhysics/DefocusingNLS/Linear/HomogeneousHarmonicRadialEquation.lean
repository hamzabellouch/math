import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicAnnularTesting
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialLaplacianGreen
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousAngularProjection
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

namespace OAI

/-! # The classical radial equation for an angular projection

The angular eigenfunction and its degree-zero extension are explicit data.
The radial differential equation follows from Cartesian Green's identity;
no completeness or spectral decomposition assumption is used.
-/

open Set Filter MeasureTheory
open scoped ContDiff SchwartzMap Laplacian

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem harmonicAngularCoefficient_continuous (Y F : E → ℂ)
    (hY : Continuous (fun z : PhysicalUnitSphere => Y z.1)) (hF : Continuous F) :
    Continuous (harmonicAngularCoefficient Y F) := by
  have h : Continuous (fun p : ℝ × PhysicalUnitSphere => Y p.2.1 * F (p.1 • p.2.1)) :=
    (hY.comp continuous_snd).mul
      (hF.comp (continuous_fst.smul continuous_snd.subtype_val))
  change Continuous (fun r : ℝ => ∫ z : PhysicalUnitSphere,
    Y z.1 * F (r • z.1) ∂physicalSphereMeasure)
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ := physicalSphereMeasure)
      (f := fun (r : ℝ) (z : PhysicalUnitSphere) => Y z.1 * F (r • z.1)) h isCompact_univ)

private theorem test_and_derivatives_zero_nonpositive (φ : 𝓢(ℝ, ℂ))
    (hs : tsupport φ ⊆ Ioi (0 : ℝ)) (r : ℝ) (hr : r ≤ 0) :
    φ r = 0 ∧ deriv φ r = 0 ∧ deriv (deriv φ) r = 0 := by
  let φ' := SchwartzMap.derivCLM ℂ ℂ φ
  let φ'' := SchwartzMap.derivCLM ℂ ℂ φ'
  have hz : r ∉ tsupport φ := fun h => (not_lt_of_ge hr) (hs h)
  have hz' : r ∉ tsupport φ' := fun h => hz (SchwartzMap.tsupport_derivCLM_subset ℂ φ h)
  have hz'' : r ∉ tsupport φ'' := fun h => hz' (SchwartzMap.tsupport_derivCLM_subset ℂ φ' h)
  exact ⟨image_eq_zero_of_notMem_tsupport hz,
    image_eq_zero_of_notMem_tsupport hz', image_eq_zero_of_notMem_tsupport hz''⟩

theorem harmonicAngularCoefficient_weighted_laplacian
    (Y F : E → ℂ) (lam : ℂ)
    (hY : ∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x)
    (hRay : ∀ (x : E) (t : ℝ), 0 < t → Y (t • x) = Y x)
    (hEigen : ∀ x : E, x ≠ 0 → Δ Y x = -(lam / (‖x‖ ^ 2 : ℝ)) * Y x)
    (hF : ContDiff ℝ 2 F)
    (φ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi (0 : ℝ)) :
    (∫ r : ℝ, φ r * ((r : ℂ) ^ 11 * harmonicAngularCoefficient Y (Δ F) r)) =
    ∫ r : ℝ, ((r : ℂ) ^ 11 * deriv (deriv φ) r +
      11 * (r : ℂ) ^ 10 * deriv φ r - lam * (r : ℂ) ^ 9 * φ r) *
        harmonicAngularCoefficient Y F r := by
  have hw := harmonicAngularCoefficient_annular_laplacian Y F lam hY hRay hEigen hF φ hc hs
  have hleft : (∫ r : PhysicalPositiveRadius, φ r * harmonicAngularCoefficient Y (Δ F) r
      ∂physicalRadiusMeasure) =
      ∫ r : ℝ, φ r * ((r : ℂ) ^ 11 * harmonicAngularCoefficient Y (Δ F) r) := by
    rw [integral_physicalRadiusMeasure
      (fun r : ℝ => φ r * harmonicAngularCoefficient Y (Δ F) r)]
    calc
      _ = ∫ r in Ioi (0 : ℝ), φ r * ((r : ℂ) ^ 11 *
          harmonicAngularCoefficient Y (Δ F) r) := by
        apply integral_congr_ae
        filter_upwards [] with r
        simp only [Complex.real_smul, Complex.ofReal_pow]
        ring
      _ = _ := integral_Ioi_eq_of_zero_nonpositive _ (fun r hr => by
        rw [(test_and_derivatives_zero_nonpositive φ hs r hr).1, zero_mul])
  have hright : (∫ r : PhysicalPositiveRadius,
      (deriv (deriv φ) r + ((11 / r.1 : ℝ) : ℂ) * deriv φ r -
        lam / (r.1 ^ 2 : ℝ) * φ r) * harmonicAngularCoefficient Y F r
        ∂physicalRadiusMeasure) =
      ∫ r : ℝ, ((r : ℂ) ^ 11 * deriv (deriv φ) r +
        11 * (r : ℂ) ^ 10 * deriv φ r - lam * (r : ℂ) ^ 9 * φ r) *
          harmonicAngularCoefficient Y F r := by
    rw [integral_physicalRadiusMeasure (fun r : ℝ =>
      (deriv (deriv φ) r + ((11 / r : ℝ) : ℂ) * deriv φ r -
        lam / (r ^ 2 : ℝ) * φ r) * harmonicAngularCoefficient Y F r)]
    calc
      _ = ∫ r in Ioi (0 : ℝ), ((r : ℂ) ^ 11 * deriv (deriv φ) r +
          11 * (r : ℂ) ^ 10 * deriv φ r - lam * (r : ℂ) ^ 9 * φ r) *
            harmonicAngularCoefficient Y F r := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
        simp only [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat]
        field_simp [hrC]
      _ = _ := integral_Ioi_eq_of_zero_nonpositive _ (fun r hr => by
        obtain ⟨h0, h1, h2⟩ := test_and_derivatives_zero_nonpositive φ hs r hr
        simp only [h0, h1, h2, mul_zero, add_zero, sub_zero, zero_mul])
  exact hleft.symm.trans (hw.trans hright)

private theorem compact_positive_test_integrable (G : ℝ → ℂ)
    (hG : ContinuousOn G (Ioi (0 : ℝ))) (φ : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Integrable (fun r => φ r * G r) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_left _ _).trans (subset_tsupport φ))).mp
  exact IntegrableOn.continuousOn_mul φ.continuous.continuousOn
    (hG.locallyIntegrableOn measurableSet_Ioi |>.integrableOn_compact_subset hs hc) hc

theorem radial_laplacian_eq_of_weighted_tests (A B : ℝ → ℂ) (lam : ℂ)
    (hA : ContDiff ℝ 2 A) (hB : ContinuousOn B (Ioi (0 : ℝ)))
    (htest : ∀ φ : 𝓢(ℝ, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ioi (0 : ℝ) →
      (∫ r : ℝ, φ r * ((r : ℂ) ^ 11 * B r)) =
      ∫ r : ℝ, ((r : ℂ) ^ 11 * deriv (deriv φ) r +
        11 * (r : ℂ) ^ 10 * deriv φ r - lam * (r : ℂ) ^ 9 * φ r) * A r) :
    ∀ r : ℝ, 0 < r → B r = deriv (deriv A) r +
      ((11 / r : ℝ) : ℂ) * deriv A r - lam / (r ^ 2 : ℝ) * A r := by
  let L : ℝ → ℂ := fun r => (r : ℂ) ^ 11 * deriv (deriv A) r +
    11 * (r : ℂ) ^ 10 * deriv A r - lam * (r : ℂ) ^ 9 * A r
  let G : ℝ → ℂ := fun r => (r : ℂ) ^ 11 * B r
  let R : ℝ → ℂ := fun r => G r - L r
  have hLc : Continuous L :=
    (((Complex.continuous_ofReal.pow 11).mul
      ((hA.deriv' : ContDiff ℝ 1 (deriv A)).continuous_deriv (by norm_num))).add
      ((continuous_const.mul (Complex.continuous_ofReal.pow 10)).mul
        (hA.continuous_deriv (by norm_num)))).sub
      ((continuous_const.mul (Complex.continuous_ofReal.pow 9)).mul hA.continuous)
  have hGc : ContinuousOn G (Ioi (0 : ℝ)) :=
    (Complex.continuous_ofReal.pow 11).continuousOn.mul hB
  have hRc : ContinuousOn R (Ioi (0 : ℝ)) := hGc.sub hLc.continuousOn
  have heq := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hRc.locallyIntegrableOn measurableSet_Ioi) (by
      intro φ hφ hc hs
      have hcc : HasCompactSupport (fun r => (φ r : ℂ)) :=
        hc.comp_left (g := Complex.ofReal) (by simp)
      let ψ : 𝓢(ℝ, ℂ) := hcc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφ)
      have hψc : HasCompactSupport ψ := hcc
      have hψs : tsupport ψ ⊆ Ioi (0 : ℝ) := by
        change closure (Function.support (fun r => (φ r : ℂ))) ⊆ Ioi (0 : ℝ)
        have he : Function.support (fun r => (φ r : ℂ)) = Function.support φ := by
          ext r
          simp
        rwa [he]
      have hiG := compact_positive_test_integrable G hGc ψ hψc hψs
      have hiL := compact_positive_test_integrable L hLc.continuousOn ψ hψc hψs
      have hh : (∫ r : ℝ, ψ r * G r) = ∫ r : ℝ, ψ r * L r :=
        (htest ψ hψc hψs).trans (radial_laplacian_green ψ hψc A hA lam)
      calc
        (∫ r : ℝ, φ r • R r) = ∫ r : ℝ, ψ r * G r - ψ r * L r := by
          apply integral_congr_ae
          filter_upwards [] with r
          change φ r • (G r - L r) = (φ r : ℂ) * G r - (φ r : ℂ) * L r
          rw [Complex.real_smul, mul_sub]
        _ = (∫ r : ℝ, ψ r * G r) - ∫ r : ℝ, ψ r * L r := integral_sub hiG hiL
        _ = 0 := sub_eq_zero.mpr hh)
  have hz : EqOn R (fun _ => (0 : ℂ)) (Ioi (0 : ℝ)) :=
    Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' measurableSet_Ioi).mpr heq)
      isOpen_Ioi hRc continuousOn_const
  intro r hr
  have hL : (r : ℂ) ^ 11 * B r = L r := sub_eq_zero.mp (hz hr)
  apply mul_left_cancel₀ (pow_ne_zero 11 (Complex.ofReal_ne_zero.mpr hr.ne'))
  rw [hL]
  dsimp only [L]
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  push_cast
  field_simp [hrC]

/-- The actual homogeneous-space physical realization satisfies the
classical radial Laplacian identity in every explicit harmonic channel. -/
theorem homogeneous_harmonic_radial_laplacian
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (u : HomogeneousY a k) (Y : E → ℂ) (lam : ℂ)
    (hY : ∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x)
    (hRay : ∀ (x : E) (t : ℝ), 0 < t → Y (t • x) = Y x)
    (hEigen : ∀ x : E, x ≠ 0 → Δ Y x = -(lam / (‖x‖ ^ 2 : ℝ)) * Y x)
    (r : ℝ) (hr : 0 < r) :
    harmonicAngularCoefficient Y (Δ (fun x : E => homogeneousPhysicalCLM a k ha ha1 hk u x)) r =
      deriv (deriv (harmonicAngularCoefficient Y (homogeneousPhysicalCLM a k ha ha1 hk u))) r +
      ((11 / r : ℝ) : ℂ) *
        deriv (harmonicAngularCoefficient Y (homogeneousPhysicalCLM a k ha ha1 hk u)) r -
      lam / (r ^ 2 : ℝ) *
        harmonicAngularCoefficient Y (homogeneousPhysicalCLM a k ha ha1 hk u) r := by
  let F : E → ℂ := homogeneousPhysicalCLM a k ha ha1 hk u
  have hF : ContDiff ℝ 2 F := contDiff_homogeneousPhysical a k ha ha1 hk u
  have hYs : Continuous (fun z : PhysicalUnitSphere => Y z.1) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hz : z.1 ≠ 0 := by
      have hn : ‖z.1‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using z.2
      intro he
      simp [he] at hn
    exact (hY z.1 hz).continuousAt.comp continuous_subtype_val.continuousAt
  let h : PhysicalUnitSphere → ℂ := fun z => star (Y z.1)
  have hh : MemLp h 2 physicalSphereMeasure := by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hYs.star.continuousOn
    exact MemLp.of_bound hYs.star.aestronglyMeasurable B
      (Eventually.of_forall fun z => hB z (mem_univ z))
  have hA : ContDiff ℝ 2 (harmonicAngularCoefficient Y F) := by
    have he : homogeneousAngularProjection a k ha ha1 hk h u =
        harmonicAngularCoefficient Y F := by
      funext t
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [h, RCLike.inner_apply', starRingEnd_apply, star_star, F]
    rw [← he]
    exact contDiff_homogeneousAngularProjection a k ha ha1 hk h hh u
  apply radial_laplacian_eq_of_weighted_tests
    (harmonicAngularCoefficient Y F) (harmonicAngularCoefficient Y (Δ F)) lam hA
    (harmonicAngularCoefficient_continuous Y (Δ F) hYs
      (continuous_laplacian_of_contDiff_two F hF)).continuousOn
    (fun φ hc hs => harmonicAngularCoefficient_weighted_laplacian
      Y F lam hY hRay hEigen hF φ hc hs) r hr

end DefocusingNLS

end OAI
