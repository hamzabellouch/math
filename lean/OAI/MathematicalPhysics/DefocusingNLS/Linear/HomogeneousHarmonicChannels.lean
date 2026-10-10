import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicTransport
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousInhomogeneousChannels

namespace OAI

/-! # Actual generator vectors satisfy the projected radial system

The source is the actual strong generator derivative. Thus the same result
applies both to eigenvectors and to the inhomogeneous vectors in Jordan chains.
-/

open MeasureTheory Set Filter
open scoped ContDiff Laplacian

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneous_harmonic_project_equation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u v : HomogeneousY a k)
    (S Y : E → ℂ) (eta cD cE : ℂ) (alpha beta : ℝ → ℂ)
    (hY : ∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x)
    (hRay : ∀ (x : E) (t : ℝ), 0 < t → Y (t • x) = Y x)
    (hEigen : ∀ x : E, x ≠ 0 → Δ Y x = -(eta / (‖x‖ ^ 2 : ℝ)) * Y x)
    (hS : ∀ x : E, S x =
      cD * Δ (fun y => homogeneousPhysicalCLM a k ha ha1 hk u y) x +
      cE * fderiv ℝ (fun y => homogeneousPhysicalCLM a k ha ha1 hk u y) x x +
      alpha ‖x‖ * homogeneousPhysicalCLM a k ha ha1 hk u x +
      beta ‖x‖ * homogeneousPhysicalCLM a k ha ha1 hk v x)
    (r : ℝ) (hr : 0 < r) :
    let A := harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a k ha ha1 hk u x)
    let B := harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a k ha ha1 hk v x)
    harmonicAngularCoefficient Y S r =
      cD * (deriv (deriv A) r + ((11 / r : ℝ) : ℂ) * deriv A r -
        eta / (r ^ 2 : ℝ) * A r) + cE * ((r : ℂ) * deriv A r) +
      alpha r * A r + beta r * B r := by
  let F : E → ℂ := fun x => homogeneousPhysicalCLM a k ha ha1 hk u x
  let G : E → ℂ := fun x => homogeneousPhysicalCLM a k ha ha1 hk v x
  let T : E → ℂ := fun x => fderiv ℝ F x x
  have hF : ContDiff ℝ 2 F := contDiff_homogeneousPhysical a k ha ha1 hk u
  have hG : ContDiff ℝ 2 G := contDiff_homogeneousPhysical a k ha ha1 hk v
  have hT : Continuous T :=
    (contDiff_one_iff_fderiv.mp (hF.of_le (by norm_num))).2.clm_apply continuous_id
  have hYs := continuous_harmonicSphere Y hY
  have he : harmonicAngularCoefficient Y S r =
      harmonicAngularCoefficient Y
        (fun x => cD * Δ F x + cE * T x + alpha r * F x + beta r * G x) r := by
    apply integral_congr_ae
    filter_upwards [] with z
    have hn : ‖r • z.1‖ = r := by
      have hz : ‖z.1‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using z.2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hz, mul_one]
    rw [hS, hn]
  rw [harmonicAngularCoefficient_four Y (Δ F) T F G hYs
    (continuous_laplacian_of_contDiff_two F hF) hT hF.continuous hG.continuous
    cD cE (alpha r) (beta r) r] at he
  rw [homogeneous_harmonic_radial_laplacian a k ha ha1 hk u Y eta hY hRay hEigen r hr,
    homogeneous_harmonic_euler a k ha ha1 hk u Y hYs r] at he
  exact he

/-- The strong generator equation becomes the exact two-channel radial
system under every explicit spherical harmonic test. -/
theorem homogeneous_generator_harmonic_channels (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (q : HomogeneousY a k) (Q : ℝ → ℂ)
    (hq : ∀ x : E, homogeneousPhysicalCLM a k ha ha1 hk q x = Q ‖x‖)
    (w z : HomogeneousY a k × HomogeneousY a k)
    (hw : HasDerivWithinAt (fun t : ℝ =>
      homogeneousComplexLinearizedStep a b k ha ha1 hk m q t.toNNReal w) z (Ici 0) 0)
    (Y : E → ℂ) (eta : ℂ)
    (hY : ∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x)
    (hRay : ∀ (x : E) (t : ℝ), 0 < t → Y (t • x) = Y x)
    (hEigen : ∀ x : E, x ≠ 0 → Δ Y x = -(eta / (‖x‖ ^ 2 : ℝ)) * Y x) :
    let P := fun f : HomogeneousY a k => fun x : E => homogeneousPhysicalCLM a k ha ha1 hk f x
    let A := fun f : HomogeneousY a k => harmonicAngularCoefficient Y (P f)
    let D := fun r : ℝ => ((m + 1 : ℕ) : ℂ) * Q r ^ m * star (Q r) ^ m
    let C := fun r : ℝ => (m : ℂ) * Q r ^ (m + 1) * star (Q r) ^ (m - 1)
    ContDiff ℝ 2 (A w.1) ∧ ContDiff ℝ 2 (A w.2) ∧ ∀ r : ℝ, 0 < r →
      (A z.1 r = Complex.I * (deriv (deriv (A w.1)) r +
        ((11 / r : ℝ) : ℂ) * deriv (A w.1) r - eta / (r ^ 2 : ℝ) * A w.1 r) -
        (r / 2 : ℝ) * deriv (A w.1) r + (-(a : ℂ) + Complex.I * (b : ℂ)) * A w.1 r -
        Complex.I * (D r * A w.1 r + C r * A w.2 r)) ∧
      (A z.2 r = -Complex.I * (deriv (deriv (A w.2)) r +
        ((11 / r : ℝ) : ℂ) * deriv (A w.2) r - eta / (r ^ 2 : ℝ) * A w.2 r) -
        (r / 2 : ℝ) * deriv (A w.2) r + (-(a : ℂ) - Complex.I * (b : ℂ)) * A w.2 r +
        Complex.I * (star (D r) * A w.2 r + star (C r) * A w.1 r)) := by
  let P := fun f : HomogeneousY a k => fun x : E => homogeneousPhysicalCLM a k ha ha1 hk f x
  let A := fun f : HomogeneousY a k => harmonicAngularCoefficient Y (P f)
  let D := fun r : ℝ => ((m + 1 : ℕ) : ℂ) * Q r ^ m * star (Q r) ^ m
  let C := fun r : ℝ => (m : ℂ) * Q r ^ (m + 1) * star (Q r) ^ (m - 1)
  have hYs := continuous_harmonicSphere Y hY
  refine ⟨homogeneous_harmonic_contDiff a k ha ha1 hk w.1 Y hYs,
    homogeneous_harmonic_contDiff a k ha ha1 hk w.2 Y hYs, ?_⟩
  obtain ⟨_, _, hpde⟩ := homogeneous_generator_classical_channels a b k ha ha1 hk m q w z hw
  intro r hr
  constructor
  · have hs : ∀ x : E, P z.1 x =
        Complex.I * Δ (P w.1) x + (-(1 / 2 : ℂ)) * fderiv ℝ (P w.1) x x +
        (-(a : ℂ) + Complex.I * (b : ℂ) - Complex.I * D ‖x‖) * P w.1 x +
        (-Complex.I * C ‖x‖) * P w.2 x := by
      intro x
      have hx := (hpde x).1
      dsimp only at hx
      rw [hq] at hx
      dsimp only [P, D, C]
      rw [hx]
      ring
    have he := homogeneous_harmonic_project_equation a k ha ha1 hk w.1 w.2 (P z.1)
      Y eta Complex.I (-(1 / 2 : ℂ))
      (fun t => -(a : ℂ) + Complex.I * (b : ℂ) - Complex.I * D t)
      (fun t => -Complex.I * C t) hY hRay hEigen hs r hr
    dsimp only [A, P, D, C] at he ⊢
    rw [he]
    push_cast
    ring
  · have hs : ∀ x : E, P z.2 x =
        -Complex.I * Δ (P w.2) x + (-(1 / 2 : ℂ)) * fderiv ℝ (P w.2) x x +
        (-(a : ℂ) - Complex.I * (b : ℂ) + Complex.I * star (D ‖x‖)) * P w.2 x +
        (Complex.I * star (C ‖x‖)) * P w.1 x := by
      intro x
      have hx := (hpde x).2
      dsimp only at hx
      rw [hq] at hx
      dsimp only [P, D, C]
      rw [hx]
      ring
    have he := homogeneous_harmonic_project_equation a k ha ha1 hk w.2 w.1 (P z.2)
      Y eta (-Complex.I) (-(1 / 2 : ℂ))
      (fun t => -(a : ℂ) - Complex.I * (b : ℂ) + Complex.I * star (D t))
      (fun t => Complex.I * star (C t)) hY hRay hEigen hs r hr
    dsimp only [A, P, D, C] at he ⊢
    rw [he]
    push_cast
    ring

end DefocusingNLS

end OAI
