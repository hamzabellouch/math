import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingMassCutoff
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarScaling

namespace OAI

/-! Smooth concentration tests following an expanding translation gate.
The Laplacian loss has the required inverse-square scaling. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows VelocityDetector Set Filter
open scoped ContDiff Topology

def concentrationCutoff (R : ℝ) (c x : Plane) : ℝ :=
  massCutoff (scalarAffineScale R⁻¹ c x)

theorem concentrationCutoff_smooth (R : ℝ) (c : Plane) :
    ContDiff ℝ ∞ (concentrationCutoff R c) :=
  massCutoff_smooth.comp (scalarAffineScale_smooth _ _)

theorem concentrationCutoff_range (R : ℝ) (c x : Plane) :
    concentrationCutoff R c x ∈ Icc (0 : ℝ) 1 := massCutoff_range _

theorem concentrationCutoff_support {R : ℝ} (hR : 0 < R) (c : Plane) :
    Function.support (concentrationCutoff R c) ⊆ {x | ∀ j, |x j - c j| ≤ R} := by
  intro x hx j
  have hb := massCutoff_support (subset_closure hx) j
  change |R⁻¹ * (x j - c j)| ≤ 1 at hb
  rw [abs_mul, abs_of_pos (inv_pos.mpr hR), ← div_eq_inv_mul] at hb
  simpa only [one_mul] using (div_le_iff₀ hR).mp hb

theorem concentrationCutoff_compactSupport {R : ℝ} (hR : 0 < R) (c : Plane) :
    HasCompactSupport (concentrationCutoff R c) := by
  apply HasCompactSupport.intro (K := Icc (fun j => c j - R) (fun j => c j + R)) isCompact_Icc
  intro x hx
  by_contra hn
  have hb := concentrationCutoff_support hR c hn
  apply hx
  constructor <;> intro j
  · linarith [(abs_le.mp (hb j)).1]
  · linarith [(abs_le.mp (hb j)).2]

theorem concentrationCutoff_one_near {R : ℝ} (hR : 0 < R) {c x : Plane}
    (hx : ∀ j, |x j - c j| < (2 / 3) * R) :
    concentrationCutoff R c =ᶠ[𝓝 x] fun _ => 1 := by
  have he : massCutoff =ᶠ[𝓝 (scalarAffineScale R⁻¹ c x)] fun _ => 1 := by
    apply massCutoff_one_near
    intro j
    change |R⁻¹ * (x j - c j)| < 2 / 3
    rw [abs_mul, abs_of_pos (inv_pos.mpr hR), ← div_eq_inv_mul]
    exact (div_lt_iff₀ hR).mpr (hx j)
  exact he.comp_tendsto (scalarAffineScale_smooth R⁻¹ c).continuous.continuousAt

theorem concentrationCutoff_one {R : ℝ} (hR : 0 < R) {c x : Plane}
    (hx : ∀ j, |x j - c j| < (2 / 3) * R) : concentrationCutoff R c x = 1 :=
  (concentrationCutoff_one_near hR hx).eq_of_nhds

theorem concentrationCutoff_laplacian {C : ℝ}
    (hC : ∀ x, |scalarLaplacian massCutoff x| ≤ C) (R : ℝ) (c x : Plane) :
    |scalarLaplacian (concentrationCutoff R c) x| ≤ R⁻¹ ^ 2 * C := by
  change |scalarLaplacian (fun y => massCutoff (scalarAffineScale R⁻¹ c y)) x| ≤ _
  rw [scalarLaplacian_affine_scale massCutoff_smooth, abs_mul,
    abs_of_nonneg (sq_nonneg R⁻¹)]
  exact mul_le_mul_of_nonneg_left (hC _) (sq_nonneg _)

theorem concentrationCutoff_timeDerivative (R : ℝ) {c : ℝ → Plane}
    (hc : ContDiff ℝ ∞ c) (t : ℝ) (x : Plane) :
    HasDerivAt (fun s => concentrationCutoff R (c s) x)
      (-fderiv ℝ (concentrationCutoff R (c t)) x (deriv c t)) t := by
  have hinner : HasDerivAt (fun s => scalarAffineScale R⁻¹ (c s) x)
      (-(R⁻¹ • deriv c t)) t := by
    convert (((hc.differentiable (by simp) t).hasDerivAt).const_sub x).const_smul R⁻¹
      using 1
    · rfl
    · ext j
      simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, mul_neg]
  have ht := (massCutoff_smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t hinner
  have hs := (massCutoff_smooth.differentiable (by simp) _).hasFDerivAt.comp x
    (scalarAffineScale_hasFDerivAt R⁻¹ (c t) x)
  change HasFDerivAt (concentrationCutoff R (c t)) _ x at hs
  rw [hs.fderiv]
  convert ht using 1 <;> simp [concentrationCutoff, Function.comp_def]

end ForcedComputation.ExpandingDetector

end

end OAI
