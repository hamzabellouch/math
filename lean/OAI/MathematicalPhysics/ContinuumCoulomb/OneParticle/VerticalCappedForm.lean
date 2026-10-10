import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalSpectralInput
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ExplicitVerticalCutoff
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support

namespace OAI

/-! The actual capped transverse oscillator and its two-part IMS formula.
The cutoff is one on the inner half-slab and zero beyond the slab. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

def verticalCapPotential (freq S z : ℝ) : ℝ :=
  (freq^2/2) * min (z^2) (S^2)

def verticalCappedForm (freq S : ℝ) (u : ℝ → ℝ) : ℝ :=
  (1/2 : ℝ) * (∫ z, deriv u z^2) + ∫ z, verticalCapPotential freq S z * u z^2

def verticalCutoffAngle (S z : ℝ) : ℝ :=
  (Real.pi/2) * verticalCutoffBump ((2/S)*z)

def verticalInnerCutoff (S z : ℝ) : ℝ := Real.sin (verticalCutoffAngle S z)
def verticalOuterCutoff (S z : ℝ) : ℝ := Real.cos (verticalCutoffAngle S z)

theorem verticalCutoffAngle_smooth (S : ℝ) : ContDiff ℝ ∞ (verticalCutoffAngle S) :=
  contDiff_const.mul (verticalCutoffBump.contDiff.comp (contDiff_const.mul contDiff_id))

theorem verticalInnerCutoff_smooth (S : ℝ) : ContDiff ℝ ∞ (verticalInnerCutoff S) :=
  (verticalCutoffAngle_smooth S).sin

theorem verticalOuterCutoff_smooth (S : ℝ) : ContDiff ℝ ∞ (verticalOuterCutoff S) :=
  (verticalCutoffAngle_smooth S).cos

theorem verticalCutoff_partition (S z : ℝ) :
    verticalInnerCutoff S z^2 + verticalOuterCutoff S z^2 = 1 := Real.sin_sq_add_cos_sq _

theorem verticalCutoff_inner {S : ℝ} (hS : 0 < S) {z : ℝ} (hz : |z| ≤ S/2) :
    verticalInnerCutoff S z = 1 ∧ verticalOuterCutoff S z = 0 := by
  have hb : verticalCutoffBump ((2/S)*z) = 1 := by
    apply verticalCutoffBump.one_of_mem_closedBall
    change dist ((2/S)*z) 0 ≤ 1
    rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos (by norm_num) hS)]
    have hm := mul_le_mul_of_nonneg_left hz (div_pos (by norm_num : (0:ℝ)<2) hS).le
    have he : (2/S)*(S/2) = (1:ℝ) := by field_simp
    exact hm.trans_eq he
  simp [verticalInnerCutoff, verticalOuterCutoff, verticalCutoffAngle, hb]

theorem verticalCutoff_outer {S : ℝ} (hS : 0 < S) {z : ℝ} (hz : S ≤ |z|) :
    verticalInnerCutoff S z = 0 ∧ verticalOuterCutoff S z = 1 := by
  have hb : verticalCutoffBump ((2/S)*z) = 0 := by
    apply verticalCutoffBump.zero_of_le_dist
    rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos (by norm_num) hS)]
    have hm := mul_le_mul_of_nonneg_left hz (div_pos (by norm_num : (0:ℝ)<2) hS).le
    have he : (2/S)*S = (2:ℝ) := by field_simp
    exact he.symm.le.trans hm
  simp [verticalInnerCutoff, verticalOuterCutoff, verticalCutoffAngle, hb]

theorem vertical_deriv_square_integrable (u : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) : Integrable (fun z => deriv u z^2) := by
  have hd : Continuous (deriv u) := hu.continuous_deriv (by norm_num)
  have hdc : HasCompactSupport (deriv u) := hc.deriv
  have hsq : HasCompactSupport (fun z => deriv u z^2) :=
    hdc.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  exact (hd.pow 2).integrable_of_hasCompactSupport hsq

theorem vertical_product_integrable (V u : ℝ → ℝ) (hV : Continuous V)
    (hu : Continuous u) (hc : HasCompactSupport u) : Integrable (fun z => V z*u z^2) := by
  have huc : HasCompactSupport (fun z => u z^2) :=
    hc.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hprod : HasCompactSupport (fun z => V z * u z^2) := huc.mul_left
  exact (hV.mul (hu.pow 2)).integrable_of_hasCompactSupport hprod

private theorem verticalCutoffBump_deriv_bounded :
    ∃ C : ℝ, ∀ z, ‖deriv (verticalCutoffBump : ℝ → ℝ) z‖ ≤ C := by
  have hs : ContDiff ℝ 2 (verticalCutoffBump : ℝ → ℝ) := verticalCutoffBump.contDiff
  exact (hs.continuous_deriv (by norm_num)).bounded_above_of_compact_support
    verticalCutoffBump.hasCompactSupport.deriv

def verticalCutoffDerivativeConstant : ℝ := Classical.choose verticalCutoffBump_deriv_bounded

theorem verticalCutoffDerivativeConstant_nonnegative : 0 ≤ verticalCutoffDerivativeConstant :=
  (norm_nonneg _).trans (Classical.choose_spec verticalCutoffBump_deriv_bounded 0)

def verticalCutoffDerivativeBound (S : ℝ) : ℝ :=
  (Real.pi/2 * (2/S)) * verticalCutoffDerivativeConstant

theorem verticalCutoffAngle_deriv (S z : ℝ) :
    deriv (verticalCutoffAngle S) z =
      (Real.pi/2 * (2/S)) * deriv (verticalCutoffBump : ℝ → ℝ) ((2/S)*z) := by
  have hs : ContDiff ℝ 1 (verticalCutoffBump : ℝ → ℝ) := verticalCutoffBump.contDiff
  have hb := (hs.differentiable (by norm_num) ((2/S)*z)).hasDerivAt
  have h := (hb.comp z ((hasDerivAt_id z).const_mul (2/S))).const_mul (Real.pi/2)
  change HasDerivAt (verticalCutoffAngle S) _ z at h
  rw [h.deriv]
  ring

theorem verticalCutoffAngle_deriv_bound {S : ℝ} (hS : 0 < S) (z : ℝ) :
    |deriv (verticalCutoffAngle S) z| ≤ verticalCutoffDerivativeBound S := by
  have hc : 0 ≤ Real.pi/2 * (2/S) := by positivity
  rw [verticalCutoffAngle_deriv, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left
    (Classical.choose_spec verticalCutoffBump_deriv_bounded ((2/S)*z)) hc

theorem verticalCutoff_deriv_identity (S : ℝ) (u : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (z : ℝ) :
    deriv (fun x => verticalInnerCutoff S x*u x) z^2 +
      deriv (fun x => verticalOuterCutoff S x*u x) z^2 =
      deriv u z^2 + deriv (verticalCutoffAngle S) z^2*u z^2 := by
  have ha := (verticalCutoffAngle_smooth S).differentiable (by simp) z
  have hi := ha.hasDerivAt.sin
  have ho := ha.hasDerivAt.cos
  have hu' := (hu.differentiable (by norm_num) z).hasDerivAt
  have hdi : deriv (fun x => verticalInnerCutoff S x*u x) z =
      Real.cos (verticalCutoffAngle S z) * deriv (verticalCutoffAngle S) z * u z +
        Real.sin (verticalCutoffAngle S z) * deriv u z := by
    simpa only [verticalInnerCutoff] using (hi.fun_mul hu').deriv
  have hdo : deriv (fun x => verticalOuterCutoff S x*u x) z =
      -(Real.sin (verticalCutoffAngle S z) * deriv (verticalCutoffAngle S) z) * u z +
        Real.cos (verticalCutoffAngle S z) * deriv u z := by
    simpa only [verticalOuterCutoff, neg_mul] using (ho.fun_mul hu').deriv
  rw [hdi, hdo]
  linear_combination (deriv u z^2 + deriv (verticalCutoffAngle S) z^2*u z^2) *
    Real.sin_sq_add_cos_sq (verticalCutoffAngle S z)

/-- Exact IMS identity on the actual one-dimensional capped form. -/
theorem verticalCappedForm_IMS (freq S : ℝ) (u : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    verticalCappedForm freq S (fun z => verticalInnerCutoff S z*u z) +
      verticalCappedForm freq S (fun z => verticalOuterCutoff S z*u z) =
      verticalCappedForm freq S u + (1/2:ℝ)*∫ z, deriv (verticalCutoffAngle S) z^2*u z^2 := by
  have hi : ContDiff ℝ 1 (verticalInnerCutoff S) := (verticalInnerCutoff_smooth S).of_le (by simp)
  have ho : ContDiff ℝ 1 (verticalOuterCutoff S) := (verticalOuterCutoff_smooth S).of_le (by simp)
  have ha : Continuous (fun z => deriv (verticalCutoffAngle S) z^2) :=
    ((verticalCutoffAngle_smooth S).continuous_deriv (by simp)).pow 2
  have hV : Continuous (verticalCapPotential freq S) := by unfold verticalCapPotential; fun_prop
  have hd : (∫ z, deriv (fun x => verticalInnerCutoff S x*u x) z^2) +
      (∫ z, deriv (fun x => verticalOuterCutoff S x*u x) z^2) =
      (∫ z, deriv u z^2) + ∫ z, deriv (verticalCutoffAngle S) z^2*u z^2 := by
    rw [← integral_add (vertical_deriv_square_integrable _ (hi.mul hu) hc.mul_left)
      (vertical_deriv_square_integrable _ (ho.mul hu) hc.mul_left),
      ← integral_add (vertical_deriv_square_integrable u hu hc)
      (vertical_product_integrable _ u ha hu.continuous hc)]
    exact integral_congr_ae (Filter.Eventually.of_forall (verticalCutoff_deriv_identity S u hu))
  have hp : (∫ z, verticalCapPotential freq S z*(verticalInnerCutoff S z*u z)^2) +
      (∫ z, verticalCapPotential freq S z*(verticalOuterCutoff S z*u z)^2) =
      ∫ z, verticalCapPotential freq S z*u z^2 := by
    rw [← integral_add
      (vertical_product_integrable _ _ hV (hi.mul hu).continuous hc.mul_left)
      (vertical_product_integrable _ _ hV (ho.mul hu).continuous hc.mul_left)]
    apply integral_congr_ae
    filter_upwards [] with z
    linear_combination (verticalCapPotential freq S z*u z^2) * verticalCutoff_partition S z
  unfold verticalCappedForm
  linarith

/-- On the supported inner piece the capped potential is exactly harmonic. -/
theorem verticalCappedForm_inner {S : ℝ} (hS : 0 < S) (freq : ℝ) (u : ℝ → ℝ) :
    verticalCappedForm freq S (fun z => verticalInnerCutoff S z*u z) =
      verticalForm freq (fun z => verticalInnerCutoff S z*u z) := by
  unfold verticalCappedForm verticalForm
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : |z| ≤ S
  · have hs : z^2 ≤ S^2 := by
      nlinarith [sq_abs z, (sq_le_sq₀ (abs_nonneg z) hS.le).mpr hz]
    simp only [verticalCapPotential, min_eq_left hs]
    ring
  · rw [(verticalCutoff_outer hS (le_of_not_ge hz)).1]
    simp

end ContinuumCoulomb

end

end OAI
