import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarNormalized
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalEnergy
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Actual localized modes in planar/transverse coordinates. The measure is
the product of planar Euclidean volume and one-dimensional Lebesgue measure.
The split Laplacian below is the sum of the three coordinate derivatives. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

abbrev SplitPosition := PlanarPosition × ℝ

def localizedMode (freq : ℝ) (u : PlanarPosition) (p : SplitPosition) : ℝ :=
  normalizedPlanarMode (p.1 - u) * verticalMode freq p.2

def localizedPotential (freq : ℝ) (u : PlanarPosition) (p : SplitPosition) : ℝ :=
  manufacturedPlanarWell (p.1 - u) + freq ^ 2 * p.2 ^ 2 / 2

def splitLaplacian (f : SplitPosition → ℝ) (p : SplitPosition) : ℝ :=
  planarLaplacian (fun r => f (r, p.2)) p.1 +
    deriv (deriv (fun z => f (p.1, z))) p.2

theorem localizedMode_C7 (freq : ℝ) (u : PlanarPosition) :
    ContDiff ℝ 7 (localizedMode freq u) :=
  (normalizedPlanarMode_C7.comp (contDiff_fst.sub contDiff_const)).mul
    (((verticalMode_smooth freq).of_le (by simp)).comp contDiff_snd)

theorem localizedMode_positive {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (p : SplitPosition) : 0 < localizedMode freq u p :=
  mul_pos (normalizedPlanarMode_positive _) (verticalMode_positive hfreq _)

theorem localizedMode_square_integrable {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : Integrable (fun p => localizedMode freq u p ^ 2) := by
  simp_rw [localizedMode, mul_pow]
  exact (normalizedPlanarMode_square_integrable.comp_sub_right u).mul_prod
    (verticalMode_square_integrable hfreq)

theorem localizedMode_normalized {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : (∫ p, localizedMode freq u p ^ 2) = 1 := by
  simp_rw [localizedMode, mul_pow]
  rw [Measure.volume_eq_prod,
    integral_prod_mul (fun r => normalizedPlanarMode (r - u) ^ 2)
      (fun z => verticalMode freq z ^ 2),
    integral_sub_right_eq_self (fun r => normalizedPlanarMode r ^ 2) u,
    normalizedPlanarMode_normalized, verticalMode_normalized hfreq, one_mul]

theorem localizedMode_memLp {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    MemLp (localizedMode freq u) 2 :=
  (memLp_two_iff_integrable_sq (localizedMode_C7 freq u).continuous.aestronglyMeasurable).mpr
    (localizedMode_square_integrable hfreq u)

theorem localizedMode_planar_laplacian (freq : ℝ) (u : PlanarPosition) (p : SplitPosition) :
    planarLaplacian (fun r => localizedMode freq u (r, p.2)) p.1 =
      (2 * manufacturedPlanarWell (p.1 - u) + 1) * localizedMode freq u p := by
  have hc : ContDiff ℝ 2 (fun r => normalizedPlanarMode (r - u)) :=
    (normalizedPlanarMode_C7.comp (contDiff_id.sub contDiff_const)).of_le (by norm_num)
  change planarLaplacian (fun r => normalizedPlanarMode (r - u) * verticalMode freq p.2) p.1 = _
  rw [show (fun r => normalizedPlanarMode (r - u) * verticalMode freq p.2) =
    (fun r => verticalMode freq p.2 * normalizedPlanarMode (r - u))
    from funext (fun r => mul_comm _ _), planarLaplacian_const_mul hc,
    planarLaplacian_translate, normalizedPlanarMode_eigen_equation]
  simp only [localizedMode]
  ring

theorem localizedMode_vertical_second (freq : ℝ) (u : PlanarPosition) (p : SplitPosition) :
    deriv (deriv (fun z => localizedMode freq u (p.1, z))) p.2 =
      (freq ^ 2 * p.2 ^ 2 - freq) * localizedMode freq u p := by
  simp only [localizedMode, deriv_const_mul_field', deriv_const_mul_field,
    verticalMode_second_deriv]
  ring

theorem localizedMode_eigen_equation (freq : ℝ) (u : PlanarPosition) (p : SplitPosition) :
    -(1 / 2 : ℝ) * splitLaplacian (localizedMode freq u) p +
      localizedPotential freq u p * localizedMode freq u p =
        ((-1 / 2 : ℝ) + freq / 2) * localizedMode freq u p := by
  simp only [splitLaplacian, localizedMode_planar_laplacian,
    localizedMode_vertical_second, localizedPotential]
  ring

end ContinuumCoulomb

end

end OAI
