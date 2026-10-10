import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarPartition
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarModeH1

namespace OAI

/-! Actual scaled cutoffs for separated planar sites. Their square
partition has a localization cost of order D⁻² independent of site count. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
open PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

def planarSiteAngle (D : ℝ) (u x : PlanarPosition) : ℝ :=
  (Real.pi / 2) * cutoffBump ((6 / D) • (x - u))

theorem planarSiteAngle_C1 (D : ℝ) (u : PlanarPosition) :
    ContDiff ℝ 1 (planarSiteAngle D u) :=
  contDiff_const.mul ((cutoffBump_smooth.of_le (by simp)).comp
    ((contDiff_id.sub contDiff_const).const_smul (6 / D)))

theorem planarSiteAngle_support {D : ℝ} (hD : 0 < D) (u : PlanarPosition) :
    tsupport (planarSiteAngle D u) ⊆ Metric.closedBall u (D / 3) := by
  apply closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  change planarSiteAngle D u x ≠ 0 at hx
  change dist x u ≤ D / 3
  by_contra! hn
  have hb : cutoffBump ((6 / D) • (x - u)) = 0 := by
    apply cutoffBump.zero_of_le_dist
    change 2 ≤ dist ((6 / D) • (x - u)) 0
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hD)]
    rw [div_mul_eq_mul_div, le_div_iff₀ hD]
    rw [dist_eq_norm] at hn
    linarith
  exact hx (by simp only [planarSiteAngle, hb, mul_zero])

theorem planarSiteAngle_disjoint {ι : Type*} {D : ℝ} (hD : 0 < D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (i j : ι) (hij : i ≠ j) :
    Disjoint (tsupport (planarSiteAngle D (u i))) (tsupport (planarSiteAngle D (u j))) := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hi' := planarSiteAngle_support hD (u i) hi
  have hj' := planarSiteAngle_support hD (u j) hj
  simp only [Metric.mem_closedBall, dist_eq_norm] at hi' hj'
  have ht : ‖u i - u j‖ ≤ ‖x - u i‖ + ‖x - u j‖ := by
    simpa only [dist_eq_norm, norm_sub_rev (u i) x] using dist_triangle (u i) x (u j)
  have hs := hsep i j hij
  linarith

theorem planarSiteAngle_inner {D : ℝ} (hD : 0 < D) (u x : PlanarPosition)
    (hx : ‖x-u‖ ≤ D / 8) : planarSiteAngle D u x = Real.pi / 2 := by
  have hb : cutoffBump ((6 / D) • (x - u)) = 1 := by
    apply cutoffBump.one_of_mem_closedBall
    change dist ((6 / D) • (x - u)) 0 ≤ 1
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hD)]
    rw [div_mul_eq_mul_div, div_le_iff₀ hD]
    linarith
  simp only [planarSiteAngle, hb, mul_one]

def planarSitePartition {ι : Type*} [Fintype ι] (D : ℝ) (u : ι → PlanarPosition) :
    Option ι → PlanarPosition → ℝ := planarTrigPartition (fun i => planarSiteAngle D (u i))

theorem planarSitePartition_C1 {ι : Type*} [Fintype ι] (D : ℝ)
    (u : ι → PlanarPosition) (i : Option ι) : ContDiff ℝ 1 (planarSitePartition D u i) :=
  planarTrigPartition_C1 _ (fun i => planarSiteAngle_C1 D (u i)) i

theorem planarSitePartition_square_sum {ι : Type*} [Fintype ι] {D : ℝ} (hD : 0 < D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (x : PlanarPosition) :
    ∑ i, planarSitePartition D u i x ^ 2 = 1 :=
  planarTrigPartition_square_sum _ (planarSiteAngle_disjoint hD u hsep) x

theorem planarSitePartition_site_inner {ι : Type*} [Fintype ι] {D : ℝ} (hD : 0 < D)
    (u : ι → PlanarPosition) (i : ι) (x : PlanarPosition) (hx : ‖x-u i‖ ≤ D / 8) :
    planarSitePartition D u (some i) x = 1 := by
  dsimp only [planarSitePartition, planarTrigPartition]
  rw [planarSiteAngle_inner hD _ _ hx, Real.sin_pi_div_two]

theorem planarSiteAngle_partial (D : ℝ) (u e x : PlanarPosition) :
    planarPartial (planarSiteAngle D u) e x =
      (Real.pi / 2 * (6 / D)) * planarPartial cutoffBump e ((6 / D) • (x-u)) := by
  change fderiv ℝ (fun y => Real.pi / 2 * cutoffBump ((6 / D) • (y-u))) x e =
    (Real.pi / 2 * (6 / D)) * fderiv ℝ cutoffBump ((6 / D) • (x-u)) e
  have hm := ((hasFDerivAt_id (𝕜 := ℝ) x).sub (hasFDerivAt_const u x)).const_smul (6 / D)
  have hb := (cutoffBump_smooth.differentiable (by simp) ((6 / D) • (x-u))).hasFDerivAt.comp x hm
  have ha := hb.const_mul (Real.pi / 2)
  have he := congrArg (fun L : PlanarPosition →L[ℝ] ℝ => L e) ha.fderiv
  simpa only [Pi.sub_def, Pi.mul_def, Pi.smul_def,
    id_eq, Function.comp_def,
    ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul, sub_zero,
    ContinuousLinearMap.id_apply, zero_apply, map_smul, mul_assoc] using he

def planarSiteDerivativeBound (D : ℝ) : ℝ :=
  (Real.pi / 2 * (6 / D)) * cutoffGradBound

theorem planarSiteDerivativeBound_nonnegative {D : ℝ} (hD : 0 < D) :
    0 ≤ planarSiteDerivativeBound D := by
  unfold planarSiteDerivativeBound
  exact mul_nonneg (mul_nonneg (div_nonneg Real.pi_pos.le (by norm_num))
    (div_pos (by norm_num) hD).le) cutoffGradBound_nonnegative

theorem planarSiteAngle_partial_bound {D : ℝ} (hD : 0 < D)
    (u x : PlanarPosition) (a : Fin 2) :
    |planarPartial (planarSiteAngle D u) (planarAxis a) x| ≤ planarSiteDerivativeBound D := by
  have hc : 0 ≤ Real.pi / 2 * (6 / D) :=
    mul_nonneg (div_nonneg Real.pi_pos.le (by norm_num)) (div_pos (by norm_num) hD).le
  rw [planarSiteAngle_partial, abs_mul, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left ?_ hc
  rw [← grad_coordinate]
  exact (PiLp.norm_apply_le (grad cutoffBump ((6 / D) • (x-u))) a).trans (cutoffGradBound_spec _)

theorem planarSitePartition_direction_bound {ι : Type*} [Fintype ι] {D : ℝ} (hD : 0 < D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (a : Fin 2) (x : PlanarPosition) :
    (∑ i, planarPartial (planarSitePartition D u i) (planarAxis a) x ^ 2) ≤
      planarSiteDerivativeBound D ^ 2 :=
  planarTrigPartition_gradient_bound _ (fun i => planarSiteAngle_C1 D (u i))
    (planarSiteAngle_disjoint hD u hsep) (planarSiteDerivativeBound_nonnegative hD)
    (planarAxis a) (fun i x => planarSiteAngle_partial_bound hD (u i) x a) x

theorem planarSitePartition_gradient_bound {ι : Type*} [Fintype ι] {D : ℝ} (hD : 0 < D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (x : PlanarPosition) :
    (∑ a : Fin 2, ∑ i, planarPartial (planarSitePartition D u i) (planarAxis a) x ^ 2) ≤
      2 * planarSiteDerivativeBound D ^ 2 := by
  rw [Fin.sum_univ_two]
  linarith [planarSitePartition_direction_bound hD u hsep 0 x,
    planarSitePartition_direction_bound hD u hsep 1 x]

end ContinuumCoulomb

end

end OAI
