import OAI.MathematicalPhysics.Boltzmann.Collision.TransverseAverage
import OAI.MathematicalPhysics.Boltzmann.Collision.TransverseAverage

namespace OAI

/-!
# The graph chart for a collision plane

The chart records actual three-dimensional velocities. Its displacement
satisfies the collision-plane equation, and the three-dimensional ball
restriction is precisely the transverse-plus-axial restriction used in
the geometric slice estimate. Identifying its measure with the Carleman
plane measure remains a separate change-of-variables theorem.
-/

noncomputable section

open scoped RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.TransverseLine
open BoltzmannNonuniqueness.TransverseAverage

namespace BoltzmannNonuniqueness.PlaneChart

def join (u : Transverse) (z : ℝ) : Velocity := split.symm (z, u)

theorem transverse_join (u : Transverse) (z : ℝ) : transverse (join u z) = u := by
  have h := congrArg Prod.snd (split.apply_symm_apply (z, u))
  simpa only [join, split_apply] using h

theorem axial_join (u : Transverse) (z : ℝ) : axial (join u z) = z := by
  have h := congrArg Prod.fst (split.apply_symm_apply (z, u))
  simpa only [join, split_apply] using h

theorem join_transverse_axial (v : Velocity) : join (transverse v) (axial v) = v := by
  apply split.injective
  simp only [join, split.apply_symm_apply, split_apply]

theorem norm_join_sq (u : Transverse) (z : ℝ) : ‖join u z‖ ^ 2 = ‖u‖ ^ 2 + z ^ 2 := by
  rw [norm_sq_split, transverse_join, axial_join]

theorem transverse_sub (v w : Velocity) : transverse (v - w) = transverse v - transverse w := by
  apply (WithLp.ext_iff 2).mpr
  funext i
  rfl

theorem axial_sub (v w : Velocity) : axial (v - w) = axial v - axial w := rfl

theorem inner_split (v w : Velocity) :
    inner ℝ v w = inner ℝ (transverse v) (transverse w) + axial v * axial w := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    transverse, axial]
  rw [Fin.sum_univ_castSucc]
  congr 1
  ring

def normal (v p : Velocity) : Transverse := transverse (v - p)

def slope (v p : Velocity) : ℝ := axial (v - p) / ‖normal v p‖

def offset (v p : Velocity) : ℝ := inner ℝ (direction (normal v p)) (transverse v)

def chart (v p : Velocity) (z s : ℝ) : Velocity :=
  join (line (direction (normal v p)) (offset v p - slope v p * z) s) (axial v + z)

theorem transverse_chart (v p : Velocity) (z s : ℝ) :
    transverse (chart v p z s) =
      line (direction (normal v p)) (offset v p - slope v p * z) s :=
  transverse_join _ _

theorem axial_chart (v p : Velocity) (z s : ℝ) : axial (chart v p z s) = axial v + z :=
  axial_join _ _

/-- The graph chart lies on the collision plane whenever the transverse normal is nonzero. -/
theorem chart_on_plane (v p : Velocity) (z s : ℝ) (hn : normal v p ≠ 0) :
    inner ℝ (v - p) (chart v p z s - v) = 0 := by
  have hnn : ‖normal v p‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  have hscale : ‖normal v p‖ • direction (normal v p) = normal v p := by
    rw [direction, smul_smul, mul_inv_cancel₀ hnn, one_smul]
  simp only [inner_split, transverse_sub, axial_sub, transverse_chart, axial_chart]
  change inner ℝ (normal v p)
    (line (direction (normal v p)) (offset v p - slope v p * z) s - transverse v) +
      axial (v - p) * (axial v + z - axial v) = 0
  conv_lhs => lhs; lhs; rw [← hscale]
  rw [real_inner_smul_left, inner_sub_right,
    inner_line _ _ _ (norm_direction hn)]
  change ‖normal v p‖ * ((offset v p - slope v p * z) - offset v p) +
    axial (v - p) * (axial v + z - axial v) = 0
  unfold slope
  field_simp
  ring

/-- Exact norm of the displacement, used for the genuine ball restriction. -/
theorem chart_displacement_norm_sq (v p : Velocity) (z s : ℝ) :
    ‖chart v p z s - v‖ ^ 2 =
      ‖line (direction (normal v p)) (offset v p - slope v p * z) s - transverse v‖ ^ 2 + z ^ 2 := by
  rw [norm_sq_split, transverse_sub, axial_sub, transverse_chart, axial_chart]
  congr 2
  ring

theorem chart_tangent_coordinate (v p : Velocity) (z s : ℝ) (hn : normal v p ≠ 0) :
    inner ℝ (quarterTurn (direction (normal v p))) (transverse (chart v p z s)) = s := by
  rw [transverse_chart, inner_quarterTurn_line _ _ _ (norm_direction hn)]

/-- The chart is one-to-one in its two free coordinates. -/
theorem chart_injective (v p : Velocity) (hn : normal v p ≠ 0) :
    Function.Injective (fun zs : ℝ × ℝ => chart v p zs.1 zs.2) := by
  intro a b hab
  have hz := congrArg axial hab
  simp only [axial_chart] at hz
  have hz' : a.1 = b.1 := by linarith
  have hs := congrArg (fun ξ => inner ℝ (quarterTurn (direction (normal v p))) (transverse ξ)) hab
  simp only [chart_tangent_coordinate v p _ _ hn] at hs
  exact Prod.ext hz' hs

/-- Every velocity on the plane is recovered by its axial and tangent coordinates. -/
theorem chart_recovers (v p ξ : Velocity) (hn : normal v p ≠ 0)
    (hplane : inner ℝ (v - p) (ξ - v) = 0) :
    chart v p (axial ξ - axial v)
      (inner ℝ (quarterTurn (direction (normal v p))) (transverse ξ)) = ξ := by
  have hnn : ‖normal v p‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  have hscale : ‖normal v p‖ • direction (normal v p) = normal v p := by
    rw [direction, smul_smul, mul_inv_cancel₀ hnn, one_smul]
  have he : ‖normal v p‖ *
      (inner ℝ (direction (normal v p)) (transverse ξ) - offset v p) +
      axial (v - p) * (axial ξ - axial v) = 0 := by
    simp only [inner_split, transverse_sub, axial_sub] at hplane
    change inner ℝ (normal v p) (transverse ξ - transverse v) +
      axial (v - p) * (axial ξ - axial v) = 0 at hplane
    rw [← hscale, real_inner_smul_left, inner_sub_right] at hplane
    exact hplane
  have hD : offset v p - slope v p * (axial ξ - axial v) =
      inner ℝ (direction (normal v p)) (transverse ξ) := by
    unfold slope
    field_simp
    nlinarith only [he]
  unfold chart
  rw [hD, line_reconstruct _ _ (norm_direction hn), add_sub_cancel]
  exact join_transverse_axial ξ

end BoltzmannNonuniqueness.PlaneChart

end

end OAI
