import OAI.Geometry.EinsteinFour.ActualJacobiODEExistence
import OAI.Geometry.EinsteinFour.JacobiODEPositivity
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.Prod

namespace OAI

/-! The matrix Jacobi equation and its compact-interval regularity bounds.
The coefficient is allowed to vary with time and need not commute with its
values at other times. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix Set
open scoped Topology NNReal Matrix.Norms.L2Operator

noncomputable section

abbrev JacobiState := NormalMatrix × NormalMatrix

def jacobiStateOperator (R : NormalMatrix) : JacobiState →L[ℝ] JacobiState :=
  (ContinuousLinearMap.snd ℝ NormalMatrix NormalMatrix).prod
    (-((ContinuousLinearMap.mul ℝ NormalMatrix R).comp
      (ContinuousLinearMap.fst ℝ NormalMatrix NormalMatrix)))

theorem jacobiStateOperator_apply (R : NormalMatrix) (p : JacobiState) :
    jacobiStateOperator R p = (p.2, -(R * p.1)) := rfl

theorem continuous_jacobiStateOperator : Continuous jacobiStateOperator := by
  have h : Continuous (fun R : NormalMatrix =>
      -((ContinuousLinearMap.mul ℝ NormalMatrix R).comp
        (ContinuousLinearMap.fst ℝ NormalMatrix NormalMatrix))) := by fun_prop
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp
    (continuous_const.prodMk h)

theorem norm_jacobiStateOperator_le (R : NormalMatrix) :
    ‖jacobiStateOperator R‖ ≤ 1 + ‖R‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  rw [jacobiStateOperator_apply, Prod.norm_def, Prod.norm_def, norm_neg]
  apply max_le
  · calc
      ‖p.2‖ ≤ max ‖p.1‖ ‖p.2‖ := le_max_right _ _
      _ ≤ (1 + ‖R‖) * max ‖p.1‖ ‖p.2‖ := by
        nlinarith [norm_nonneg R, le_max_left ‖p.1‖ ‖p.2‖, norm_nonneg p.1]
  · calc
      ‖R * p.1‖ ≤ ‖R‖ * ‖p.1‖ := norm_mul_le _ _
      _ ≤ ‖R‖ * max ‖p.1‖ ‖p.2‖ :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
      _ ≤ (1 + ‖R‖) * max ‖p.1‖ ‖p.2‖ := by
        nlinarith [le_max_left ‖p.1‖ ‖p.2‖, norm_nonneg p.1]

structure MatrixJacobiSolution (R : ℝ → NormalMatrix) where
  J : ℝ → NormalMatrix
  V : ℝ → NormalMatrix
  initial_position : J 0 = 0
  initial_velocity : V 0 = 1
  position_derivative : ∀ s, HasDerivAt J (V s) s
  velocity_derivative : ∀ s, HasDerivAt V (-(R s * J s)) s

theorem exists_matrixJacobiSolution (R : ℝ → NormalMatrix) (hR : Continuous R)
    (K : ℝ≥0) (hK : ∀ s, ‖R s‖ ≤ K) :
    Nonempty (MatrixJacobiSolution R) := by
  have hA : Continuous (fun s => jacobiStateOperator (R s)) :=
    continuous_jacobiStateOperator.comp hR
  have hB (s : ℝ) : ‖jacobiStateOperator (R s)‖ ≤ ((1 + K : ℝ≥0) : ℝ) := by
    apply (norm_jacobiStateOperator_le _).trans
    simpa only [NNReal.coe_add, NNReal.coe_one, add_comm] using add_le_add_left (hK s) 1
  obtain ⟨Γ, hΓ0, hΓ⟩ := exists_global_linear_solution _ hA (1 + K) hB
    ((0 : NormalMatrix), (1 : NormalMatrix))
  refine ⟨{
    J := fun s => (Γ s).1
    V := fun s => (Γ s).2
    initial_position := congrArg Prod.fst hΓ0
    initial_velocity := congrArg Prod.snd hΓ0
    position_derivative := fun s => (hΓ s).fst
    velocity_derivative := fun s => (hΓ s).snd }⟩

namespace MatrixJacobiSolution

variable {R : ℝ → NormalMatrix} (d : MatrixJacobiSolution R)

theorem continuous_J : Continuous d.J :=
  continuous_iff_continuousAt.mpr (fun s => (d.position_derivative s).continuousAt)

theorem continuous_V : Continuous d.V :=
  continuous_iff_continuousAt.mpr (fun s => (d.velocity_derivative s).continuousAt)

/-- Every compact interval has the bounds needed by the discrete Jacobi
comparison. No uniformity in the interval is assumed. -/
theorem exists_regular (R' : ℝ → NormalMatrix) (hR : Continuous R)
    (hR' : Continuous R') (hdR : ∀ s, HasDerivAt R (R' s) s)
    (hsym : ∀ s, (R s)ᵀ = R s) (t : ℝ) :
    ∃ q : RegularJacobi t, q.R = R ∧ q.J = d.J ∧ q.V = d.V := by
  let A : ℝ → NormalMatrix := fun s => -(R s * d.J s)
  let A' : ℝ → NormalMatrix := fun s => -(R' s * d.J s + R s * d.V s)
  have hA : Continuous A := (hR.mul d.continuous_J).neg
  have hA' : Continuous A' :=
    ((hR'.mul d.continuous_J).add (hR.mul d.continuous_V)).neg
  have hdA (s : ℝ) : HasDerivAt A (A' s) s :=
    ((hdR s).mul (d.position_derivative s)).neg
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hR.continuousOn
  obtain ⟨F, hF⟩ := isCompact_Icc.exists_bound_of_continuousOn hA.continuousOn
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hA'.continuousOn
  let K₀ := max 0 K
  let F₀ := max 0 F
  let L₀ := max 0 L
  have hbA (s : ℝ) (hs : s ∈ Icc 0 t) : ‖A s‖ ≤ F₀ :=
    (hF s hs).trans (le_max_right _ _)
  have hbA' (s : ℝ) (hs : s ∈ Icc 0 t) : ‖A' s‖ ≤ L₀ :=
    (hL s hs).trans (le_max_right _ _)
  refine ⟨{
    R := R
    J := d.J
    V := d.V
    K := K₀
    Lx := F₀
    Lv := L₀
    F := F₀
    K_nonneg := le_max_left _ _
    Lx_nonneg := le_max_left _ _
    Lv_nonneg := le_max_left _ _
    F_nonneg := le_max_left _ _
    initial_position := d.initial_position
    initial_velocity := d.initial_velocity
    symmetric := hsym
    curvature_bound := fun s hs => (hK s hs).trans (le_max_right _ _)
    position_derivative := fun s _ => d.position_derivative s
    velocity_derivative := fun s _ => d.velocity_derivative s
    velocity_lipschitz := ?_
    acceleration_lipschitz := ?_
    force_bound := ?_ }, rfl, rfl, rfl⟩
  · intro s hs r hr
    simpa only [Real.norm_eq_abs] using
      (convex_Icc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun u _ => (d.velocity_derivative u).hasDerivWithinAt) hbA hr hs
  · intro s hs r hr
    simpa only [A, Real.norm_eq_abs] using
      (convex_Icc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun u _ => (hdA u).hasDerivWithinAt) hbA' hr hs
  · intro s hs
    simpa only [A, norm_neg] using hbA s hs

end MatrixJacobiSolution

end
end PositiveEinsteinFour.Jacobi

end OAI
