import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTAdaptiveDisk

namespace OAI

/-! Normalization of Dirichlet L-functions on a moving disk. The radius is
an explicit parameter; all characters, including the principal character,
are allowed when the disk stays away from the real axis. -/

namespace TwoPointCorrelations

open Complex Filter
open scoped BigOperators Classical Topology

variable {q : ℕ} [NeZero q]

noncomputable def mrtMovingPoint (r t : ℝ) (z : ℂ) : ℂ :=
  ((1 + 2 * r : ℝ) : ℂ) + Complex.I * (t : ℂ) + ((3 * r : ℝ) : ℂ) * z

noncomputable def mrtMovingLFunction (χ : DirichletCharacter ℂ q) (r t : ℝ)
    (z : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ (mrtMovingPoint r t z) /
    DirichletCharacter.LFunction χ (mrtMovingPoint r t 0)

lemma mrt_moving_point_ne_one {r t : ℝ} (hr : 0 < r) (ht : 3 * r < |t|)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : mrtMovingPoint r t z ≠ 1 := by
  intro he
  have him := congrArg Complex.im he
  have him' : t + 3 * r * z.im = 0 := by
    simpa [mrtMovingPoint, Complex.mul_im] using him
  have hzi := (Complex.abs_im_le_norm z).trans hz
  have heq : t = -(3 * r * z.im) := by linarith
  rw [heq, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < 3 * r)] at ht
  nlinarith

lemma mrt_moving_point_center_ne_zero (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    DirichletCharacter.LFunction χ (mrtMovingPoint r t 0) ≠ 0 := by
  apply χ.LFunction_ne_zero_of_one_le_re
  · right
    intro h
    have hh := congrArg Complex.re h
    simp [mrtMovingPoint] at hh
    linarith
  · simp [mrtMovingPoint]
    linarith

lemma mrt_moving_LFunction_zero (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr : 0 < r) (t : ℝ) : mrtMovingLFunction χ r t 0 = 1 :=
  div_self (mrt_moving_point_center_ne_zero χ hr t)

lemma mrt_moving_LFunction_analytic (χ : DirichletCharacter ℂ q)
    {r t : ℝ} (hr : 0 < r) (ht : 3 * r < |t|) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ (mrtMovingLFunction χ r t) z := by
  intro z hz
  have hn := mrt_moving_point_ne_one hr ht (by simpa using hz)
  have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
    intro w hw
    exact (χ.differentiableAt_LFunction w (Or.inl hw)).differentiableWithinAt
  have ha := hd.analyticAt (isOpen_compl_singleton.mem_nhds hn)
  have hp : AnalyticAt ℂ (mrtMovingPoint r t) z := by
    apply Differentiable.analyticAt
    unfold mrtMovingPoint
    fun_prop
  exact (ha.comp hp).div_const

lemma mrt_moving_LFunction_growth (χ : DirichletCharacter ℂ q)
    {r t A V B : ℝ}
    (hA : 0 ≤ A)
    (hg : ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
      ‖DirichletCharacter.LFunction χ (mrtMovingPoint r t z)‖ ≤ A)
    (hi : ‖(DirichletCharacter.LFunction χ (mrtMovingPoint r t 0))⁻¹‖ ≤ V)
    (hB : A * V ≤ Real.exp B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
      ‖mrtMovingLFunction χ r t z‖ ≤ Real.exp B := by
  intro z hz
  unfold mrtMovingLFunction
  rw [div_eq_mul_inv, norm_mul]
  exact (mul_le_mul (hg z hz) hi (norm_nonneg _) hA).trans hB

lemma mrt_moving_LFunction_deriv (χ : DirichletCharacter ℂ q)
    {r t : ℝ} (hr : 0 < r) (ht : 3 * r < |t|)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    deriv (mrtMovingLFunction χ r t) z =
      (deriv (DirichletCharacter.LFunction χ) (mrtMovingPoint r t z) *
        ((3 * r : ℝ) : ℂ)) /
        DirichletCharacter.LFunction χ (mrtMovingPoint r t 0) := by
  have hp : HasDerivAt (mrtMovingPoint r t) ((3 * r : ℝ) : ℂ) z := by
    exact (hasDerivAt_const_mul ((3 * r : ℝ) : ℂ)).const_add
      (((1 + 2 * r : ℝ) : ℂ) + Complex.I * (t : ℂ))
  have hn := mrt_moving_point_ne_one hr ht hz
  exact (((χ.differentiableAt_LFunction _ (Or.inl hn)).hasDerivAt.comp z hp).div_const
    (DirichletCharacter.LFunction χ (mrtMovingPoint r t 0))).deriv

lemma mrt_moving_logderiv_eq (χ : DirichletCharacter ℂ q)
    {r t : ℝ} (hr : 0 < r) (ht : 3 * r < |t|)
    {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hn : DirichletCharacter.LFunction χ (mrtMovingPoint r t z) ≠ 0) :
    deriv (mrtMovingLFunction χ r t) z / mrtMovingLFunction χ r t z =
      ((3 * r : ℝ) : ℂ) *
        (deriv (DirichletCharacter.LFunction χ) (mrtMovingPoint r t z) /
          DirichletCharacter.LFunction χ (mrtMovingPoint r t z)) := by
  rw [mrt_moving_LFunction_deriv χ hr ht hz]
  unfold mrtMovingLFunction
  field_simp [hn, mrt_moving_point_center_ne_zero χ hr t]

/-- A separated normalized zero set bounds the actual logarithmic derivative.
The factor `1/(3r)` is the only cost of changing the disk radius. -/
theorem mrt_moving_logderiv_norm (χ : DirichletCharacter ℂ q)
    {r t B η : ℝ} (hr : 0 < r) (ht : 3 * r < |t|) (hB : 0 < B)
    (hg : ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
      ‖mrtMovingLFunction χ r t z‖ ≤ Real.exp B)
    {z : ℂ} (hz : ‖z‖ ≤ 3 / 4)
    (hn : DirichletCharacter.LFunction χ (mrtMovingPoint r t z) ≠ 0)
    (hη : 0 < η)
    (hd : ∀ ρ ∈ mrtDiskZeros (mrtMovingLFunction χ r t), η ≤ ‖z - ρ‖) :
    ‖deriv (DirichletCharacter.LFunction χ) (mrtMovingPoint r t z) /
      DirichletCharacter.LFunction χ (mrtMovingPoint r t z)‖ ≤
      ((mrtCharacterLogDerivativeConstant +
        (1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) / η) * B) / (3 * r) := by
  have hf := mrt_moving_LFunction_analytic χ hr ht
  have h0 := mrt_moving_LFunction_zero χ hr t
  have hfn : mrtMovingLFunction χ r t z ≠ 0 :=
    div_ne_zero hn (mrt_moving_point_center_ne_zero χ hr t)
  have hh := mrt_disk_logderiv_norm _ hf h0 hB hg hz hfn hη hd
  rw [mrt_moving_logderiv_eq χ hr ht (hz.trans (by norm_num)) hn, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 3 * r)] at hh
  exact (le_div_iff₀ (by positivity : 0 < 3 * r)).mpr (by nlinarith only [hh])

end TwoPointCorrelations

end OAI
