import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Ring.Commute

namespace OAI

/-! # The resolvent contour operator

This is the contour operator on the circle used to split the actual linearized
time step.  Its action on eigenvectors is proved directly.  Idempotence and
finite rank are separate obligations; no spectral splitting is assumed here.
-/

open Complex Set MeasureTheory

namespace DefocusingNLS

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem commute_resolvent_of_commute (U T : E →L[ℂ] E) (hUT : Commute U T) {z : ℂ}
    (hz : z ∈ resolventSet ℂ T) : Commute U (resolvent T z) := by
  rw [spectrum.resolvent_eq hz]
  apply Commute.units_inv_right
  rw [hz.unit_spec]
  exact (Algebra.commute_algebraMap_right z U).sub_right hUT

omit [CompleteSpace E] in
theorem commute_resolvent_operator (T : E →L[ℂ] E) {z : ℂ}
    (hz : z ∈ resolventSet ℂ T) : Commute T (resolvent T z) :=
  commute_resolvent_of_commute T T (Commute.refl T) hz

omit [CompleteSpace E] in
theorem resolvent_first_identity (T : E →L[ℂ] E) {z w : ℂ}
    (hz : z ∈ resolventSet ℂ T) (hw : w ∈ resolventSet ℂ T) (hwz : w ≠ z) :
    resolvent T z * resolvent T w = (w - z)⁻¹ • (resolvent T z - resolvent T w) := by
  let Az := algebraMap ℂ (E →L[ℂ] E) z - T
  let Aw := algebraMap ℂ (E →L[ℂ] E) w - T
  have hzl : resolvent T z * Az = 1 := Ring.inverse_mul_cancel Az hz
  have hwr : Aw * resolvent T w = 1 := Ring.mul_inverse_cancel Aw hw
  have hdiff : Aw - Az = (w - z) • (1 : E →L[ℂ] E) := by
    calc
      Aw - Az = algebraMap ℂ (E →L[ℂ] E) w - algebraMap ℂ (E →L[ℂ] E) z := by
        dsimp only [Aw, Az]
        abel
      _ = _ := by rw [← map_sub, Algebra.algebraMap_eq_smul_one]
  have h : resolvent T z - resolvent T w =
      (w - z) • (resolvent T z * resolvent T w) := by
    calc
      resolvent T z - resolvent T w =
          resolvent T z * (Aw - Az) * resolvent T w := by
        rw [mul_sub, sub_mul, mul_assoc, hwr, mul_one, hzl, one_mul]
      _ = (w - z) • (resolvent T z * resolvent T w) := by
        rw [hdiff, mul_smul_comm, mul_one, smul_mul_assoc]
  rw [h, inv_smul_smul₀ (sub_ne_zero.mpr hwz)]

omit [CompleteSpace E] in
theorem resolvent_apply_eigenvector (T : E →L[ℂ] E) {lam z : ℂ} {x : E}
    (hx : T x = lam • x) (hz : z ∈ resolventSet ℂ T) (hlamz : z ≠ lam) :
    resolvent T z x = (z - lam)⁻¹ • x := by
  let A := algebraMap ℂ (E →L[ℂ] E) z - T
  have hA : IsUnit A := hz
  have hRA : (resolvent T z).comp A = ContinuousLinearMap.id ℂ E :=
    Ring.inverse_mul_cancel A hA
  have hAx : A x = (z - lam) • x := by
    change z • x - T x = (z - lam) • x
    rw [hx, sub_smul]
  have h := congrArg (fun L : E →L[ℂ] E => L x) hRA
  change resolvent T z (A x) = x at h
  rw [hAx, map_smul] at h
  calc
    resolvent T z x = (z - lam)⁻¹ • ((z - lam) • resolvent T z x) := by
      rw [inv_smul_smul₀ (sub_ne_zero.mpr hlamz)]
    _ = (z - lam)⁻¹ • x := by rw [h]

noncomputable def circleResolventOperator (T : E →L[ℂ] E) (r : ℝ) : E →L[ℂ] E :=
  (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(0, r), resolvent T z

theorem circleIntegrable_resolvent (T : E →L[ℂ] E) {r : ℝ} (hr : 0 ≤ r)
    (hres : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T) :
    CircleIntegrable (resolvent T) 0 r := by
  apply ContinuousOn.circleIntegrable hr
  intro z hz
  apply ((spectrum.hasDerivAt_resolvent_const_left
    (hres z (by simpa only [Metric.mem_sphere, dist_zero_right] using hz))).continuousAt).continuousWithinAt

theorem circleResolventOperator_apply (T : E →L[ℂ] E) {r : ℝ} (hr : 0 ≤ r)
    (hres : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T) (x : E) :
    circleResolventOperator T r x =
      (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(0, r), resolvent T z x := by
  have hint := (circleIntegrable_resolvent T hr hres).out
  unfold circleResolventOperator
  rw [smul_apply, circleIntegral,
    ContinuousLinearMap.intervalIntegral_apply hint]
  rfl

theorem circleIntegral_map_clm {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] (L : A →L[ℂ] F)
    {f : ℂ → A} {c : ℂ} {r : ℝ} (hf : CircleIntegrable f c r) :
    (∮ z in C(c, r), L (f z)) = L (∮ z in C(c, r), f z) := by
  unfold circleIntegral
  simpa only [map_smul] using L.intervalIntegral_comp_comm hf.out

theorem circleResolventOperator_commute_of_commute (U T : E →L[ℂ] E)
    (hUT : Commute U T) {r : ℝ} (hr : 0 ≤ r)
    (hres : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T) :
    Commute U (circleResolventOperator T r) := by
  let A := E →L[ℂ] E
  have hint := circleIntegrable_resolvent T hr hres
  have hl := circleIntegral_map_clm (ContinuousLinearMap.mul ℂ A U) hint
  have hh := circleIntegral_map_clm ((ContinuousLinearMap.mul ℂ A).flip U) hint
  change (∮ z in C(0, r), U * resolvent T z) = U * (∮ z in C(0, r), resolvent T z) at hl
  change (∮ z in C(0, r), resolvent T z * U) = (∮ z in C(0, r), resolvent T z) * U at hh
  have he : (∮ z in C(0, r), U * resolvent T z) =
      ∮ z in C(0, r), resolvent T z * U := by
    apply circleIntegral.integral_congr hr
    intro z hz
    exact (commute_resolvent_of_commute U T hUT
      (hres z (by simpa only [Metric.mem_sphere, dist_zero_right] using hz))).eq
  rw [hl, hh] at he
  change U * ((2 * Real.pi * I : ℂ)⁻¹ • (∮ z in C(0, r), resolvent T z)) =
    ((2 * Real.pi * I : ℂ)⁻¹ • (∮ z in C(0, r), resolvent T z)) * U
  rw [mul_smul_comm, smul_mul_assoc, he]

theorem circleResolventOperator_commute (T : E →L[ℂ] E) {r : ℝ} (hr : 0 ≤ r)
    (hres : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T) :
    Commute T (circleResolventOperator T r) :=
  circleResolventOperator_commute_of_commute T T (Commute.refl T) hr hres

theorem circleResolventOperator_eq_of_annulus (T : E →L[ℂ] E)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hres : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R → z ∈ resolventSet ℂ T) :
    circleResolventOperator T R = circleResolventOperator T r := by
  have hc : ContinuousOn (resolvent T)
      (Metric.closedBall (0 : ℂ) R \ Metric.ball 0 r) := by
    intro z hz
    apply ((spectrum.hasDerivAt_resolvent_const_left (hres z ?_ ?_)).continuousAt).continuousWithinAt
    · simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hz.2
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
  have hd : ∀ z ∈ (Metric.ball (0 : ℂ) R \ Metric.closedBall 0 r) \ (∅ : Set ℂ),
      DifferentiableAt ℂ (resolvent T) z := by
    intro z hz
    apply (spectrum.hasDerivAt_resolvent_const_left (hres z ?_ ?_)).differentiableAt
    · exact le_of_lt (by
        simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz.1.2)
    · exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hz.1.1)
  unfold circleResolventOperator
  rw [Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR Set.countable_empty hc hd]

theorem circleResolventOperator_eigenvector_inside (T : E →L[ℂ] E)
    {r : ℝ} (hr : 0 < r)
    (hres : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T)
    {lam : ℂ} {x : E} (hx : T x = lam • x) (hlam : ‖lam‖ < r) :
    circleResolventOperator T r x = x := by
  rw [circleResolventOperator_apply T hr.le hres]
  have heq : (∮ z in C(0, r), resolvent T z x) =
      ∮ z in C(0, r), (z - lam)⁻¹ • x := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hz' : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    apply resolvent_apply_eigenvector T hx (hres z hz')
    intro he
    have := congrArg norm he
    linarith
  rw [heq, circleIntegral.integral_smul_const,
    circleIntegral.integral_sub_inv_of_mem_ball
      (by simpa only [Metric.mem_ball, dist_zero_right] using hlam),
    inv_smul_smul₀ (by simp [Real.pi_ne_zero, I_ne_zero])]

theorem circleResolventOperator_eigenvector_outside (T : E →L[ℂ] E)
    {r : ℝ} (hr : 0 ≤ r)
    (hres : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T)
    {lam : ℂ} {x : E} (hx : T x = lam • x) (hlam : r < ‖lam‖) :
    circleResolventOperator T r x = 0 := by
  rw [circleResolventOperator_apply T hr hres]
  have hn (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) r) : z - lam ≠ 0 := by
    intro he
    have hz' : ‖z‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    rw [sub_eq_zero.mp he] at hz'
    exact (not_le_of_gt hlam) hz'
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => (z - lam)⁻¹ • x)
      (Metric.closedBall (0 : ℂ) r) := by
    intro z hz
    exact (((differentiableAt_id.sub_const lam).inv (hn z hz)).smul
      (differentiableAt_const x)).differentiableWithinAt
  have heq : (∮ z in C(0, r), resolvent T z x) =
      ∮ z in C(0, r), (z - lam)⁻¹ • x := by
    apply circleIntegral.integral_congr hr
    intro z hz
    have hz' : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    exact resolvent_apply_eigenvector T hx (hres z hz')
      (sub_ne_zero.mp (hn z (Metric.sphere_subset_closedBall hz)))
  rw [heq, (hdiff.diffContOnCl_ball (Subset.refl _)).circleIntegral_eq_zero hr, smul_zero]

end

end DefocusingNLS

end OAI
