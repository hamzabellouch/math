import Mathlib
import OAI.Geometry.IntegralFillings.Slicing.NormalRestriction
import OAI.Geometry.IntegralFillings.Optimality.BallCurrent

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.Optimality
open SmoothCutoff

noncomputable def radiusFunction (d : ℕ) (x : UnitBall d) : ℝ := -‖x.val‖

lemma radiusFunction_lipschitz (d : ℕ) : LipschitzWith 1 (radiusFunction d) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [radiusFunction, NNReal.coe_one, one_mul, dist_neg_neg, Real.dist_eq,
    Subtype.dist_eq]
  rw [dist_eq_norm]
  exact abs_norm_sub_norm_le x.val y.val

lemma radiusFunction_boundedLip (d : ℕ) : BoundedLip (radiusFunction d) := by
  refine ⟨⟨1, radiusFunction_lipschitz d⟩, 1, ?_⟩
  intro x
  simpa only [radiusFunction, abs_neg, abs_of_nonneg (norm_nonneg _),
    Metric.mem_closedBall, dist_zero_right] using x.property

noncomputable def radialProfile {d : ℕ} (a : ℝ≥0) (t : ℝ) (z : Euc d) : ℝ :=
  profile a t (-‖z‖)

lemma radialProfile_contDiff {d : ℕ} {a : ℝ≥0} {t : ℝ}
    (ha : 1 < (a:ℝ) * (-t)) : ContDiff ℝ 1 (radialProfile (d := d) a t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have hc : Continuous (fun z : Euc d => (a:ℝ) * (-‖z‖ - t)) := by fun_prop
    have he : radialProfile (d := d) a t =ᶠ[𝓝 0] fun _ => 1 := by
      have ha' : 1 < (a:ℝ) * (-‖(0 : Euc d)‖ - t) := by simpa using ha
      filter_upwards [hc.continuousAt.eventually (eventually_gt_nhds ha')] with z hz
      exact Real.smoothTransition.one_of_one_le hz.le
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact Real.smoothTransition.contDiff.contDiffAt.comp x
      (contDiffAt_const.mul ((contDiffAt_id.norm ℝ hx).neg.sub contDiffAt_const))

lemma radialProfile_compact {d : ℕ} (a : ℝ≥0) (t : ℝ) :
    HasCompactSupport (radialProfile (d := d) a t) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (-t))
  intro x hx
  apply profile_zero
  have hh : -t < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  linarith

lemma radialProfile_zero_outside {d : ℕ} (a : ℝ≥0) {t : ℝ} (ht : -1 < t)
    {x : Euc d} (hx : x ∉ Metric.ball 0 1) : radialProfile a t x = 0 := by
  apply profile_zero
  have hh : 1 ≤ ‖x‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hx
  linarith

lemma radialProfile_fderiv_zero_outside {d : ℕ} (a : ℝ≥0) {t : ℝ} (ht : -1 < t)
    {x : Euc d} (hx : x ∉ Metric.ball 0 1) : fderiv ℝ (radialProfile a t) x = 0 := by
  have hh : 1 ≤ ‖x‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hx
  have he : radialProfile a t =ᶠ[𝓝 x] fun _ => 0 := by
    have hc : Continuous (fun y : Euc d => -‖y‖) := continuous_norm.neg
    have hx' : -‖x‖ < t := by linarith
    filter_upwards [hc.continuousAt.eventually_lt_const hx'] with y hy
    exact profile_zero a hy.le
  simpa using he.fderiv_eq (𝕜 := ℝ)

lemma ballChart_param_lipschitz (d : ℕ) : LipschitzWith 1 (ballChart d).param := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  rfl

lemma ballChart_scalar_extension {d : ℕ} {f : UnitBall d → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∃ F : Euc d → ℝ, LipschitzWith K F ∧ EqOn ((ballChart d).scalar f) F (ballChart d).domain := by
  have hs : LipschitzOnWith K ((ballChart d).scalar f) (ballChart d).domain := by
    simpa using (ballChart d).scalar_lipschitzOn (ballChart_param_lipschitz d) hf
  exact hs.extend_real

lemma ballChart_action_extensions {d : ℕ} {b : UnitBall d → ℝ}
    {π : Fin d → UnitBall d → ℝ} {B : Euc d → ℝ} {P : Fin d → Euc d → ℝ}
    {K : Fin d → ℝ≥0} (hab : Admissible b π) (hP : ∀ i, LipschitzWith (K i) (P i))
    (hb : EqOn ((ballChart d).scalar b) B (ballChart d).domain)
    (hπ : ∀ i, EqOn ((ballChart d).scalar (π i)) (P i) (ballChart d).domain) :
    (ballChart d).action b π = ∫ z in Metric.ball 0 1,
      B z * coordinateJacobian P (fun j => EuclideanSpace.single j 1) z := by
  rw [IntegerChart.action, ite_eq_left hab]
  apply integral_congr_ae
  filter_upwards [(ballChart d).ae_jacobian_eq_extensions hP hπ,
    ae_restrict_mem (ballChart d).borel] with z hj hz
  change (1:ℤ) * ((ballChart d).scalar b z) * _ = _
  rw [Int.cast_one, one_mul, hb hz, hj]
  congr 1
  rw [coordinateJacobian, ← Matrix.det_transpose]
  rfl

lemma radialProfile_lipschitz {d : ℕ} (a : ℝ≥0) (t : ℝ) :
    ∃ K : ℝ≥0, LipschitzWith K (radialProfile (d := d) a t) := by
  obtain ⟨C, hC⟩ := exists_profile_bounds
  have hn : LipschitzWith 1 (fun z : Euc d => -‖z‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, dist_neg_neg, Real.dist_eq]
    rw [dist_eq_norm]
    exact abs_norm_sub_norm_le x y
  exact ⟨C*a*1, (hC a t).1.comp hn⟩

lemma ballChart_local_stokes {k : ℕ} {a : ℝ≥0} {t : ℝ} (ht : -1 < t)
    (ha : 1 < (a:ℝ) * (-t)) {b : UnitBall (k+1) → ℝ}
    {π : Fin k → UnitBall (k+1) → ℝ} (hab : Admissible b π) :
    (ballChart (k+1)).action (profile a t ∘ radiusFunction (k+1)) (Matrix.vecCons b π) =
      -(ballChart (k+1)).action b (Matrix.vecCons (profile a t ∘ radiusFunction (k+1)) π) := by
  let C := ballChart (k+1)
  let f := radialProfile (d := k+1) a t
  obtain ⟨K, hK⟩ := hab.1.1
  obtain ⟨B, hB, hBe⟩ := ballChart_scalar_extension hK
  choose L hL using hab.2
  choose P hP hPe using fun i => ballChart_scalar_extension (hL i)
  obtain ⟨J,hJ⟩ := radialProfile_lipschitz (d := k+1) a t
  have hprof := Slicing.profile_comp_boundedLip (radiusFunction_boundedLip (k+1)) a t
  have hfe : EqOn (C.scalar (profile a t ∘ radiusFunction (k+1))) f C.domain := by
    intro z hz
    rw [C.scalar_eq hz]
    rfl
  have hleft : C.action (profile a t ∘ radiusFunction (k+1)) (Matrix.vecCons b π) =
      ∫ z in Metric.ball 0 1, f z * coordinateJacobian (Fin.cons B P)
        (fun j => EuclideanSpace.single j 1) z := by
    apply ballChart_action_extensions (K := Fin.cons K L)
      (Foundations.admissible_vecCons hprof hab.1.1 hab.2)
    · intro i
      exact Fin.cases hB (fun j => hP j) i
    · exact hfe
    · intro i
      exact Fin.cases hBe (fun j => hPe j) i
  have hright : C.action b (Matrix.vecCons (profile a t ∘ radiusFunction (k+1)) π) =
      ∫ z in Metric.ball 0 1, B z * coordinateJacobian (Fin.cons f P)
        (fun j => EuclideanSpace.single j 1) z := by
    apply ballChart_action_extensions (K := Fin.cons J L)
      (Foundations.admissible_vecCons hab.1 hprof.1 hab.2)
    · intro i
      exact Fin.cases hJ (fun j => hP j) i
    · exact hBe
    · intro i
      exact Fin.cases hfe (fun j => hPe j) i
  rw [hleft, hright]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)]
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)]
    · have hPu : ∀ i, LipschitzWith (∑ j, L j) (P i) := fun i =>
        (hP i).weaken (Finset.single_le_sum (fun j _ => zero_le) (Finset.mem_univ i))
      exact integral_coordinateJacobian_cons volume (radialProfile_contDiff ha)
        (radialProfile_compact a t) hB hPu (fun j => EuclideanSpace.single j 1)
    · have hdf : fderiv ℝ f z = 0 := radialProfile_fderiv_zero_outside a ht hz
      have hdet : coordinateJacobian (Fin.cons f P) (fun j => EuclideanSpace.single j 1) z = 0 := by
        apply Matrix.det_eq_zero_of_column_eq_zero 0
        intro i
        change fderiv ℝ f z _ = 0
        rw [hdf]
        rfl
      rw [hdet, mul_zero]
  · rw [show f z = 0 from radialProfile_zero_outside a ht hz, zero_mul]

end SharpIntegralFillings.Optimality

end

end OAI
