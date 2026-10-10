import OAI.Analysis.BernoulliCone.SobolevCalculus

namespace OAI

universe uE uι

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

noncomputable section
open Set Filter Finset
open scoped Topology
namespace Bernoulli.DeSilvaJerison

/-- Half the logarithmic ratio; it is artanh on (-1,1). -/
def A (t : ℝ) : ℝ := (Real.log (1+t) - Real.log (1-t))/2

/-- The even solution of (1-t²)f''-6tf'+6f=0 with f(0)=1. -/
def f (t : ℝ) : ℝ :=
  (8-25*t^2+15*t^4)/(8*(1-t^2)^2) - (15/8)*t*A t

/-- A convenient rational-logarithmic expression for f'. -/
def fp (t : ℝ) : ℝ :=
  -t/(1-t^2)^3 - (5/4)*t/(1-t^2)^2 - (15/8)*t/(1-t^2) - (15/8)*A t

lemma A_neg (t : ℝ) : A (-t) = -A t := by
  simp only [A, sub_eq_add_neg, neg_neg]
  ring

@[simp] lemma A_zero : A 0 = 0 := by simp [A]
@[simp] lemma f_zero : f 0 = 1 := by norm_num [f]
@[simp] lemma fp_zero : fp 0 = 0 := by simp [fp]

lemma f_neg (t : ℝ) : f (-t) = f t := by
  simp only [f, neg_sq, A_neg]
  ring

lemma A_eq_half_log {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    A t = 1/2 * Real.log ((1+t)/(1-t)) := by
  rw [Real.log_div (by linarith [ht.1] : 1+t≠0) (by linarith [ht.2] : 1-t≠0)]
  unfold A
  ring

lemma hasDerivAt_A {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt A (1/(1-t^2)) t := by
  have hp : 1+t≠0 := by linarith [ht.1]
  have hm : 1-t≠0 := by linarith [ht.2]
  have hd : 1-t^2≠0 := by nlinarith [ht.1,ht.2]
  apply (((((hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)).log hp).sub
    (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).log hm)).div_const 2).congr_deriv
  norm_num
  field_simp [hd,hp,hm]
  ring

lemma hasDerivAt_f {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : HasDerivAt f (fp t) t := by
  have hd : 1-t^2≠0 := by nlinarith [ht.1,ht.2]
  have hden : 8*(1-t^2)^2≠0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hd)
  have hnum := ((hasDerivAt_const t (8:ℝ)).sub
    (((hasDerivAt_id t).pow 2).const_mul 25)).add
      (((hasDerivAt_id t).pow 4).const_mul 15)
  have hden' := (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)).pow 2).const_mul 8
  apply ((hnum.div hden' hden).sub
    (((hasDerivAt_id t).const_mul (15/8)).mul (hasDerivAt_A ht))).congr_deriv
  norm_num [fp]
  field_simp [hd]
  ring

lemma hasDerivAt_fp {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt fp (-6/(1-t^2)^4) t := by
  have hd : 1-t^2≠0 := by nlinarith [ht.1,ht.2]
  have hD := (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)
  apply (((((hasDerivAt_id t).neg.div (hD.pow 3) (pow_ne_zero _ hd)).sub
    (((hasDerivAt_id t).const_mul (5/4)).div (hD.pow 2) (pow_ne_zero _ hd))).sub
    (((hasDerivAt_id t).const_mul (15/8)).div hD hd)).sub
    ((hasDerivAt_A ht).const_mul (15/8))).congr_deriv
  norm_num
  field_simp [hd]
  ring

lemma f_relation {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    t * fp t - f t = -1/(1-t^2)^3 := by
  have hd : 1-t^2≠0 := by nlinarith [ht.1,ht.2]
  unfold fp f
  field_simp
  ring

/-- The profile satisfies the differential equation `(1-t²)f''-6tf'+6f=0`. -/
theorem profile_equation {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    (1-t^2) * deriv (deriv f) t - 6*t*deriv f t + 6*f t = 0 := by
  have he : deriv f =ᶠ[𝓝 t] fp := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    exact (hasDerivAt_f hx).deriv
  rw [he.deriv_eq, (hasDerivAt_fp ht).deriv, (hasDerivAt_f ht).deriv]
  have hr := f_relation ht
  have hd : 1-t^2≠0 := by nlinarith [ht.1,ht.2]
  field_simp at hr ⊢
  nlinarith [hr]

lemma A_nonneg {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) : 0 ≤ A t := by
  rw [A_eq_half_log ⟨by linarith,ht1⟩]
  exact mul_nonneg (by norm_num) (Real.log_nonneg ((one_le_div (by linarith)).mpr (by linarith)))

lemma fp_neg {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : fp t < 0 := by
  have hD : 0<1-t^2 := by nlinarith
  have hA := A_nonneg ht.le ht1
  have h1 : 0 < t/(1-t^2)^3 := div_pos ht (pow_pos hD _)
  have h2 : 0 ≤ (5/4:ℝ)*t/(1-t^2)^2 := by positivity
  have h3 : 0 ≤ (15/8:ℝ)*t/(1-t^2) := by positivity
  unfold fp
  rw [neg_div]
  nlinarith

lemma f_strictAnti : StrictAntiOn f (Ico (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ico 0 1)
  · intro t ht
    exact (hasDerivAt_f ⟨by linarith [ht.1],ht.2⟩).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ico] at ht
    rw [(hasDerivAt_f ⟨by linarith [ht.1],ht.2⟩).deriv]
    exact fp_neg ht.1 ht.2

/-- A certified enclosure, replacing the decimal root in the preprint. -/
lemma f_lower_pos : 0 < f (517330/1000000) := by
  have hA : A (517330/1000000) ≤ 5726875/10000000 := by
    rw [A_eq_half_log (by norm_num)]
    refine (Real.log_div_le_sum_range_add (by norm_num) (by norm_num) 12).trans ?_
    norm_num [Finset.sum_range_succ]
  unfold f
  norm_num at hA ⊢
  linarith

lemma f_upper_neg : f (517331/1000000) < 0 := by
  have hA : 572688/1000000 ≤ A (517331/1000000) := by
    rw [A_eq_half_log (by norm_num)]
    refine le_trans ?_ (Real.sum_range_le_log_div (by norm_num) (by norm_num) 12)
    norm_num [Finset.sum_range_succ]
  unfold f
  norm_num at hA ⊢
  linarith

lemma exists_profile_root : ∃ t ∈ Icc (517330/1000000 : ℝ) (517331/1000000), f t = 0 := by
  have hc : ContinuousOn f (Icc (517330/1000000 : ℝ) (517331/1000000)) := by
    intro t ht
    exact (hasDerivAt_f ⟨by linarith [ht.1],by linarith [ht.2]⟩).continuousAt.continuousWithinAt
  obtain ⟨t,ht,hft⟩ := intermediate_value_Icc' (by norm_num : (517330/1000000 : ℝ) ≤ 517331/1000000)
    hc ⟨f_upper_neg.le, f_lower_pos.le⟩
  exact ⟨t,ht,hft⟩

/-- The first positive root t₇ of the normalized profile. -/
def t7 : ℝ := exists_profile_root.choose

lemma t7_bounds : t7 ∈ Icc (517330/1000000 : ℝ) (517331/1000000) :=
  exists_profile_root.choose_spec.1

@[simp] lemma f_t7 : f t7 = 0 := exists_profile_root.choose_spec.2

lemma t7_pos : 0 < t7 := by linarith [t7_bounds.1]
lemma t7_lt_one : t7 < 1 := by linarith [t7_bounds.2]

lemma f_pos_of_abs_lt {t : ℝ} (ht : |t| < t7) : 0 < f t := by
  have h : 0 < f |t| := by
    rw [← f_t7]
    exact f_strictAnti ⟨abs_nonneg t,lt_trans ht t7_lt_one⟩
      ⟨t7_pos.le,t7_lt_one⟩ ht
  by_cases h0 : 0 ≤ t
  · simpa [abs_of_nonneg h0] using h
  · simpa [abs_of_neg (lt_of_not_ge h0), f_neg] using h

lemma root_unique {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (hf : f t = 0) : t = t7 := by
  exact f_strictAnti.injOn ht ⟨t7_pos.le,t7_lt_one⟩ (hf.trans f_t7.symm)

lemma fp_t7 : fp t7 = -1 / (t7 * (1-t7^2)^3) := by
  have h := f_relation ⟨by linarith [t7_pos],t7_lt_one⟩
  rw [f_t7,sub_zero] at h
  calc
    fp t7 = (-1 / (1-t7^2)^3) / t7 :=
      (eq_div_iff (ne_of_gt t7_pos)).mpr (by rw [mul_comm]; exact h)
    _ = _ := by rw [div_div, mul_comm]

/-- The square of the normal derivative of the unscaled conical function. -/
def c7 : ℝ := (1-t7^2) * (fp t7)^2

lemma c7_pos : 0 < c7 := by
  have hD : 0 < 1-t7^2 := by nlinarith [t7_pos,t7_lt_one]
  exact mul_pos hD (sq_pos_of_neg (fp_neg t7_pos t7_lt_one))

lemma c7_eq : c7 = 1 / (t7^2 * (1-t7^2)^5) := by
  have ht : t7≠0 := ne_of_gt t7_pos
  have hd : 1-t7^2≠0 := ne_of_gt (show 0<1-t7^2 by nlinarith [t7_pos,t7_lt_one])
  rw [c7,fp_t7]
  field_simp

lemma contDiffAt_f {n : WithTop ℕ∞} {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ n f t := by
  have hd : 8*(1-t^2)^2≠0 := by
    apply mul_ne_zero (by norm_num)
    exact pow_ne_zero _ (by nlinarith [ht.1,ht.2])
  have hp : 1+t≠0 := by linarith [ht.1]
  have hm : 1-t≠0 := by linarith [ht.2]
  unfold f A
  fun_prop

/-- Extend the positive spherical profile by zero outside its first two roots. -/
def p (t : ℝ) : ℝ := f (min |t| t7)

lemma f_abs (t : ℝ) : f |t| = f t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), f_neg]

lemma p_eq_f {t : ℝ} (ht : |t| ≤ t7) : p t = f t := by
  rw [p, min_eq_left ht, f_abs]

lemma p_eq_zero {t : ℝ} (ht : t7 ≤ |t|) : p t = 0 := by
  rw [p, min_eq_right ht, f_t7]

lemma p_neg (t : ℝ) : p (-t) = p t := by simp only [p, abs_neg]
@[simp] lemma p_zero : p 0 = 1 := by rw [p_eq_f (by simpa using t7_pos.le), f_zero]

lemma p_pos_iff (t : ℝ) : 0 < p t ↔ |t| < t7 := by
  constructor
  · intro ht
    by_contra hn
    rw [p_eq_zero (le_of_not_gt hn)] at ht
    exact lt_irrefl 0 ht
  · intro ht
    rw [p_eq_f ht.le]
    exact f_pos_of_abs_lt ht

lemma p_nonneg (t : ℝ) : 0 ≤ p t := by
  rcases lt_or_ge |t| t7 with ht | ht
  · exact ((p_pos_iff t).mpr ht).le
  · rw [p_eq_zero ht]

lemma p_le_one (t : ℝ) : p t ≤ 1 := by
  rw [p, ← f_zero]
  apply f_strictAnti.antitoneOn ⟨le_rfl,by norm_num⟩
    ⟨le_min (abs_nonneg _) t7_pos.le, (min_le_right _ _).trans_lt t7_lt_one⟩
  exact le_min (abs_nonneg _) t7_pos.le

lemma exists_lipschitz_p : ∃ K : NNReal, LipschitzWith K p := by
  have hc : ContDiffOn ℝ 1 f (Icc 0 t7) := by
    intro t ht
    exact (contDiffAt_f ⟨by linarith [ht.1],ht.2.trans_lt t7_lt_one⟩).contDiffWithinAt
  obtain ⟨K,hK⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 t7) isCompact_Icc
  have hclip : LipschitzWith 1 (fun t : ℝ => min |t| t7) := by
    simpa only [Real.norm_eq_abs] using ((lipschitzWith_one_norm : LipschitzWith 1 (fun t : ℝ => ‖t‖)).min_const t7)
  refine ⟨K, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  have hm (t : ℝ) : min |t| t7 ∈ Icc 0 t7 :=
    ⟨le_min (abs_nonneg _) t7_pos.le, min_le_right _ _⟩
  exact (hK.dist_le_mul _ (hm x) _ (hm y)).trans (by
    have hh := hclip.dist_le_mul x y
    norm_num at hh
    exact mul_le_mul_of_nonneg_left hh K.coe_nonneg)

/-- The normalization imposed by the Bernoulli condition. -/
def κ : ℝ := (Real.sqrt c7)⁻¹

lemma κ_pos : 0 < κ := inv_pos.mpr (Real.sqrt_pos.mpr c7_pos)
lemma κ_sq : κ^2 * c7 = 1 := by
  rw [κ, inv_pow, Real.sq_sqrt c7_pos.le]
  exact inv_mul_cancel₀ (ne_of_gt c7_pos)

end Bernoulli.DeSilvaJerison

/-! The concrete seven-dimensional cone belonging to the De Silva–Jerison profile.
These are actual function/Sobolev constructions, not an assumption of minimality. -/
namespace Bernoulli.DeSilvaJerison

/-- The homogeneous, nonnegative profile, prior to normalizing its boundary slope. -/
def Z (x : Space 7) : ℝ := ‖x‖ * p (x 6 / ‖x‖)

def U (x : Space 7) : ℝ := κ * Z x

@[simp] lemma Z_zero : Z 0 = 0 := by simp [Z]
@[simp] lemma U_zero : U 0 = 0 := by simp [U]
lemma Z_nonneg (x : Space 7) : 0 ≤ Z x := mul_nonneg (norm_nonneg x) (p_nonneg _)
lemma U_nonneg (x : Space 7) : 0 ≤ U x := mul_nonneg κ_pos.le (Z_nonneg x)
lemma Z_le_norm (x : Space 7) : Z x ≤ ‖x‖ := by
  calc Z x ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left (p_le_one _) (norm_nonneg x)
    _ = _ := mul_one _
lemma U_even (x : Space 7) : U (-x) = U x := by
  simp only [U,Z,norm_neg,PiLp.neg_apply,neg_div,p_neg]

lemma coordinate_le_norm (x : Space 7) : |x 6| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (6 : Fin 7)

lemma angular_estimate {x y : Space 7} (hx : x≠0) (hy : y≠0) :
    ‖y‖ * |x 6/‖x‖ - y 6/‖y‖| ≤ 2*‖x-y‖ := by
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  have hs : 0<‖y‖ := norm_pos_iff.mpr hy
  have hq : |x 6/‖x‖| ≤ 1 := by
    rw [abs_div,abs_of_pos hr]
    exact (div_le_one hr).mpr (coordinate_le_norm x)
  have hxy : |x 6-y 6| ≤ ‖x-y‖ := by
    simpa only [PiLp.sub_apply] using coordinate_le_norm (x-y)
  calc
    ‖y‖ * |x 6/‖x‖ - y 6/‖y‖| =
        |(‖y‖-‖x‖)*(x 6/‖x‖) + (x 6-y 6)| := by
      rw [← abs_of_pos hs, ← abs_mul]
      congr 1
      rw [abs_of_pos hs]
      field_simp
      ring
    _ ≤ |‖y‖-‖x‖| * |x 6/‖x‖| + |x 6-y 6| := by
      simpa only [abs_mul] using abs_add_le ((‖y‖-‖x‖)*(x 6/‖x‖)) (x 6-y 6)
    _ ≤ |‖y‖-‖x‖| * 1 + ‖x-y‖ := by gcongr
    _ ≤ ‖x-y‖ + ‖x-y‖ := by
      rw [mul_one]
      gcongr
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x
    _ = _ := by ring

lemma exists_lipschitz_Z : ∃ K : NNReal, LipschitzWith K Z := by
  obtain ⟨K,hK⟩ := exists_lipschitz_p
  refine ⟨1+2*K, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_one, NNReal.coe_ofNat]
  by_cases hx : x=0
  · subst x
    rw [Z_zero,zero_sub,abs_neg,abs_of_nonneg (Z_nonneg y),zero_sub,norm_neg]
    exact (Z_le_norm y).trans (by nlinarith [K.coe_nonneg,norm_nonneg y])
  by_cases hy : y=0
  · subst y
    rw [Z_zero,sub_zero,abs_of_nonneg (Z_nonneg x),sub_zero]
    exact (Z_le_norm x).trans (by nlinarith [K.coe_nonneg,norm_nonneg x])
  have hpd : |p (x 6/‖x‖)-p (y 6/‖y‖)| ≤ K * |x 6/‖x‖- y 6/‖y‖| := by
    simpa only [Real.dist_eq] using hK.dist_le_mul (x 6/‖x‖) (y 6/‖y‖)
  have hpb : |p (x 6/‖x‖)| ≤ 1 := by
    rw [abs_of_nonneg (p_nonneg _)]
    exact p_le_one _
  calc
    |Z x-Z y| = |(‖x‖-‖y‖)*p (x 6/‖x‖) + ‖y‖*(p (x 6/‖x‖)-p (y 6/‖y‖))| := by
      unfold Z
      congr 1
      ring
    _ ≤ |‖x‖-‖y‖| * |p (x 6/‖x‖)| + ‖y‖* |p (x 6/‖x‖)-p (y 6/‖y‖)| := by
      simpa only [abs_mul, abs_of_nonneg (norm_nonneg y)] using
        abs_add_le ((‖x‖-‖y‖)*p (x 6/‖x‖)) (‖y‖*(p (x 6/‖x‖)-p (y 6/‖y‖)))
    _ ≤ |‖x‖-‖y‖| * 1 + ‖y‖*(K* |x 6/‖x‖-y 6/‖y‖|) := by gcongr
    _ = |‖x‖-‖y‖| + K*(‖y‖* |x 6/‖x‖-y 6/‖y‖|) := by ring
    _ ≤ ‖x-y‖ + K*(2*‖x-y‖) := by
      exact add_le_add (abs_norm_sub_norm_le x y)
        (mul_le_mul_of_nonneg_left (angular_estimate hx hy) K.coe_nonneg)
    _ = _ := by ring

lemma exists_lipschitz_U : ∃ K : NNReal, LipschitzWith K U := by
  obtain ⟨K,hK⟩ := exists_lipschitz_Z
  exact ⟨‖κ‖₊*K, (lipschitzWith_smul κ).comp hK⟩

lemma U_continuous : Continuous U := exists_lipschitz_U.choose_spec.continuous

theorem U_h1loc : H1Loc univ U (gradient U) := by
  obtain ⟨K,hK⟩ := exists_lipschitz_U
  intro c r _ _
  exact LipschitzSobolev.h1_ball hK c r

lemma U_smul (r : ℝ) (hr : 0<r) (x : Space 7) : U (r • x) = r * U x := by
  simp only [U,Z,norm_smul,Real.norm_eq_abs,abs_of_pos hr,PiLp.smul_apply,smul_eq_mul,
    mul_div_mul_left _ _ (ne_of_gt hr)]
  ring

theorem U_homogeneous : OneHomogeneous U := by
  intro r hr
  exact Filter.Eventually.of_forall (U_smul r hr)

/-- Values in every direction perpendicular to the symmetry axis are positive. -/
lemma U_of_coordinate_zero {x : Space 7} (hx : x 6=0) : U x = κ*‖x‖ := by
  simp [U,Z,hx]

theorem U_nonzero : Nonzero U := by
  intro h
  have he := congrFun (MeasureTheory.Measure.eq_of_ae_eq h U_continuous continuous_const)
    (EuclideanSpace.single 0 (1:ℝ) : Space 7)
  have hv : U (EuclideanSpace.single 0 (1:ℝ)) = κ := by
    rw [U_of_coordinate_zero (by simp)]
    simp
  rw [hv] at he
  exact (ne_of_gt κ_pos) he

theorem U_not_flat : ¬ Flat U := by
  rintro ⟨e,he,hae⟩
  have hc : Continuous (fun x : Space 7 => max (inner ℝ x e) 0) := by fun_prop
  have heq := MeasureTheory.Measure.eq_of_ae_eq hae U_continuous hc
  have hp := congrFun heq e
  have hn := congrFun heq (-e)
  rw [U_even] at hn
  rw [real_inner_self_eq_norm_sq,he] at hp
  rw [inner_neg_left,real_inner_self_eq_norm_sq,he] at hn
  norm_num at hp hn
  linarith

end Bernoulli.DeSilvaJerison

/-! Euclidean calculus for the actual De Silva–Jerison axisymmetric construction.
No free-boundary or variational conclusion is built into these definitions. -/
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Axisymmetric
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasDerivAt_radius (x v : E) (t : ℝ) (h : x+t • v ≠ 0) :
    HasDerivAt (fun a:ℝ=>‖x+a • v‖)
      (inner ℝ (x+t • v) v / ‖x+t • v‖) t := by
  have hc : HasDerivAt (fun a:ℝ=>x+a • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hn : ‖x+t • v‖ ≠ 0 := norm_ne_zero_iff.mpr h
  have hh := hc.norm_sq.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg _)] at hh
  convert hh using 1; field_simp

lemma hasDerivAt_axis (x v e : E) (t : ℝ) :
    HasDerivAt (fun a:ℝ=>inner ℝ (x+a • v) e) (inner ℝ v e) t := by
  have hc : HasDerivAt (fun a:ℝ=>x+a • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  simpa using hc.inner ℝ (hasDerivAt_const t e)

/-- Lift of a polar profile; values at the origin use the usual total operations. -/
def lift (e : E) (α : ℝ) (φ : ℝ → ℝ) (x : E) : ℝ :=
  ‖x‖ ^ α * φ (inner ℝ x e / ‖x‖)

lemma hasDerivAt_angular (x v e : E) (t : ℝ) (h : x+t • v≠0) :
    HasDerivAt (fun a:ℝ=>inner ℝ (x+a • v) e / ‖x+a • v‖)
      ((inner ℝ v e * ‖x+t • v‖^2 - inner ℝ (x+t • v) e *
        inner ℝ (x+t • v) v) / ‖x+t • v‖^3) t := by
  have hn := norm_ne_zero_iff.mpr h
  apply ((hasDerivAt_axis x v e t).div (hasDerivAt_radius x v t h) hn).congr_deriv
  field_simp

lemma hasDerivAt_lift_line {φ : ℝ → ℝ} {φ' : ℝ} (e x v : E) (α t : ℝ)
    (hx : x+t • v≠0)
    (hφ : HasDerivAt φ φ' (inner ℝ (x+t • v) e / ‖x+t • v‖)) :
    HasDerivAt (fun a:ℝ=>lift e α φ (x+a • v))
      (‖x+t • v‖^α *
        (α * inner ℝ (x+t • v) v / ‖x+t • v‖^2 * φ (inner ℝ (x+t • v) e / ‖x+t • v‖) +
          φ' * ((inner ℝ v e * ‖x+t • v‖^2 - inner ℝ (x+t • v) e *
            inner ℝ (x+t • v) v) / ‖x+t • v‖^3))) t := by
  have hn := norm_ne_zero_iff.mpr hx
  have hr := (hasDerivAt_radius x v t hx).rpow_const (p:=α) (Or.inl hn)
  have hp := hφ.comp t (hasDerivAt_angular x v e t hx)
  apply (hr.mul hp).congr_deriv
  simp only [Function.comp_def]
  rw [Real.rpow_sub_one hn]
  field_simp

/-- The explicit first derivative along a line, used to avoid assuming an ODE
or a second derivative in the Euclidean Laplacian computation. -/
def lineFirst (e x v : E) (α : ℝ) (φ φ₁ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ‖x+t • v‖^α *
    (α * inner ℝ (x+t • v) v / ‖x+t • v‖^2 * φ (inner ℝ (x+t • v) e / ‖x+t • v‖) +
      φ₁ (inner ℝ (x+t • v) e / ‖x+t • v‖) *
        ((inner ℝ v e * ‖x+t • v‖^2 - inner ℝ (x+t • v) e *
          inner ℝ (x+t • v) v) / ‖x+t • v‖^3))

lemma hasDerivAt_lineFirst {φ φ₁ : ℝ → ℝ} {φ₂ : ℝ} (e x v : E) (α t : ℝ)
    (hx : x+t • v≠0)
    (hφ : HasDerivAt φ (φ₁ (inner ℝ (x+t • v) e / ‖x+t • v‖))
      (inner ℝ (x+t • v) e / ‖x+t • v‖))
    (hφ₁ : HasDerivAt φ₁ φ₂ (inner ℝ (x+t • v) e / ‖x+t • v‖)) :
    HasDerivAt (lineFirst e x v α φ φ₁)
      (‖x+t • v‖^α / ‖x+t • v‖^2 *
        (α * φ (inner ℝ (x+t • v) e / ‖x+t • v‖) * ‖v‖^2 +
         α * (α-2) * φ (inner ℝ (x+t • v) e / ‖x+t • v‖) *
           (inner ℝ (x+t • v) v / ‖x+t • v‖)^2 +
         2*(α-1) * φ₁ (inner ℝ (x+t • v) e / ‖x+t • v‖) *
           (inner ℝ (x+t • v) v / ‖x+t • v‖) *
           (inner ℝ v e - inner ℝ (x+t • v) e / ‖x+t • v‖ *
             (inner ℝ (x+t • v) v / ‖x+t • v‖)) -
         inner ℝ (x+t • v) e / ‖x+t • v‖ *
           φ₁ (inner ℝ (x+t • v) e / ‖x+t • v‖) *
           (‖v‖^2-(inner ℝ (x+t • v) v / ‖x+t • v‖)^2) +
         φ₂ * (inner ℝ v e - inner ℝ (x+t • v) e / ‖x+t • v‖ *
           (inner ℝ (x+t • v) v / ‖x+t • v‖))^2)) t := by
  have hn := norm_ne_zero_iff.mpr hx
  have hr := hasDerivAt_radius x v t hx
  have ha := hasDerivAt_axis x v e t
  have hq : HasDerivAt (fun a:ℝ=>inner ℝ (x+a • v) v) (‖v‖^2) t := by
    simpa only [real_inner_self_eq_norm_sq] using hasDerivAt_axis x v v t
  have hs := hasDerivAt_angular x v e t hx
  have hp := hφ.comp t hs
  have hp₁ := hφ₁.comp t hs
  have hQ := ((hq.const_mul α).div (hr.pow 2) (pow_ne_zero _ hn)).mul hp
  have hS := (((hr.pow 2).const_mul (inner ℝ v e)).sub (ha.mul hq)).div
    (hr.pow 3) (pow_ne_zero _ hn)
  apply (((hr.rpow_const (p:=α) (Or.inl hn)).mul
    (hQ.add (hp₁.mul hS)))).congr_deriv
  simp only [Function.comp_def, Pi.pow_apply, Pi.div_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
  rw [Real.rpow_sub_one hn]
  field_simp
  ring

/-- Scalar diagonal Hessian coefficient in a unit radial/angular frame. -/
def secondCoeff (α F F₁ F₂ s p b n : ℝ) : ℝ :=
  α*F*n + α*(α-2)*F*p^2 + 2*(α-1)*F₁*p*(b-s*p) -
    s*F₁*(n-p^2) + F₂*(b-s*p)^2

lemma secondCoeff_sum {ι : Type uι} [Fintype ι]
    (α F F₁ F₂ s : ℝ) (p b : ι → ℝ)
    (hp : ∑ i, (p i)^2 = 1) (hb : ∑ i, (b i)^2 = 1)
    (hpb : ∑ i, p i*b i = s) :
    ∑ i, secondCoeff α F F₁ F₂ s (p i) (b i) 1 =
      α*(α+(Fintype.card ι : ℝ)-2)*F - ((Fintype.card ι : ℝ)-1)*s*F₁ + (1-s^2)*F₂ := by
  have he (i:ι) : secondCoeff α F F₁ F₂ s (p i) (b i) 1 =
      (α*F-s*F₁) + (α*(α-2)*F-(2*α-3)*s*F₁+s^2*F₂)*(p i)^2 +
        (2*(α-1)*F₁-2*s*F₂)*(p i*b i) + F₂*(b i)^2 := by
    unfold secondCoeff
    ring
  simp_rw [he, Finset.sum_add_distrib, ←Finset.mul_sum]
  rw [hp,hb,hpb]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

lemma contDiffAt_lift {φ : ℝ → ℝ} {e x : E} {α : ℝ} {n : WithTop ℕ∞}
    (hx : x ≠ 0) (hf : ContDiffAt ℝ n φ (inner ℝ x e / ‖x‖)) :
    ContDiffAt ℝ n (lift e α φ) x := by
  have hn : ContDiffAt ℝ n (fun y:E=>‖y‖) x := contDiffAt_id.norm ℝ hx
  have ha : ContDiffAt ℝ n (fun y:E=>inner ℝ y e / ‖y‖) x :=
    ((contDiffAt_id.inner ℝ contDiffAt_const).div hn (norm_ne_zero_iff.mpr hx))
  exact (hn.rpow_const_of_ne (norm_ne_zero_iff.mpr hx)).mul (hf.comp x ha)

lemma lift_line_second {φ φ₁ : ℝ → ℝ} {φ₂ : ℝ} (e x v : E) (α : ℝ)
    (hx : x≠0)
    (hφ : ∀ᶠ s in 𝓝 (inner ℝ x e / ‖x‖), HasDerivAt φ (φ₁ s) s)
    (hφ₁ : HasDerivAt φ₁ φ₂ (inner ℝ x e / ‖x‖)) :
    deriv (deriv (fun t:ℝ=>lift e α φ (x+t • v))) 0 =
      ‖x‖^α / ‖x‖^2 * secondCoeff α (φ (inner ℝ x e / ‖x‖))
        (φ₁ (inner ℝ x e / ‖x‖)) φ₂ (inner ℝ x e / ‖x‖)
        (inner ℝ x v / ‖x‖) (inner ℝ v e) (‖v‖^2) := by
  have hx0 : x+(0:ℝ) • v≠0 := by simpa
  have hc : ContinuousAt (fun t:ℝ=>x+t • v) 0 := by fun_prop
  have hnear : ∀ᶠ t:ℝ in 𝓝 0, x+t • v≠0 :=
    hc.eventually_ne hx0
  have hs := (hasDerivAt_angular x v e 0 hx0).continuousAt
  have hp : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt φ (φ₁ (inner ℝ (x+t • v) e / ‖x+t • v‖))
      (inner ℝ (x+t • v) e / ‖x+t • v‖) := by
    exact hs.tendsto.eventually (p:=fun s=>HasDerivAt φ (φ₁ s) s) (by simpa using hφ)
  have he : deriv (fun t:ℝ=>lift e α φ (x+t • v)) =ᶠ[𝓝 0] lineFirst e x v α φ φ₁ := by
    filter_upwards [hnear,hp] with t ht hpt
    exact (hasDerivAt_lift_line e x v α t ht hpt).deriv
  rw [he.deriv_eq]
  have hh := hasDerivAt_lineFirst e x v α 0 hx0 (by simpa using hφ.self_of_nhds)
    (by simpa using hφ₁)
  simpa only [zero_smul, add_zero, secondCoeff] using hh.deriv

lemma line_second_derivative {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v : E) :
    deriv (deriv (fun t:ℝ=>f (x+t • v))) 0=(fderiv ℝ (fderiv ℝ f) x v) v := by
  let c := fun t:ℝ=>x+t • v
  let q := fun t:ℝ=>(fderiv ℝ f (c t)) v
  have hc (t:ℝ) : HasDerivAt c v t := by
    simpa only [one_smul,id_eq,c] using ((hasDerivAt_id t).smul_const v).const_add x
  have hc0 : c 0=x := by simp [c]
  have hnear : ∀ᶠ t in 𝓝 (0:ℝ), ContDiffAt ℝ 2 f (c t) :=
    (hc 0).continuousAt.tendsto.eventually (hc0 ▸ hf.eventually (by norm_num))
  have hq : deriv (fun t:ℝ=>f (x+t • v)) =ᶠ[𝓝 0] q := by
    filter_upwards [hnear] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hc t)).deriv
  have hff := (hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hff' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (c 0) := hc0.symm ▸ hff.hasFDerivAt
  have hh := (hff'.comp_hasDerivAt 0 (hc 0)).clm_apply (hasDerivAt_const 0 v)
  have hqq : HasDerivAt q ((fderiv ℝ (fderiv ℝ f) x v) v) 0 := by
    simpa only [Function.comp_def,ContinuousLinearMap.map_zero,add_zero,q] using hh
  rw [hq.deriv_eq,hqq.deriv]

lemma laplacian_lift [FiniteDimensional ℝ E] {φ φ₁ : ℝ → ℝ} {φ₂ : ℝ}
    (e x : E) (α : ℝ) (he : ‖e‖=1) (hx : x≠0)
    (hc : ContDiffAt ℝ 2 φ (inner ℝ x e / ‖x‖))
    (hφ : ∀ᶠ s in 𝓝 (inner ℝ x e / ‖x‖), HasDerivAt φ (φ₁ s) s)
    (hφ₁ : HasDerivAt φ₁ φ₂ (inner ℝ x e / ‖x‖)) :
    Δ (lift e α φ) x = ‖x‖^α / ‖x‖^2 *
      (α*(α+(Module.finrank ℝ E : ℝ)-2)*φ (inner ℝ x e / ‖x‖) -
        ((Module.finrank ℝ E : ℝ)-1)*(inner ℝ x e / ‖x‖)*φ₁ (inner ℝ x e / ‖x‖) +
        (1-(inner ℝ x e / ‖x‖)^2)*φ₂) := by
  let b := stdOrthonormalBasis ℝ E
  have hn := norm_ne_zero_iff.mpr hx
  have hp : ∑ i, (inner ℝ x (b i) / ‖x‖)^2 = 1 := by
    simp_rw [div_pow, ←Finset.sum_div]
    rw [b.sum_sq_inner_left]
    exact div_self (pow_ne_zero _ hn)
  have hb : ∑ i, (inner ℝ (b i) e)^2 = 1 := by
    rw [b.sum_sq_inner_right,he]
    norm_num
  have hpb : ∑ i, (inner ℝ x (b i) / ‖x‖) * inner ℝ (b i) e = inner ℝ x e / ‖x‖ := by
    simp_rw [div_mul_eq_mul_div, ←Finset.sum_div]
    rw [b.sum_inner_mul_inner]
  have hs := secondCoeff_sum α (φ (inner ℝ x e / ‖x‖)) (φ₁ (inner ℝ x e / ‖x‖)) φ₂
    (inner ℝ x e / ‖x‖) (fun i=>inner ℝ x (b i) / ‖x‖) (fun i=>inner ℝ (b i) e) hp hb hpb
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [iteratedFDeriv_two_apply]
  simp only [Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hcc := contDiffAt_lift (α:=α) hx hc
  simp_rw [←line_second_derivative hcc, lift_line_second e x _ α hx hφ hφ₁]
  have hbunit (i:Fin (Module.finrank ℝ E)) : ‖b i‖^2 = (1:ℝ) := by simp
  change (∑ i, ‖x‖^α / ‖x‖^2 * secondCoeff α (φ (inner ℝ x e / ‖x‖))
    (φ₁ (inner ℝ x e / ‖x‖)) φ₂ (inner ℝ x e / ‖x‖)
    (inner ℝ x (b i) / ‖x‖) (inner ℝ (b i) e) (‖b i‖^2)) = _
  simp_rw [hbunit, ←Finset.mul_sum]
  rw [hs]
  simp

/-- The radial unit vector (at nonzero points) and the tangential polar direction. -/
def radial (x : E) : E := ‖x‖⁻¹ • x

def polarGradient (e x : E) (a b : ℝ) : E :=
  a • radial x + b • (e - (inner ℝ x e / ‖x‖) • radial x)

lemma radial_norm {x : E} (hx : x≠0) : ‖radial x‖=1 := by
  rw [radial,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

lemma radial_inner (x e : E) : inner ℝ (radial x) e = inner ℝ x e / ‖x‖ := by
  simp only [radial,real_inner_smul_left,div_eq_mul_inv,mul_comm]

lemma norm_sq_polarGradient {e x : E} (he : ‖e‖=1) (hx : x≠0) (a b : ℝ) :
    ‖polarGradient e x a b‖^2 = a^2 + (1-(inner ℝ x e / ‖x‖)^2)*b^2 := by
  have hn : inner ℝ (radial x) (radial x)=1 := by
    rw [real_inner_self_eq_norm_sq,radial_norm hx]; norm_num
  have het : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he]; norm_num
  have hrev : inner ℝ e (radial x) = inner ℝ x e / ‖x‖ :=
    (real_inner_comm e (radial x)).symm.trans (radial_inner x e)
  rw [←real_inner_self_eq_norm_sq]
  simp only [polarGradient,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,hn,het,hrev,radial_inner]
  ring

lemma hasGradientAt_lift [CompleteSpace E] {φ : ℝ → ℝ} {φ₁ : ℝ}
    (e x : E) (α : ℝ) (hx : x≠0)
    (hφ : HasDerivAt φ φ₁ (inner ℝ x e / ‖x‖)) :
    HasGradientAt (lift e α φ)
      ((‖x‖^α / ‖x‖) • polarGradient e x (α*φ (inner ℝ x e / ‖x‖)) φ₁) x := by
  have hn := norm_ne_zero_iff.mpr hx
  have hdN : DifferentiableAt ℝ (fun y:E=>‖y‖) x := differentiableAt_id.norm ℝ hx
  have ha : ContDiffAt ℝ 1 (fun y:E=>inner ℝ y e / ‖y‖) x :=
    (contDiffAt_id.inner ℝ contDiffAt_const).div (contDiffAt_id.norm ℝ hx) hn
  have hdA := ha.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hd : DifferentiableAt ℝ (lift e α φ) x := by
    exact (hdN.rpow_const (Or.inl hn)).fun_mul (hφ.differentiableAt.comp x hdA)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  apply hd.hasFDerivAt.congr_fderiv
  ext v
  have hl : HasDerivAt (fun t:ℝ=>x+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hd0 : HasFDerivAt (lift e α φ) (fderiv ℝ (lift e α φ) x) (x+(0:ℝ) • v) := by
    simpa using hd.hasFDerivAt
  have hcomp := hd0.comp_hasDerivAt (0:ℝ) hl
  have hline := hasDerivAt_lift_line e x v α 0 (by simpa using hx) (by simpa using hφ)
  simp only [zero_smul,add_zero] at hline
  rw [hcomp.unique hline]
  simp only [InnerProductSpace.toDual_apply_apply,real_inner_smul_left,polarGradient,
    inner_add_left,inner_sub_left,real_inner_smul_left,radial,real_inner_smul_left,
    real_inner_comm e v]
  field_simp

lemma gradient_lift_norm_sq [CompleteSpace E] {φ : ℝ → ℝ} {φ₁ : ℝ}
    (e x : E) (α : ℝ) (he : ‖e‖=1) (hx : x≠0)
    (hφ : HasDerivAt φ φ₁ (inner ℝ x e / ‖x‖)) :
    ‖gradient (lift e α φ) x‖^2 = (‖x‖^α / ‖x‖)^2 *
      ((α*φ (inner ℝ x e / ‖x‖))^2+(1-(inner ℝ x e / ‖x‖)^2)*φ₁^2) := by
  rw [(hasGradientAt_lift e x α hx hφ).gradient,norm_smul,mul_pow]
  rw [norm_sq_polarGradient he hx]
  simp only [Real.norm_eq_abs,sq_abs]

end Bernoulli.Axisymmetric

namespace Bernoulli.DeSilvaJerison
open Axisymmetric InnerProductSpace
open scoped Laplacian ContDiff

def axis : Space 7 := EuclideanSpace.single 6 1

def angle (x : Space 7) : ℝ := x 6 / ‖x‖

@[simp] lemma axis_norm : ‖axis‖=1 := by simp [axis]
@[simp] lemma inner_axis (x : Space 7) : inner ℝ x axis=x 6 := by
  simp [axis, EuclideanSpace.inner_single_right]

lemma angle_contDiffAt {x : Space 7} {n : WithTop ℕ∞} (hx : x≠0) :
    ContDiffAt ℝ n angle x := by
  have hn : ContDiffAt ℝ n (fun y:Space 7=>‖y‖) x := contDiffAt_id.norm ℝ hx
  have hi : ContDiffAt ℝ n (fun y:Space 7=>inner ℝ y axis) x :=
    contDiffAt_id.inner ℝ contDiffAt_const
  unfold angle
  simpa only [inner_axis] using hi.fun_div hn (norm_ne_zero_iff.mpr hx)

lemma U_pos_iff (x : Space 7) : 0<U x ↔ x≠0 ∧ |angle x|<t7 := by
  rw [U, mul_pos_iff_of_pos_left κ_pos,Z]
  constructor
  · intro h
    have hx : x≠0 := by rintro rfl; simp at h
    exact ⟨hx, (p_pos_iff _).mp ((mul_pos_iff_of_pos_left (norm_pos_iff.mpr hx)).mp h)⟩
  · rintro ⟨hx,ht⟩
    exact mul_pos (norm_pos_iff.mpr hx) ((p_pos_iff _).mpr ht)

/-- Smooth signed extension near the free boundary away from the singular axis. -/
def Zsigned : Space 7 → ℝ := lift axis 1 f

def Usigned (x : Space 7) : ℝ := κ*Zsigned x

lemma Zsigned_eq (x : Space 7) : Zsigned x=‖x‖*f (angle x) := by
  simp [Zsigned,lift,angle]

lemma Z_eq_Zsigned {x : Space 7} (ht : |angle x|≤t7) : Z x=Zsigned x := by
  rw [Zsigned_eq,Z,p_eq_f (show |x 6 / ‖x‖|≤t7 from ht)]
  rfl

lemma U_eq_Usigned {x : Space 7} (ht : |angle x|≤t7) : U x=Usigned x := by
  unfold U Usigned
  rw [Z_eq_Zsigned ht]

lemma signed_contDiffAt {x : Space 7} {n : WithTop ℕ∞} (hx : x≠0)
    (ha : |angle x|<1) : ContDiffAt ℝ n Zsigned x := by
  apply contDiffAt_lift hx
  simpa only [inner_axis,angle] using contDiffAt_f (abs_lt.mp ha)

lemma signed_laplacian {x : Space 7} (hx : x≠0) (ha : |angle x|<1) : Δ Zsigned x=0 := by
  have ht : angle x ∈ Ioo (-1:ℝ) 1 := abs_lt.mp ha
  have hp : ∀ᶠ s in 𝓝 (inner ℝ x axis/‖x‖), HasDerivAt f (fp s) s := by
    simp only [inner_axis]
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hasDerivAt_f hs
  have ht' : inner ℝ x axis / ‖x‖ ∈ Ioo (-1:ℝ) 1 := by simpa only [inner_axis,angle] using ht
  have hl := laplacian_lift axis x 1 axis_norm hx (contDiffAt_f ht') hp (hasDerivAt_fp ht')
  have hd : 1-(angle x)^2≠0 := by nlinarith [sq_nonneg (angle x),ht.1,ht.2]
  have hr := f_relation ht
  have he : 6*f (angle x)-6*angle x*fp (angle x)+(1-(angle x)^2)*(-6/(1-(angle x)^2)^4)=0 := by
    field_simp at hr ⊢
    nlinarith [hr]
  change Δ (lift axis 1 f) x=0
  simp only [inner_axis,Space,finrank_euclideanSpace_fin, Nat.cast_ofNat] at hl
  norm_num only at hl
  change Δ (lift axis 1 f) x = ‖x‖^ (1:ℝ) / ‖x‖^2 *
    (6*f (angle x)-6*angle x*fp (angle x)+(1-(angle x)^2)*(-6/(1-(angle x)^2)^4)) at hl
  simpa only [he,mul_zero] using hl

lemma signed_harmonicAt {x : Space 7} (hx : x≠0) (ha : |angle x|<1) :
    HarmonicAt Zsigned x := by
  refine ⟨signed_contDiffAt hx ha,?_⟩
  have hN : ∀ᶠ y in 𝓝 x, y≠0 := isOpen_compl_singleton.mem_nhds hx
  have hA : ∀ᶠ y in 𝓝 x, |angle y|<1 :=
    (angle_contDiffAt (n:=1) hx).continuousAt.abs.eventually (gt_mem_nhds ha)
  filter_upwards [hN,hA] with y hy hya
  exact signed_laplacian hy hya

lemma U_eventuallyEq_Usigned {x : Space 7} (hu : 0<U x) : U =ᶠ[𝓝 x] Usigned := by
  obtain ⟨hx,ht⟩ := (U_pos_iff x).mp hu
  have hA : ∀ᶠ y in 𝓝 x, |angle y|<t7 :=
    (angle_contDiffAt (n:=1) hx).continuousAt.abs.eventually (gt_mem_nhds ht)
  exact hA.mono (fun y hy=>U_eq_Usigned hy.le)

/-- Positive-phase harmonicity is proved for the actual Sobolev candidate. -/
theorem U_harmonic : HarmonicOnNhd U {x|0<U x} := by
  intro x hu
  obtain ⟨hx,ht⟩ := (U_pos_iff x).mp hu
  apply (harmonicAt_congr_nhds (U_eventuallyEq_Usigned hu)).mpr
  exact (signed_harmonicAt hx (ht.trans t7_lt_one)).const_smul (c:=κ)

lemma fp_neg_arg (t : ℝ) : fp (-t)= -fp t := by
  simp only [fp,neg_sq,A_neg]
  ring

lemma f_zero_at_boundary {t : ℝ} (ht : |t|=t7) : f t=0 := by
  rw [←f_abs,ht,f_t7]

lemma fp_sq_at_boundary {t : ℝ} (ht : |t|=t7) : (fp t)^2=(fp t7)^2 := by
  have h : (fp |t|)^2=(fp t)^2 := by
    rcases le_total 0 t with h|h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,fp_neg_arg,neg_sq]
  rw [ht] at h
  exact h.symm

lemma signed_gradient_norm_sq {x : Space 7} (hx : x≠0) (ha : |angle x|<1) :
    ‖gradient Zsigned x‖^2=(f (angle x))^2+(1-(angle x)^2)*(fp (angle x))^2 := by
  have ha' : |inner ℝ x axis/‖x‖|<1 := by simpa only [inner_axis,angle] using ha
  have hh := gradient_lift_norm_sq axis x 1 axis_norm hx (hasDerivAt_f (abs_lt.mp ha'))
  simpa only [Zsigned,inner_axis,angle,Real.rpow_one,div_self (norm_ne_zero_iff.mpr hx),one_pow,one_mul] using hh

/-- Exact slope-squared c7 on the boundary of the unnormalized cone. -/
lemma Zsigned_boundary_slope {x : Space 7} (hx : x≠0) (ha : |angle x|=t7) :
    ‖gradient Zsigned x‖^2=c7 := by
  rw [signed_gradient_norm_sq hx (ha.trans_lt t7_lt_one),f_zero_at_boundary ha,
    fp_sq_at_boundary ha]
  have hs : (angle x)^2=t7^2 := by rw [←sq_abs,ha]
  simp only [hs,zero_pow (by norm_num : 2≠0),zero_add,c7]

lemma gradient_const_mul {F : Space 7 → ℝ} {x : Space 7} (c : ℝ)
    (hF : DifferentiableAt ℝ F x) :
    gradient (fun y=>c*F y) x=c • gradient F x := by
  rw [gradient, fderiv_const_mul hF]
  simp only [map_smul,gradient]

/-- The actual signed extension has exactly unit normal slope at every
nonvertex free-boundary point. This does not claim its energy comparison. -/
theorem Usigned_boundary_slope {x : Space 7} (hx : x≠0) (ha : |angle x|=t7) :
    ‖gradient Usigned x‖=1 := by
  have hd : DifferentiableAt ℝ Zsigned x :=
    (signed_contDiffAt (n:=1) hx (ha.trans_lt t7_lt_one)).differentiableAt (by norm_num)
  have he : gradient Usigned x=κ • gradient Zsigned x := gradient_const_mul κ hd
  have hs : ‖gradient Usigned x‖^2=1 := by
    rw [he,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Zsigned_boundary_slope hx ha,κ_sq]
  nlinarith [norm_nonneg (gradient Usigned x)]

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison
open scoped BigOperators

def B (n:ℕ) (u:ℝ) : ℝ := ∑ i ∈ Finset.range n, u^i / (2*i+1)

lemma B_nonneg (n:ℕ) {u:ℝ} (hu:0≤u) : 0≤B n u := by
  apply Finset.sum_nonneg
  intro i hi
  positivity

lemma odd_sum_eq (n:ℕ) (t:ℝ) :
    (∑ i ∈ Finset.range n, t^(2*i+1)/(2*i+1))=t*B n (t^2) := by
  rw [B,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_add,pow_mul]
  ring

lemma A_series_bounds (n:ℕ) {t:ℝ} (ht:0≤t) (ht1:t<1) :
    t*B n (t^2) ≤ A t ∧ A t ≤ t*(B n (t^2)+(t^2)^n/(1-t^2)) := by
  have hI : t∈Ioo (-1:ℝ) 1 := ⟨by linarith,ht1⟩
  have hL := Real.sum_range_le_log_div ht ht1 n
  have hU := Real.log_div_le_sum_range_add ht ht1 n
  rw [odd_sum_eq,A_eq_half_log hI] at *
  constructor
  · exact hL
  · convert hU using 1
    rw [pow_add,pow_mul]
    ring

lemma f_series_lower (n:ℕ) {t:ℝ} (ht:0≤t) (ht1:t<1) :
    (8-25*t^2+15*(t^2)^2)/(8*(1-t^2)^2)
      -15/8*t^2*(B n (t^2)+(t^2)^n/(1-t^2)) ≤ f t := by
  have ha := (A_series_bounds n ht ht1).2
  have hp := mul_le_mul_of_nonneg_left ha (show (0:ℝ)≤15/8*t from by positivity)
  unfold f
  convert! sub_le_sub_left hp ((8-25*t^2+15*t^4)/(8*(1-t^2)^2)) using 1
  ring

lemma fp_series_upper (n:ℕ) {t:ℝ} (ht:0≤t) (ht1:t<1) :
    fp t ≤ -t*(1/(1-t^2)^3+5/4/(1-t^2)^2+15/8/(1-t^2)+15/8*B n (t^2)) := by
  have ha := (A_series_bounds n ht ht1).1
  unfold fp
  have hp := mul_le_mul_of_nonneg_left ha (show (0:ℝ)≤15/8 from by norm_num)
  convert! sub_le_sub_left hp (-t/(1-t^2)^3-5/4*t/(1-t^2)^2-15/8*t/(1-t^2)) using 1
  ring

end Bernoulli.DeSilvaJerison

noncomputable section
open scoped BigOperators
namespace Bernoulli.DeSilvaJerison.Algebra
def g (u:ℝ) : ℝ := (1+u*((2869387/1000000:ℝ)+u*((589981/125000:ℝ)+u*((6566689/1000000:ℝ)+u*((4206127/500000:ℝ)+u*((10257227/1000000:ℝ)+u*((6050939/500000:ℝ)+u*((2789267/200000:ℝ)+u*(7895333/500000:ℝ)))))))))

def g1 (u:ℝ) : ℝ := ((2869387/1000000:ℝ)+u*((589981/62500:ℝ)+u*((19700067/1000000:ℝ)+u*((4206127/125000:ℝ)+u*((10257227/200000:ℝ)+u*((18152817/250000:ℝ)+u*((19524869/200000:ℝ)+u*(7895333/62500:ℝ))))))))

def g2 (u:ℝ) : ℝ := ((589981/62500:ℝ)+u*((19700067/500000:ℝ)+u*((12618381/125000:ℝ)+u*((10257227/50000:ℝ)+u*((18152817/50000:ℝ)+u*((58574607/100000:ℝ)+u*(55267331/62500:ℝ)))))))

def FlowNum (u:ℝ) : ℝ := (8+u*(-40+u*(40+u*(-8+u*((-8/7:ℝ)+u*((-8/21:ℝ)+u*((-40/231:ℝ)+u*((-460/33:ℝ)+u*(150/11:ℝ)))))))))

def JlowNum (u:ℝ) : ℝ := (48+u*(-80+u*(48+u*((-48/7:ℝ)+u*((-16/21:ℝ)+u*((-16/77:ℝ)+u*((-95/77:ℝ)+u*((80/33:ℝ)+u*(-15/11:ℝ)))))))))

def H (u:ℝ) : ℝ :=
 (1-(-643/200:ℝ))^2 * (FlowNum u)^2*(1-u)^2*(g u)^2
 +u*(1-u)*(JlowNum u*g u+2*FlowNum u*(1-u)*g1 u)^2
 -64*(177344/10000:ℝ)*(1-u)^6*(g u)^2

def bern (x:ℝ) :ℝ :=
 (1273/625:ℝ)*x^0*(1-x)^34 +
 (18301700752813/39062500000:ℝ)*x^1*(1-x)^33 +
 (215052290412518053937/15625000000000000:ℝ)*x^2*(1-x)^32 +
 (4011660524023528296977/19531250000000000:ℝ)*x^3*(1-x)^31 +
 (2737813200177456418780827/1367187500000000000:ℝ)*x^4*(1-x)^30 +
 (36470062299690915838876891/2563476562500000000:ℝ)*x^5*(1-x)^29 +
 (25224069904037561558116841153/322265625000000000000:ℝ)*x^6*(1-x)^28 +
 (1140064408982925692415284885429/3289794921875000000000:ℝ)*x^7*(1-x)^27 +
 (41702430755303183867323989789361/32897949218750000000000:ℝ)*x^8*(1-x)^26 +
 (3302410109850186979935464577903227/845947265625000000000000:ℝ)*x^9*(1-x)^25 +
 (607809096133375762153335847523839391/59216308593750000000000000:ℝ)*x^10*(1-x)^24 +
 (8427099588852868346099742136229588957/361877441406250000000000000:ℝ)*x^11*(1-x)^23 +
 (83162165720757436741420385026341254509/1809387207031250000000000000:ℝ)*x^12*(1-x)^22 +
 (6465714023183326120974320513863787790989/81422424316406250000000000000:ℝ)*x^13*(1-x)^21 +
 (3070489019357153411700150072588091455833/25444507598876953125000000000:ℝ)*x^14*(1-x)^20 +
 (82369624574464912186052678411201103823739/508890151977539062500000000000:ℝ)*x^15*(1-x)^19 +
 (3910314359275519861283649778682853171355229/20355606079101562500000000000000:ℝ)*x^16*(1-x)^18 +
 (979175253390516279186463881299949127320211/4846572875976562500000000000000:ℝ)*x^17*(1-x)^17 +
 (18263450287363530970672089631693726965414361/96931457519531250000000000000000:ℝ)*x^18*(1-x)^16 +
 (17617068143172995639202711944743442184849557/113086700439453125000000000000000:ℝ)*x^19*(1-x)^15 +
 (5805157568137808862325200615665450856083238073/50889015197753906250000000000000000:ℝ)*x^20*(1-x)^14 +
 (106751395374573342818643134988112428956196041/1445710659027099609375000000000000:ℝ)*x^21*(1-x)^13 +
 (13399476602886887470912830751358415258789263239/318056344985961914062500000000000000:ℝ)*x^22*(1-x)^12 +
 (203394843320074906765348971241270582814374973/9638071060180664062500000000000000:ℝ)*x^23*(1-x)^11 +
 (73412104728736551372464217800669117696986097123/7951408624649047851562500000000000000:ℝ)*x^24*(1-x)^10 +
 (139309476218905417280721075386752271276084623033/39757043123245239257812500000000000000:ℝ)*x^25*(1-x)^9 +
 (32477127068915750179291210097408098171730074813/28397887945175170898437500000000000000:ℝ)*x^26*(1-x)^8 +
 (39433145196824909814460561789894422591933034093/124240759760141372680664062500000000000:ℝ)*x^27*(1-x)^7 +
 (1852317908162190170035216935656039577364200647/25099143385887145996093750000000000000:ℝ)*x^28*(1-x)^6 +
 (5836982899230309706402487066150347002468521567/414135865867137908935546875000000000000:ℝ)*x^29*(1-x)^5 +
 (53440683331803983473324825254354074715316174661/24848151952028274536132812500000000000000:ℝ)*x^30*(1-x)^4 +
 (1564303979409844850797520400352897238700085837/6212037988007068634033203125000000000000:ℝ)*x^31*(1-x)^3 +
 (219633445088755317503000659291685432421229847/10353396646678447723388671875000000000000:ℝ)*x^32*(1-x)^2 +
 (4437106302213137739667714564011045560602003/3882523742504417896270751953125000000000:ℝ)*x^33*(1-x)^1 +
 (57307964213152837654157884692498315776209/1941261871252208948135375976562500000000:ℝ)*x^34*(1-x)^0

lemma identity (x:ℝ) : H ((1/5:ℝ)*x)=bern x := by
  unfold H FlowNum JlowNum g g1 bern
  ring

lemma bern_nonneg {x:ℝ} (hx:0≤x) (hx1:x≤1) : 0≤bern x := by
  have hy : 0≤1-x := sub_nonneg.mpr hx1
  unfold bern
  positivity

lemma H_nonneg {u:ℝ} (hu:0≤u) (hu1:u≤1/5) : 0≤H u := by
  have he : u=(1/5:ℝ)*(u/(1/5)) := by ring
  rw [he,identity]
  apply bern_nonneg
  · positivity
  · rw [div_le_one (by norm_num : (0:ℝ)<1/5)]
    exact hu1

lemma hasDerivAt_g (u:ℝ) : HasDerivAt g (g1 u) u := by
  have hh := ((hasDerivAt_const u 1).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (2869387/1000000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (589981/125000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (6566689/1000000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (4206127/500000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (10257227/1000000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (6050939/500000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (2789267/200000:ℝ)).add ((hasDerivAt_id u).mul (hasDerivAt_const u (7895333/500000:ℝ))))))))))))))))))
  convert! hh using 1
  simp only [g1, Pi.add_apply, Pi.mul_apply, id_eq]
  ring

lemma hasDerivAt_g1 (u:ℝ) : HasDerivAt g1 (g2 u) u := by
  have hh := ((hasDerivAt_const u (2869387/1000000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (589981/62500:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (19700067/1000000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (4206127/125000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (10257227/200000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (18152817/250000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (19524869/200000:ℝ)).add ((hasDerivAt_id u).mul (hasDerivAt_const u (7895333/62500:ℝ))))))))))))))))
  convert! hh using 1
  simp only [g2, Pi.add_apply, Pi.mul_apply, id_eq]
  ring

lemma g_ge_one {u:ℝ} (hu:0≤u) : 1≤g u := by
  unfold g
  have : 0≤u*((2869387/1000000:ℝ)+u*((589981/125000:ℝ)+u*((6566689/1000000:ℝ)+u*((4206127/500000:ℝ)+u*((10257227/1000000:ℝ)+u*((6050939/500000:ℝ)+u*((2789267/200000:ℝ)+u*(7895333/500000:ℝ)))))))) := by positivity
  linarith

lemma g1_nonneg {u:ℝ} (hu:0≤u) : 0≤g1 u := by unfold g1; positivity

lemma g_residual_nonpos {u:ℝ} (hu:0≤u) :
    (1-u)*(2*g1 u+4*u*g2 u)-12*u*g1 u+(-643/200:ℝ)*(-643/200+5)*g u ≤0 := by
  have he : -((1-u)*(2*g1 u+4*u*g2 u)-12*u*g1 u+(-643/200:ℝ)*(-643/200+5)*g u) =
      ((1/1000000:ℝ)+u*((335237/40000000000:ℝ)+u*((18531/5000000000:ℝ)+u*((26639/40000000000:ℝ)+u*((378977/20000000000:ℝ)+u*((2875077/40000000000:ℝ)+u*((1938389/20000000000:ℝ)+u*((1189117/8000000000:ℝ)+u*(107925657105483/20000000000:ℝ))))))))) := by unfold g g1 g2; ring
  have hz : 0≤ -((1-u)*(2*g1 u+4*u*g2 u)-12*u*g1 u+(-643/200:ℝ)*(-643/200+5)*g u) := by
    rw [he]
    positivity
  linarith

lemma lower_logder {u:ℝ} (hu:0≤u) (hub:u≤(27/100:ℝ)) : 0≤2*(1-u)*g1 u-5*g u := by
  let x:=u/(27/100:ℝ)
  have hx:0≤x := by dsimp [x]; positivity
  have hy:0≤1-x := by dsimp [x]; linarith
  have he : 2*(1-u)*g1 u-5*g u =
      (369387/500000:ℝ)*x^0*(1-x)^8 + (558448641/100000000:ℝ)*x^1*(1-x)^7 + (90906551829/5000000000:ℝ)*x^2*(1-x)^6 + (33087845213199/1000000000000:ℝ)*x^3*(1-x)^5 + (910658646456597/25000000000000:ℝ)*x^4*(1-x)^4 + (243550667389510017/10000000000000000:ℝ)*x^5*(1-x)^3 + (1156300362730287837/125000000000000000:ℝ)*x^6*(1-x)^2 + (160712254758181821273/100000000000000000000:ℝ)*x^7*(1-x)^1 + (141611539097570077017/5000000000000000000000:ℝ)*x^8*(1-x)^0 := by
    dsimp [x]
    unfold g g1
    ring
  rw [he]
  positivity

lemma upper_logder {u:ℝ} (hu:0≤u) (hub:u≤(27/100:ℝ)) : 0≤2*g u-(13/25)*g1 u := by
  let x:=u/(27/100:ℝ)
  have hx:0≤x := by dsimp [x]; positivity
  have hy:0≤1-x := by dsimp [x]; linarith
  have he : 2*g u-(13/25)*g1 u =
      (12697969/25000000:ℝ)*x^0*(1-x)^8 + (5359357177/1250000000:ℝ)*x^1*(1-x)^7 + (3933009652441/250000000000:ℝ)*x^2*(1-x)^6 + (408907285769443/12500000000000:ℝ)*x^3*(1-x)^5 + (21018853182775349/500000000000000:ℝ)*x^4*(1-x)^4 + (4252809530492624731/125000000000000000:ℝ)*x^5*(1-x)^3 + (83958125315148478907/5000000000000000000:ℝ)*x^6*(1-x)^2 + (5678700560736300182329/1250000000000000000000:ℝ)*x^7*(1-x)^1 + (1242771118592263674331/2500000000000000000000:ℝ)*x^8*(1-x)^0 := by
    dsimp [x]
    unfold g g1
    ring
  rw [he]
  positivity

lemma FlowNum_nonneg {u:ℝ} (hu:0≤u) (hub:u≤(1/5:ℝ)) : 0≤FlowNum u := by
  let x:=u/(1/5:ℝ)
  have hx:0≤x := by dsimp [x]; positivity
  have hy:0≤1-x := by dsimp [x]; linarith
  have he : FlowNum u =
      8*x^0*(1-x)^8 + 56*x^1*(1-x)^7 + (848/5:ℝ)*x^2*(1-x)^6 + (36192/125:ℝ)*x^3*(1-x)^5 + (1328592/4375:ℝ)*x^4*(1-x)^4 + (13082512/65625:ℝ)*x^5*(1-x)^3 + (57279808/721875:ℝ)*x^6*(1-x)^2 + (62341556/3609375:ℝ)*x^7*(1-x)^1 + (5536402/3609375:ℝ)*x^8*(1-x)^0 := by
    dsimp [x]
    unfold FlowNum
    ring
  rw [he]
  positivity

end Bernoulli.DeSilvaJerison.Algebra

namespace Bernoulli.DeSilvaJerison

def gSub (t:ℝ) : ℝ := Algebra.g (t^2)
def gSub1 (t:ℝ) : ℝ := 2*t*Algebra.g1 (t^2)
def gSub2 (t:ℝ) : ℝ := 2*Algebra.g1 (t^2)+4*t^2*Algebra.g2 (t^2)
def qSub (t:ℝ) : ℝ := gSub1 t/gSub t

lemma gSub_pos (t:ℝ) : 0<gSub t := by
  have h:=Algebra.g_ge_one (sq_nonneg t)
  unfold gSub
  linarith

lemma hasDerivAt_gSub (t:ℝ) : HasDerivAt gSub (gSub1 t) t := by
  have hh:=(Algebra.hasDerivAt_g (t^2)).comp t (hasDerivAt_pow 2 t)
  convert! hh using 1
  dsimp only [gSub1,Function.comp_apply,id_eq]
  norm_num only
  ring

lemma hasDerivAt_gSub1 (t:ℝ) : HasDerivAt gSub1 (gSub2 t) t := by
  have hh:=((hasDerivAt_id t).const_mul 2).mul
    ((Algebra.hasDerivAt_g1 (t^2)).comp t (hasDerivAt_pow 2 t))
  convert! hh using 1
  dsimp only [gSub2,Function.comp_apply,id_eq]
  norm_num only
  ring

lemma gSub_residual (t:ℝ) :
    (1-t^2)*gSub2 t-6*t*gSub1 t+(-643/200:ℝ)*(-643/200+5)*gSub t ≤0 := by
  convert! Algebra.g_residual_nonpos (sq_nonneg t) using 1
  unfold gSub gSub1 gSub2
  ring

lemma qSub_nonneg {t:ℝ} (ht:0≤t) : 0≤qSub t := by
  unfold qSub gSub1
  exact div_nonneg (by have:=Algebra.g1_nonneg (sq_nonneg t); positivity) (gSub_pos t).le

lemma qSub_bounds {t:ℝ} (ht:0≤t) (hT:t≤t7) :
    5*t≤(1-t^2)*qSub t ∧ qSub t≤4 := by
  have htl:t≤517331/1000000 := hT.trans t7_bounds.2
  have hu:t^2≤27/100 := by nlinarith
  have hd:=Algebra.lower_logder (sq_nonneg t) hu
  have hm:=Algebra.upper_logder (sq_nonneg t) hu
  have hp:=Algebra.g1_nonneg (sq_nonneg t)
  have hg:=gSub_pos t
  unfold qSub gSub1 gSub at *
  constructor
  · rw [←mul_div_assoc]
    apply (le_div_iff₀ hg).mpr
    have hh:=mul_nonneg ht hd
    nlinarith
  · apply (div_le_iff₀ hg).mpr
    have hh:=mul_le_mul_of_nonneg_right (show 2*t≤26/25 by linarith) hp
    linarith

lemma c7_upper : c7≤177344/10000 := by
  have hl:t7^2≥(517330/1000000:ℝ)^2 := by nlinarith [t7_bounds.1,t7_pos]
  have hu:1-t7^2≥1-(517331/1000000:ℝ)^2 := by nlinarith [t7_bounds.2,t7_pos]
  have hp:=pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1-(517331/1000000:ℝ)^2) hu 5
  have hm:=mul_le_mul hl hp (by norm_num : (0:ℝ)≤(1-(517331/1000000:ℝ)^2)^5) (sq_nonneg t7)
  have ht : 0<1-t7^2 := by nlinarith [t7_pos,t7_lt_one]
  have hT:=t7_pos
  rw [c7_eq]
  apply (div_le_iff₀ (by positivity : 0<t7^2*(1-t7^2)^5)).mpr
  norm_num at hm
  linarith

lemma fp_strictAnti : StrictAntiOn fp (Ico (0:ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ico 0 1)
  · intro t ht
    exact (hasDerivAt_fp ⟨by linarith [ht.1],ht.2⟩).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ico] at ht
    rw [(hasDerivAt_fp ⟨by linarith [ht.1],ht.2⟩).deriv]
    have hp : 0<1-t^2 := by nlinarith [ht.1,ht.2]
    exact div_neg_of_neg_of_pos (by norm_num) (pow_pos hp 4)

lemma sub_endpoint_bounds : f (11/25)≤1/3 ∧ fp (11/25)≤-7/2 := by
  have ha : 4722/10000 ≤ A (11/25) := by
    rw [A_eq_half_log (by norm_num)]
    refine le_trans ?_ (Real.sum_range_le_log_div (by norm_num) (by norm_num) 6)
    norm_num [Finset.sum_range_succ]
  constructor <;> dsimp only [f,fp] <;> norm_num at ha ⊢ <;> linarith

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison

/-- The free-boundary gradient numerator for the explicit lower barrier. -/
def GSub (t:ℝ) : ℝ := (1-(-643/200:ℝ))^2*(f t)^2+
  (1-t^2)*(fp t-f t*qSub t)^2

def FLo (t:ℝ) : ℝ := Algebra.FlowNum (t^2)/(8*(1-t^2)^2)
def JLo (t:ℝ) : ℝ := Algebra.JlowNum (t^2)/(8*(1-t^2)^3)

lemma FLo_le {t:ℝ} (ht:0≤t) (ht1:t<1) : FLo t≤f t := by
  have hd:1-t^2≠0 := by nlinarith
  convert! f_series_lower 6 ht ht1 using 1
  unfold FLo Algebra.FlowNum B
  norm_num [Finset.sum_range_succ]
  field_simp [hd]
  ring

lemma fp_le_JLo {t:ℝ} (ht:0≤t) (ht1:t<1) : fp t≤-t*JLo t := by
  have hd:1-t^2≠0 := by nlinarith
  convert! fp_series_upper 6 ht ht1 using 1
  unfold JLo Algebra.JlowNum B
  norm_num [Finset.sum_range_succ]
  field_simp [hd]
  ring_nf
  simp

lemma JLo_nonneg {t:ℝ} (ht:0≤t) (ht1:t<1) : 0≤JLo t := by
  have hd:0<1-t^2 := by nlinarith
  have he : JLo t=1/(1-t^2)^3+5/4/(1-t^2)^2+15/8/(1-t^2)+15/8*B 6 (t^2) := by
    unfold JLo Algebra.JlowNum B
    norm_num [Finset.sum_range_succ]
    field_simp
    ring
  rw [he]
  have hh:=B_nonneg 6 (sq_nonneg t)
  positivity

lemma GSub_low {t:ℝ} (ht:0≤t) (htb:t≤11/25) : c7≤GSub t := by
  have ht1:t<1 := by linarith
  have hd:0<1-t^2 := by nlinarith
  have hu:t^2≤1/5 := by nlinarith
  have hg:=gSub_pos t
  have hF:0≤FLo t := div_nonneg (Algebra.FlowNum_nonneg (sq_nonneg t) hu) (by positivity)
  have hL:=FLo_le ht ht1
  have hp:=fp_le_JLo ht ht1
  have hJ:=JLo_nonneg ht ht1
  have hq:=qSub_nonneg ht
  have hB: t*JLo t+FLo t*qSub t ≤ -(fp t-f t*qSub t) := by
    have hh:=mul_le_mul_of_nonneg_right hL hq
    linarith
  have hB0:0≤t*JLo t+FLo t*qSub t := by positivity
  have hs1 := sq_le_sq₀ hF (hF.trans hL) |>.mpr hL
  have hs2 := sq_le_sq₀ hB0 (hB0.trans hB) |>.mpr hB
  have hH:=Algebra.H_nonneg (sq_nonneg t) hu
  have he : Algebra.H (t^2) =
      64*(1-t^2)^6*(gSub t)^2 *
        ((1-(-643/200:ℝ))^2*(FLo t)^2+(1-t^2)*(t*JLo t+FLo t*qSub t)^2-177344/10000) := by
    unfold Algebra.H FLo JLo qSub gSub gSub1
    have hgn : Algebra.g (t^2) ≠ 0 := ne_of_gt hg
    field_simp [ne_of_gt hd,hgn]
    ring
  rw [he] at hH
  have hn := (mul_nonneg_iff_of_pos_left (by positivity : 0<64*(1-t^2)^6*(gSub t)^2)).mp hH
  have hu1:=mul_le_mul_of_nonneg_left hs1 (show (0:ℝ)≤(1-(-643/200:ℝ))^2 by positivity)
  have hu2:=mul_le_mul_of_nonneg_left hs2 hd.le
  dsimp [GSub]
  nlinarith [c7_upper]

lemma hasDerivAt_qSub (t:ℝ) :
    HasDerivAt qSub (gSub2 t/gSub t-(qSub t)^2) t := by
  have hh := (hasDerivAt_gSub1 t).div (hasDerivAt_gSub t) (ne_of_gt (gSub_pos t))
  convert! hh using 1
  unfold qSub
  field_simp

lemma qSub_deriv_bound {t:ℝ} (_ht:0≤t) (_ht1:t<1) :
    (1-t^2)*(gSub2 t/gSub t-(qSub t)^2) ≤
      6*t*qSub t-(-643/200:ℝ)*(-643/200+5)-(1-t^2)*(qSub t)^2 := by
  have hg:=gSub_pos t
  have hh:=gSub_residual t
  have he : (1-t^2)*(gSub2 t/gSub t-(qSub t)^2)-
      (6*t*qSub t-(-643/200:ℝ)*(-643/200+5)-(1-t^2)*(qSub t)^2) =
      ((1-t^2)*gSub2 t-6*t*gSub1 t+(-643/200:ℝ)*(-643/200+5)*gSub t)/gSub t := by
    unfold qSub
    field_simp
    ring
  have hz:=div_nonpos_of_nonpos_of_nonneg hh hg.le
  linarith

lemma hasDerivAt_GSub {t:ℝ} (ht:t∈Ioo (-1:ℝ) 1) :
    HasDerivAt GSub
      (2*((1-(-643/200:ℝ))^2*f t*fp t-t*(fp t-f t*qSub t)^2+
        (1-t^2)*(fp t-f t*qSub t)*(-6/(1-t^2)^4-fp t*qSub t-f t*(gSub2 t/gSub t-(qSub t)^2)))) t := by
  have hh:=(((hasDerivAt_f ht).pow 2).const_mul ((1-(-643/200:ℝ))^2)).add
    (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)).mul
      (((hasDerivAt_fp ht).sub ((hasDerivAt_f ht).mul (hasDerivAt_qSub t))).pow 2))
  convert! hh using 1
  norm_num only [id_eq,pow_one,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply]
  ring

lemma GSub_nonpos_deriv {t:ℝ} (ht:11/25≤t) (ht7:t≤t7) : deriv GSub t ≤0 := by
  have ht0:0≤t := by linarith
  have ht1:t<1:=ht7.trans_lt t7_lt_one
  have hI:t∈Ioo (-1:ℝ) 1:=⟨by linarith,ht1⟩
  have hd:0<1-t^2 := by nlinarith
  have hf0:0≤f t := by
    have hh:=f_strictAnti.antitoneOn ⟨ht0,ht1⟩ ⟨t7_pos.le,t7_lt_one⟩ ht7
    simpa only [f_t7] using hh
  have hfall : f t ≤ f (11/25) := f_strictAnti.antitoneOn ⟨by norm_num,by norm_num⟩ ⟨ht0,ht1⟩ ht
  have hfp : fp t ≤ fp (11/25) := fp_strictAnti.antitoneOn ⟨by norm_num,by norm_num⟩ ⟨ht0,ht1⟩ ht
  have hf:f t≤1/3:=hfall.trans sub_endpoint_bounds.1
  have hp:fp t≤-7/2:=hfp.trans sub_endpoint_bounds.2
  have hq:=qSub_nonneg ht0
  obtain ⟨hqL,hqU⟩:=qSub_bounds ht0 ht7
  have hb:fp t-f t*qSub t≤0 := by nlinarith [mul_nonneg hf0 hq]
  have hres:=qSub_deriv_bound ht0 ht1
  have hODE: (1-t^2)*(-6/(1-t^2)^4)=6*t*fp t-6*f t := by
    have hh:=f_relation hI
    field_simp at hh ⊢
    nlinarith
  have hbd : (1-t^2)*(-6/(1-t^2)^4-fp t*qSub t-f t*(gSub2 t/gSub t-(qSub t)^2)) ≥
      6*t*fp t-6*f t-(1-t^2)*fp t*qSub t-
        f t*(6*t*qSub t-(-643/200:ℝ)*(-643/200+5)-(1-t^2)*(qSub t)^2) := by
    have hh:=mul_le_mul_of_nonneg_left hres hf0
    nlinarith only [hh,hODE]
  have hmul:=mul_le_mul_of_nonpos_left hbd hb
  rw [(hasDerivAt_GSub hI).deriv]
  have hfirst : (5*t-(1-t^2)*qSub t)*(fp t-f t*qSub t)^2 ≤0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have hlast : (6.02745:ℝ)*fp t+(11.738775:ℝ)*f t*qSub t≤0 := by
    have hmul:=mul_le_mul hf hqU hq (by norm_num : (0:ℝ)≤1/3)
    linarith
  have hlast2:=mul_nonpos_of_nonneg_of_nonpos hf0 hlast
  nlinarith only [hmul,hfirst,hlast2]

lemma GSub_high {t:ℝ} (ht:11/25≤t) (ht7:t≤t7) : c7≤GSub t := by
  have hcont:ContinuousOn GSub (Icc (11/25) t7) := by
    intro x hx
    exact (hasDerivAt_GSub ⟨by linarith [hx.1],hx.2.trans_lt t7_lt_one⟩).continuousAt.continuousWithinAt
  have hanti:AntitoneOn GSub (Icc (11/25) t7) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_GSub ⟨by linarith [hx.1],hx.2.trans t7_lt_one⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact GSub_nonpos_deriv hx.1.le hx.2.le
  have he:GSub t7=c7 := by simp [GSub,f_t7,c7]
  rw [←he]
  exact hanti ⟨ht,ht7⟩ ⟨by linarith [t7_bounds.1],le_rfl⟩ ht7

/-- Exact substitute for DSJ's numerical lower-barrier plot in dimension seven. -/
theorem GSub_ge_c7 {t:ℝ} (ht:0≤t) (ht7:t≤t7) : c7≤GSub t := by
  by_cases h:t≤11/25
  · exact GSub_low ht h
  · exact GSub_high (le_of_lt (lt_of_not_ge h)) ht7

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison
open Axisymmetric InnerProductSpace
open scoped Laplacian ContDiff

lemma qSub_neg (t:ℝ) : qSub (-t)= -qSub t := by
  simp only [qSub,gSub,gSub1,neg_sq]
  ring

lemma GSub_neg (t:ℝ) : GSub (-t)=GSub t := by
  rw [GSub,GSub,f_neg,fp_neg_arg,qSub_neg,neg_sq]
  ring

lemma GSub_ge_c7_abs {t:ℝ} (ht:|t|≤t7) : c7≤GSub t := by
  have hh:=GSub_ge_c7 (abs_nonneg t) ht
  rcases le_total 0 t with hp|hn
  · simpa only [abs_of_nonneg hp] using hh
  · simpa only [abs_of_nonpos hn,GSub_neg] using hh

lemma gSub_contDiff {n:WithTop ℕ∞} : ContDiff ℝ n gSub := by
  unfold gSub Algebra.g
  fun_prop

/-- Positive superharmonic ground state used by the lower comparison. -/
def YSub : Space 7 → ℝ := lift axis (-643/200) gSub

lemma YSub_pos {x:Space 7} (hx:x≠0) : 0<YSub x := by
  unfold YSub lift
  exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _) (gSub_pos _)

lemma YSub_contDiffAt {x:Space 7} {n:WithTop ℕ∞} (hx:x≠0) :
    ContDiffAt ℝ n YSub x := contDiffAt_lift hx gSub_contDiff.contDiffAt

/-- An actual sign of the Euclidean Laplacian, not a barrier hypothesis. -/
theorem YSub_superharmonic {x:Space 7} (hx:x≠0) : Δ YSub x≤0 := by
  have hp : ∀ᶠ s in 𝓝 (inner ℝ x axis/‖x‖), HasDerivAt gSub (gSub1 s) s :=
    Filter.Eventually.of_forall hasDerivAt_gSub
  have hh:=laplacian_lift axis x (-643/200) axis_norm hx
    (gSub_contDiff (n:=2)).contDiffAt hp (hasDerivAt_gSub1 _)
  rw [YSub,hh]
  have hR:=gSub_residual (inner ℝ x axis/‖x‖)
  have he : (-643/200:ℝ)*(-643/200+(Module.finrank ℝ (Space 7):ℝ)-2)*
      gSub (inner ℝ x axis/‖x‖)-((Module.finrank ℝ (Space 7):ℝ)-1)*
      (inner ℝ x axis/‖x‖)*gSub1 (inner ℝ x axis/‖x‖)+
      (1-(inner ℝ x axis/‖x‖)^2)*gSub2 (inner ℝ x axis/‖x‖)≤0 := by
    simp only [Space,finrank_euclideanSpace_fin,Nat.cast_ofNat]
    nlinarith [hR]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) he

lemma Usigned_gradient {x:Space 7} (hx:x≠0) (ha:|angle x|<1) :
    gradient Usigned x=κ • polarGradient axis x (f (angle x)) (fp (angle x)) := by
  have hi : inner ℝ x axis/‖x‖∈Ioo (-1:ℝ) 1 := by
    simpa only [inner_axis,angle,Set.mem_Ioo] using abs_lt.mp ha
  rw [show gradient Usigned x=κ • gradient Zsigned x from
    gradient_const_mul κ ((signed_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num))]
  rw [Zsigned,(hasGradientAt_lift axis x 1 hx (hasDerivAt_f hi)).gradient]
  simp only [Real.rpow_one,div_self (norm_ne_zero_iff.mpr hx),one_smul,one_mul,inner_axis,angle]

lemma YSub_gradient {x:Space 7} (hx:x≠0) :
    gradient YSub x=(‖x‖^(-643/200:ℝ)/‖x‖) •
      polarGradient axis x ((-643/200:ℝ)*gSub (angle x)) (gSub1 (angle x)) := by
  simpa only [YSub,inner_axis,angle] using
    (hasGradientAt_lift axis x (-643/200) hx (hasDerivAt_gSub _)).gradient

lemma U_gradient {x:Space 7} (hu:0<U x) :
    gradient U x=κ • polarGradient axis x (f (angle x)) (fp (angle x)) := by
  obtain ⟨hx,ha⟩:=(U_pos_iff x).mp hu
  have he:gradient U x=gradient Usigned x := by
    rw [gradient,(U_eventuallyEq_Usigned hu).fderiv_eq]
    rfl
  rw [he,Usigned_gradient hx (ha.trans t7_lt_one)]

/-- The square-completion vector of the lower comparison has norm at least one
throughout the entire positive phase of the concrete seven-dimensional cone. -/
theorem lower_groundstate_slope {x:Space 7} (hu:0<U x) :
    1≤‖gradient U x-(U x/YSub x) • gradient YSub x‖^2 := by
  obtain ⟨hx,ha⟩:=(U_pos_iff x).mp hu
  have hn:=norm_ne_zero_iff.mpr hx
  have hg:=ne_of_gt (gSub_pos (angle x))
  have hr:=ne_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) (-643/200:ℝ))
  have hU : U x=κ*‖x‖*f (angle x) := by
    rw [U_eq_Usigned ha.le,Usigned,Zsigned_eq]
    ring
  have he : gradient U x-(U x/YSub x) • gradient YSub x=
      κ • polarGradient axis x ((1-(-643/200:ℝ))*f (angle x))
        (fp (angle x)-f (angle x)*qSub (angle x)) := by
    rw [U_gradient hu,YSub_gradient hx,hU]
    have hy : YSub x = ‖x‖^(-643/200:ℝ)*gSub (angle x) := by
      simp only [YSub,lift,inner_axis,angle]
    rw [hy]
    unfold polarGradient qSub
    simp only [inner_axis]
    ext i
    simp only [PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    unfold angle at *
    field_simp [hn,hg,hr]
    ring
  rw [he,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,norm_sq_polarGradient axis_norm hx]
  have hG:=mul_le_mul_of_nonneg_left (GSub_ge_c7_abs ha.le) (sq_nonneg κ)
  rw [κ_sq] at hG
  simpa only [GSub,inner_axis,angle,mul_pow] using hG

end Bernoulli.DeSilvaJerison

end
end
end
end
end

end OAI
