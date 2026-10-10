import OAI.Geometry.ProjectionBodies.SupportMeasures

namespace OAI

noncomputable section
open Set Filter Topology
namespace PettyProjection.Spherical

def softAbs (ε t : ℝ) : ℝ := Real.sqrt (t^2+ε)
def softSign (ε t : ℝ) : ℝ := t/softAbs ε t
def softSlope (ε t : ℝ) : ℝ := ε/(softAbs ε t)^3

lemma softAbs_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 < softAbs ε t :=
  Real.sqrt_pos.mpr (by positivity)

lemma softAbs_sq {ε : ℝ} (hε : 0 < ε) (t : ℝ) : (softAbs ε t)^2 = t^2+ε :=
  Real.sq_sqrt (by positivity)

lemma softAbs_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ⊤ (softAbs ε) := by
  exact ((contDiff_id.pow 2).add contDiff_const).sqrt (fun t => ne_of_gt (by positivity))

lemma softSign_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ⊤ (softSign ε) :=
  contDiff_id.div (softAbs_contDiff hε) (fun t => (softAbs_pos hε t).ne')

lemma softAbs_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (softAbs ε) (softSign ε t) t := by
  have h := ((hasDerivAt_pow 2 t).add_const ε).sqrt (by positivity : t^2+ε ≠ 0)
  convert! h using 1
  simp only [softSign, softAbs, Nat.cast_ofNat]
  ring

lemma softSign_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (softSign ε) (softSlope ε t) t := by
  have h := (hasDerivAt_id t).div (softAbs_hasDerivAt hε t) (softAbs_pos hε t).ne'
  convert! h using 1
  dsimp [softSlope, softSign]
  field_simp [(softAbs_pos hε t).ne']
  nlinarith [softAbs_sq hε t]

lemma abs_le_softAbs {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |t| ≤ softAbs ε t := by
  have hs := softAbs_sq hε t
  have hp := (softAbs_pos hε t).le
  nlinarith [sq_abs t, abs_nonneg t]

lemma softAbs_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) : softAbs ε t ≤ |t|+Real.sqrt ε := by
  have hs := softAbs_sq hε t
  have hp := (softAbs_pos hε t).le
  have he := Real.sq_sqrt hε.le
  have hn := mul_nonneg (abs_nonneg t) (Real.sqrt_nonneg ε)
  nlinarith [sq_abs t, abs_nonneg t, Real.sqrt_nonneg ε]

lemma abs_softSign_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |softSign ε t| ≤ 1 := by
  rw [softSign, abs_div, abs_of_pos (softAbs_pos hε t), div_le_one (softAbs_pos hε t)]
  exact abs_le_softAbs hε t

lemma abs_softCorrection_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |t*softSlope ε t| ≤ 1 := by
  have hp := softAbs_pos hε t
  have hs : ε ≤ (softAbs ε t)^2 := by nlinarith [softAbs_sq hε t, sq_nonneg t]
  have hm := mul_le_mul (abs_le_softAbs hε t) hs hε.le hp.le
  rw [softSlope, ← mul_div_assoc, abs_div, abs_of_pos (pow_pos hp _),
    abs_mul, abs_of_pos hε, div_le_one (pow_pos hp _)]
  nlinarith

lemma real_sign_eq (t : ℝ) : Real.sign t = t/|t| := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [Real.sign_of_neg ht, abs_of_neg ht]
    field_simp [ht.ne]
  · simp
  · rw [Real.sign_of_pos ht, abs_of_pos ht, div_self ht.ne']

lemma softAbs_tendsto (t : ℝ) :
    Tendsto (fun m : ℕ => softAbs (1/((m : ℝ)+1)) t) atTop (𝓝 |t|) := by
  have h : Tendsto (fun m : ℕ => t^2 + 1/((m : ℝ)+1)) atTop (𝓝 (t^2+0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  simp only [add_zero] at h
  simpa only [softAbs, Function.comp_def, Real.sqrt_sq_eq_abs] using
    (Real.continuous_sqrt.tendsto (t^2)).comp h

lemma softSign_tendsto (t : ℝ) :
    Tendsto (fun m : ℕ => softSign (1/((m : ℝ)+1)) t) atTop (𝓝 (Real.sign t)) := by
  by_cases ht : t = 0
  · subst t
    simpa only [softSign, zero_div, Real.sign_zero] using tendsto_const_nhds
  · rw [real_sign_eq]
    exact tendsto_const_nhds.div (softAbs_tendsto t) (abs_ne_zero.mpr ht)

lemma softCorrection_tendsto (t : ℝ) :
    Tendsto (fun m : ℕ => t*softSlope (1/((m : ℝ)+1)) t) atTop (𝓝 0) := by
  by_cases ht : t = 0
  · subst t
    simp only [zero_mul]
    exact tendsto_const_nhds
  · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div
      ((softAbs_tendsto t).pow 3) (pow_ne_zero 3 (abs_ne_zero.mpr ht))
    simpa only [softSlope, Pi.div_apply, zero_div, mul_zero] using h.const_mul t

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma casimir_linear {n : ℕ} (w x : Space n) :
    casimir (fun y => ⟪w,y⟫) x = -((n : ℝ)-1)*⟪w,x⟫ := by
  simpa only [id_eq, zero_mul, mul_one, zero_sub, neg_mul] using
    casimir_scalar_inner w x (fun t => hasDerivAt_id t)
      (fun t => hasDerivAt_const t (1 : ℝ))

lemma sphereGradient_linear_inner {n : ℕ} (w : Space n) (x : Sphere n) (v : Space n) :
    ⟪sphereGradient (fun y => ⟪w,y⟫) x,v⟫ = ⟪w,v⟫-⟪w,(x : Space n)⟫*⟪(x : Space n),v⟫ := by
  rw [sphereGradient_inner]
  change (fderiv ℝ (innerSL ℝ w) x) v - (fderiv ℝ (innerSL ℝ w) x) x * _ = _
  rw [(innerSL ℝ w).fderiv]
  rfl

lemma mean_sphereGradient_inner {n : ℕ} [NeZero n] {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (w : Space n) :
    mean (fun x : Sphere n => ⟪sphereGradient f x,w⟫) =
      ((n : ℝ)-1)*mean (fun x : Sphere n => f x*⟪(x : Space n),w⟫) := by
  have h := mean_gradient_casimir hf ((innerSL ℝ w).contDiff (n := 2))
  change mean (fun x : Sphere n => ⟪sphereGradient f x,sphereGradient (fun y => ⟪w,y⟫) x⟫) =
    -mean (fun x : Sphere n => f x*casimir (fun y => ⟪w,y⟫) x) at h
  have hg (x : Sphere n) : ⟪sphereGradient f x,sphereGradient (fun y => ⟪w,y⟫) x⟫ =
      ⟪sphereGradient f x,w⟫ := by
    have ht : ⟪(x : Space n),sphereGradient f x⟫ = 0 := by
      rw [real_inner_comm, sphereGradient_tangent]
    rw [real_inner_comm, sphereGradient_linear_inner, ht, mul_zero, sub_zero, real_inner_comm]
  simp_rw [hg, casimir_linear] at h
  rw [h]
  simp_rw [real_inner_comm w]
  rw [mean, mean, ← integral_const_mul, ← integral_neg]
  congr 1
  funext x
  ring

lemma sphereGradient_product_scalar_inner {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) {ρ ρ' : ℝ → ℝ}
    (hρ : ∀ t, HasDerivAt ρ (ρ' t) t) (v x w : Space n) :
    ⟪sphereGradient (fun y => f y*ρ ⟪v,y⟫) x,w⟫ =
      ρ ⟪v,x⟫*⟪sphereGradient f x,w⟫+
      f x*ρ' ⟪v,x⟫*(⟪v,w⟫-⟪v,x⟫*⟪x,w⟫) := by
  rw [sphereGradient_inner, sphereGradient_inner]
  have hd := (hf.differentiable (by norm_num) x).hasFDerivAt.mul
    ((hρ ⟪v,x⟫).comp_hasFDerivAt x (innerSL ℝ v).hasFDerivAt)
  change HasFDerivAt (fun y => f y*ρ ⟪v,y⟫) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply, comp_apply]
  ring

lemma mean_weighted_gradient {n : ℕ} [NeZero n] {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) {ρ ρ' : ℝ → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hρ' : Continuous ρ') (hd : ∀ t, HasDerivAt ρ (ρ' t) t)
    (v w : Space n) :
    mean (fun x : Sphere n => ρ ⟪v,(x : Space n)⟫*⟪sphereGradient f x,w⟫) =
      ((n : ℝ)-1)*mean (fun x : Sphere n => ρ ⟪v,(x : Space n)⟫*f x*⟪(x : Space n),w⟫) -
      mean (fun x : Sphere n => f x*ρ' ⟪v,(x : Space n)⟫*
        (⟪v,w⟫-⟪v,(x : Space n)⟫*⟪(x : Space n),w⟫)) := by
  have h := mean_sphereGradient_inner (hf.mul (hρ.comp (innerSL ℝ v).contDiff)) w
  change mean (fun x : Sphere n => ⟪sphereGradient (fun y => f y*ρ ⟪v,y⟫) x,w⟫) =
    ((n : ℝ)-1)*mean (fun x : Sphere n => (f x*ρ ⟪v,(x : Space n)⟫)*⟪(x : Space n),w⟫) at h
  simp_rw [sphereGradient_product_scalar_inner hf hd] at h
  have h₁ : Continuous (fun x : Sphere n => ρ ⟪v,(x : Space n)⟫*⟪sphereGradient f x,w⟫) :=
    (hρ.continuous.comp (continuous_const.inner continuous_subtype_val)).mul
      (((sphereGradient_continuous hf).comp continuous_subtype_val).inner continuous_const)
  have h₂ : Continuous (fun x : Sphere n => f x*ρ' ⟪v,(x : Space n)⟫*
      (⟪v,w⟫-⟪v,(x : Space n)⟫*⟪(x : Space n),w⟫)) := by fun_prop
  rw [mean, integral_add (continuous_integrable h₁) (continuous_integrable h₂)] at h
  change mean _ + mean _ = _ at h
  have he : (fun x : Sphere n => (f x*ρ ⟪v,(x : Space n)⟫)*⟪(x : Space n),w⟫) =
      (fun x : Sphere n => ρ ⟪v,(x : Space n)⟫*f x*⟪(x : Space n),w⟫) := by
    funext x; ring
  rw [he] at h
  linarith

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma sign_measurable : Measurable Real.sign := by
  have he : Real.sign = fun t : ℝ => t/|t| := funext real_sign_eq
  rw [he]
  exact measurable_id.div measurable_id.abs

lemma abs_sign_le (t : ℝ) : |Real.sign t| ≤ 1 := by
  rw [real_sign_eq, abs_div, abs_abs]
  by_cases ht : t = 0
  · simp [ht]
  · rw [div_self (abs_ne_zero.mpr ht)]

lemma sign_mul_self (t : ℝ) : Real.sign t*t = |t| := by
  rw [real_sign_eq]
  by_cases ht : t = 0
  · simp [ht]
  · field_simp [abs_ne_zero.mpr ht]
    exact (sq_abs t).symm

lemma sign_weight_integrable {n : ℕ} [NeZero n] (t f : Sphere n → ℝ)
    (ht : Continuous t) (hf : Continuous f) :
    Integrable (fun x => Real.sign (t x)*f x) (sigma n) := by
  apply (continuous_integrable hf).bdd_mul (sign_measurable.comp ht.measurable).aestronglyMeasurable
  filter_upwards with x
  exact abs_sign_le (t x)

lemma mean_softSign_tendsto {n : ℕ} [NeZero n] (t f : Sphere n → ℝ)
    (ht : Continuous t) (hf : Continuous f) :
    Tendsto (fun m : ℕ => mean (fun x => softSign (1/((m : ℝ)+1)) (t x)*f x)) atTop
      (𝓝 (mean (fun x => Real.sign (t x)*f x))) := by
  apply tendsto_integral_of_dominated_convergence (fun x => |f x|)
  · intro m
    exact (((softSign_contDiff (by positivity : 0 < 1/((m : ℝ)+1))).continuous.comp ht).mul hf).aestronglyMeasurable
  · exact continuous_integrable hf.abs
  · intro m
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (abs_softSign_le (by positivity : 0 < 1/((m : ℝ)+1)) (t x)) (abs_nonneg (f x))
  · filter_upwards with x
    exact (softSign_tendsto (t x)).mul_const (f x)

lemma mean_softCorrection_tendsto {n : ℕ} [NeZero n] (t f : Sphere n → ℝ)
    (ht : Continuous t) (hf : Continuous f) :
    Tendsto (fun m : ℕ => mean (fun x => (t x*softSlope (1/((m : ℝ)+1)) (t x))*f x)) atTop
      (𝓝 0) := by
  have h : Tendsto (fun m : ℕ => mean (fun x => (t x*softSlope (1/((m : ℝ)+1)) (t x))*f x)) atTop
      (𝓝 (mean (fun _ : Sphere n => 0))) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |f x|)
    · intro m
      have hc : Continuous (softSlope (1/((m : ℝ)+1))) :=
        continuous_const.div ((softAbs_contDiff (by positivity)).continuous.pow 3)
          (fun y => pow_ne_zero _ (softAbs_pos (by positivity) y).ne')
      exact ((ht.mul (hc.comp ht)).mul hf).aestronglyMeasurable
    · exact continuous_integrable hf.abs
    · intro m
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (abs_softCorrection_le (by positivity : 0 < 1/((m : ℝ)+1)) (t x)) (abs_nonneg (f x))
    · filter_upwards with x
      simpa only [zero_mul] using (softCorrection_tendsto (t x)).mul_const (f x)
  simpa only [mean, integral_zero] using h

lemma mean_softAbs_tendsto {n : ℕ} [NeZero n] (t f : Sphere n → ℝ)
    (ht : Continuous t) (hf : Continuous f) :
    Tendsto (fun m : ℕ => mean (fun x => softAbs (1/((m : ℝ)+1)) (t x)*f x)) atTop
      (𝓝 (mean (fun x => |t x| *f x))) := by
  apply tendsto_integral_of_dominated_convergence (fun x => (|t x|+1)*|f x|)
  · intro m
    exact (((softAbs_contDiff (by positivity : 0 < 1/((m : ℝ)+1))).continuous.comp ht).mul hf).aestronglyMeasurable
  · exact continuous_integrable ((ht.abs.add continuous_const).mul hf.abs)
  · intro m
    filter_upwards with x
    have hε : Real.sqrt (1/((m : ℝ)+1)) ≤ 1 := by
      apply (Real.sqrt_le_one).mpr
      apply (div_le_one (by positivity : 0 < (m : ℝ)+1)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) m]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (softAbs_pos (by positivity) (t x))]
    exact mul_le_mul_of_nonneg_right ((softAbs_le (by positivity) (t x)).trans (by linarith)) (abs_nonneg (f x))
  · filter_upwards with x
    exact (softAbs_tendsto (t x)).mul_const (f x)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma mean_sign_gradient_tangent {n : ℕ} [NeZero n] {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (v w : Space n) (hvw : ⟪v,w⟫ = 0) :
    mean (fun x : Sphere n => Real.sign ⟪v,(x : Space n)⟫*⟪sphereGradient f x,w⟫) =
      ((n : ℝ)-1)*mean (fun x : Sphere n => Real.sign ⟪v,(x : Space n)⟫*f x*⟪(x : Space n),w⟫) := by
  let t : Sphere n → ℝ := fun x => ⟪v,(x : Space n)⟫
  have ht : Continuous t := continuous_const.inner continuous_subtype_val
  have hF : Continuous (fun x : Sphere n => ⟪sphereGradient f x,w⟫) :=
    ((sphereGradient_continuous hf).comp continuous_subtype_val).inner continuous_const
  have hG : Continuous (fun x : Sphere n => f x*⟪(x : Space n),w⟫) := by fun_prop
  have he (m : ℕ) :
      mean (fun x : Sphere n => softSign (1/((m : ℝ)+1)) (t x)*⟪sphereGradient f x,w⟫) =
      ((n : ℝ)-1)*mean (fun x : Sphere n => softSign (1/((m : ℝ)+1)) (t x)*(f x*⟪(x : Space n),w⟫)) +
        mean (fun x : Sphere n => (t x*softSlope (1/((m : ℝ)+1)) (t x))*(f x*⟪(x : Space n),w⟫)) := by
    have hp : 0 < 1/((m : ℝ)+1) := by positivity
    have hc : Continuous (softSlope (1/((m : ℝ)+1))) :=
      continuous_const.div ((softAbs_contDiff hp).continuous.pow 3)
        (fun y => pow_ne_zero _ (softAbs_pos hp y).ne')
    have h := mean_weighted_gradient hf ((softSign_contDiff hp).of_le (by norm_num)) hc
      (softSign_hasDerivAt hp) v w
    rw [h]
    simp only [hvw, zero_sub]
    rw [mean, mean, mean, mean, sub_eq_add_neg, ← integral_neg]
    congr 1
    · congr 1
      apply integral_congr_ae
      filter_upwards with x
      dsimp [t]; ring
    · apply integral_congr_ae
      filter_upwards with x
      dsimp [t]; ring
  have h₁ := mean_softSign_tendsto t _ ht hF
  have h₂ := ((mean_softSign_tendsto t _ ht hG).const_mul ((n : ℝ)-1)).add
    (mean_softCorrection_tendsto t _ ht hG)
  have heq := tendsto_nhds_unique h₁ (h₂.congr' (Filter.Eventually.of_forall (fun m => (he m).symm)))
  simpa only [add_zero, t, mul_assoc] using heq

lemma sphereGradient_scalar_inner {n : ℕ} {ρ ρ' : ℝ → ℝ}
    (hρ : ∀ t, HasDerivAt ρ (ρ' t) t) (v x w : Space n) :
    ⟪sphereGradient (fun y => ρ ⟪v,y⟫) x,w⟫ =
      ρ' ⟪v,x⟫*(⟪v,w⟫-⟪v,x⟫*⟪x,w⟫) := by
  have hd := (hρ ⟪v,x⟫).comp_hasFDerivAt x (innerSL ℝ v).hasFDerivAt
  change HasFDerivAt (fun y => ρ ⟪v,y⟫) _ x at hd
  rw [sphereGradient_inner, hd.fderiv]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  ring

lemma mean_sign_gradient_radial {n : ℕ} [NeZero n] {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (v : Space n) :
    mean (fun x : Sphere n => Real.sign ⟪v,(x : Space n)⟫*⟪sphereGradient f x,v⟫) =
      -mean (fun x : Sphere n => |⟪v,(x : Space n)⟫| * casimir f x) := by
  let t : Sphere n → ℝ := fun x => ⟪v,(x : Space n)⟫
  have ht : Continuous t := continuous_const.inner continuous_subtype_val
  have hF : Continuous (fun x : Sphere n => ⟪sphereGradient f x,v⟫) :=
    ((sphereGradient_continuous (hf.of_le (by norm_num))).comp continuous_subtype_val).inner continuous_const
  have hG : Continuous (fun x : Sphere n => casimir f x) :=
    by
      unfold casimir
      exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
        continuous_finsetSum _ fun j _ =>
          (continuous_rotDeriv _ (contDiff_rotDeriv _ hf)).comp continuous_subtype_val)
  have he (m : ℕ) :
      mean (fun x : Sphere n => softSign (1/((m : ℝ)+1)) (t x)*⟪sphereGradient f x,v⟫) =
      -mean (fun x : Sphere n => softAbs (1/((m : ℝ)+1)) (t x)*casimir f x) := by
    have hp : 0 < 1/((m : ℝ)+1) := by positivity
    have h := mean_gradient_casimir
      ((show ContDiff ℝ 1 (softAbs (1/((m : ℝ)+1))) from (softAbs_contDiff hp).of_le le_top).comp (innerSL ℝ v).contDiff) hf
    change mean (fun x : Sphere n => ⟪sphereGradient (fun y => softAbs (1/((m : ℝ)+1)) ⟪v,y⟫) x,sphereGradient f x⟫) = _ at h
    have hg (x : Sphere n) :
        ⟪sphereGradient (fun y => softAbs (1/((m : ℝ)+1)) ⟪v,y⟫) x,sphereGradient f x⟫ =
          softSign (1/((m : ℝ)+1)) (t x)*⟪sphereGradient f x,v⟫ := by
      rw [sphereGradient_scalar_inner (softAbs_hasDerivAt hp)]
      have hx : ⟪(x : Space n),sphereGradient f x⟫ = 0 := by rw [real_inner_comm, sphereGradient_tangent]
      rw [hx, mul_zero, sub_zero, real_inner_comm v]
    simp_rw [hg] at h
    exact h
  have h₁ := mean_softSign_tendsto t _ ht hF
  have h₂ := (mean_softAbs_tendsto t _ ht hG).neg
  exact tendsto_nhds_unique h₁ (h₂.congr' (Filter.Eventually.of_forall (fun m => (he m).symm)))

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

def signedPair {n : ℕ} (F G : Sphere n → Space n) : ℝ :=
  ∫ z : Sphere n × Sphere n, Real.sign ⟪(z.1 : Space n),(z.2 : Space n)⟫ *
    ⟪F z.1,G z.2⟫ ∂(sigma n).prod (sigma n)

lemma signedPair_integrable {n : ℕ} [NeZero n] {F G : Sphere n → Space n}
    (hF : Continuous F) (hG : Continuous G) :
    Integrable (fun z : Sphere n × Sphere n => Real.sign ⟪(z.1 : Space n),(z.2 : Space n)⟫ *
      ⟪F z.1,G z.2⟫) ((sigma n).prod (sigma n)) := by
  have hi : Integrable (fun z : Sphere n × Sphere n => ⟪F z.1,G z.2⟫)
      ((sigma n).prod (sigma n)) :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply hi.bdd_mul (sign_measurable.comp (by fun_prop : Continuous
    (fun z : Sphere n × Sphere n => ⟪(z.1 : Space n),(z.2 : Space n)⟫)).measurable).aestronglyMeasurable
  filter_upwards with z
  exact abs_sign_le _

lemma signedPair_eq {n : ℕ} [NeZero n] {F G : Sphere n → Space n}
    (hF : Continuous F) (hG : Continuous G) :
    signedPair F G = mean (fun u => mean (fun v =>
      Real.sign ⟪(u : Space n),(v : Space n)⟫ * ⟪F u,G v⟫)) :=
  integral_prod _ (signedPair_integrable hF hG)

lemma signedPair_eq_swap {n : ℕ} [NeZero n] {F G : Sphere n → Space n}
    (hF : Continuous F) (hG : Continuous G) :
    signedPair F G = mean (fun v => mean (fun u =>
      Real.sign ⟪(u : Space n),(v : Space n)⟫ * ⟪F u,G v⟫)) := by
  rw [signedPair_eq hF hG]
  exact integral_integral_swap (signedPair_integrable hF hG)

lemma signedPair_symm {n : ℕ} [NeZero n] {F G : Sphere n → Space n}
    (hF : Continuous F) (hG : Continuous G) : signedPair F G = signedPair G F := by
  rw [signedPair_eq hF hG, signedPair_eq_swap hG hF]
  congr 1
  funext u
  congr 1
  funext v
  rw [real_inner_comm (u : Space n) (v : Space n), real_inner_comm (F u) (G v)]

lemma signedPair_add_left {n : ℕ} [NeZero n] {F G J : Sphere n → Space n}
    (hF : Continuous F) (hG : Continuous G) (hJ : Continuous J) :
    signedPair (fun u => F u+G u) J = signedPair F J+signedPair G J := by
  unfold signedPair
  simp_rw [inner_add_left, mul_add]
  exact integral_add (signedPair_integrable hF hJ) (signedPair_integrable hG hJ)

lemma signedPair_add_right {n : ℕ} [NeZero n] {F G J : Sphere n → Space n}
    (hF : Continuous F) (hG : Continuous G) (hJ : Continuous J) :
    signedPair F (fun u => G u+J u) = signedPair F G+signedPair F J := by
  unfold signedPair
  simp_rw [inner_add_right, mul_add]
  exact integral_add (signedPair_integrable hF hG) (signedPair_integrable hF hJ)

lemma signedPair_smul_left {n : ℕ} (F G : Sphere n → Space n) (c : ℝ) :
    signedPair (fun u => c • F u) G = c*signedPair F G := by
  unfold signedPair
  simp_rw [real_inner_smul_left, mul_left_comm _ c]
  exact integral_const_mul c _

lemma signedPair_smul_right {n : ℕ} (F G : Sphere n → Space n) (c : ℝ) :
    signedPair F (fun u => c • G u) = c*signedPair F G := by
  unfold signedPair
  simp_rw [real_inner_smul_right, mul_left_comm _ c]
  exact integral_const_mul c _

end PettyProjection.Spherical
end

end OAI
