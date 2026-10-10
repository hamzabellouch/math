import Mathlib

namespace OAI

/-! Degree-two radial extensions and their value and derivative estimates. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.MixedRadial

variable {W Z : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem hasFDerivAt_zero_of_quadratic_bound {P : W → Z} (hzero : P 0 = 0)
    {C : ℝ} (hbound : ∀ w, ‖P w‖ ≤ C * ‖w‖ ^ 2) :
    HasFDerivAt P (0 : W →L[ℝ] Z) 0 := by
  rw [hasFDerivAt_iff_tendsto]
  simp only [sub_zero, hzero, zero_apply]
  have ht : Tendsto (fun w : W => C * ‖w‖) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (continuous_norm.tendsto (0 : W)))
  refine squeeze_zero (fun w => mul_nonneg (inv_nonneg.mpr (norm_nonneg w)) (norm_nonneg _)) ?_ ht
  · intro w
    by_cases hw : w = 0
    · simp [hw, hzero]
    · calc
        ‖w‖⁻¹ * ‖P w‖ ≤ ‖w‖⁻¹ * (C * ‖w‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hbound w) (inv_nonneg.mpr (norm_nonneg w))
        _ = C * ‖w‖ := by field_simp

theorem exists_quadratic_bound [ProperSpace W] {P : W → Z} (hzero : P 0 = 0)
    (hhom : ∀ r : ℝ, 0 < r → ∀ w, P (r • w) = r ^ 2 • P w)
    (hcont : ∀ w ≠ 0, ContinuousAt P w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w, ‖P w‖ ≤ C * ‖w‖ ^ 2 := by
  let S : C(Metric.sphere (0 : W) 1, Z) :=
    ⟨fun u => P u, continuous_iff_continuousAt.mpr (fun u =>
      (hcont u (by
        have hu : ‖(u : W)‖ = 1 := by simp
        exact norm_ne_zero_iff.mp (by rw [hu]; norm_num))).comp
          continuous_subtype_val.continuousAt)⟩
  refine ⟨‖S‖, norm_nonneg _, fun w => ?_⟩
  by_cases hw : w = 0
  · simp [hw, hzero]
  let u : Metric.sphere (0 : W) 1 := ⟨‖w‖⁻¹ • w, by
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]⟩
  have hre : ‖w‖ • (u : W) = w := by simp [u, smul_smul, hw]
  have hrad : P w = ‖w‖ ^ 2 • S u := by
    calc
      P w = P (‖w‖ • (u : W)) := congrArg P hre.symm
      _ = ‖w‖ ^ 2 • S u := hhom _ (norm_pos_iff.mpr hw) u
  rw [hrad, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    ‖w‖ ^ 2 * ‖S u‖ ≤ ‖w‖ ^ 2 * ‖S‖ :=
      mul_le_mul_of_nonneg_left (S.norm_coe_le_norm u) (sq_nonneg _)
    _ = ‖S‖ * ‖w‖ ^ 2 := mul_comm _ _

theorem differentiable_degree_two [ProperSpace W] {P : W → Z} (hzero : P 0 = 0)
    (hhom : ∀ r : ℝ, 0 < r → ∀ w, P (r • w) = r ^ 2 • P w)
    (hdiff : ∀ w ≠ 0, DifferentiableAt ℝ P w) : Differentiable ℝ P := by
  obtain ⟨C, _, hbound⟩ := exists_quadratic_bound hzero hhom
    (fun w hw => (hdiff w hw).continuousAt)
  intro w
  by_cases hw : w = 0
  · subst w
    exact (hasFDerivAt_zero_of_quadratic_bound hzero hbound).differentiableAt
  · exact hdiff w hw

theorem fderiv_smul_degree_two {P : W → Z} (hP : Differentiable ℝ P)
    (hhom : ∀ r : ℝ, 0 < r → ∀ w, P (r • w) = r ^ 2 • P w)
    {r : ℝ} (hr : 0 < r) (w : W) :
    fderiv ℝ P (r • w) = r • fderiv ℝ P w := by
  have h₁ : HasFDerivAt (fun x => P (r • x))
      ((fderiv ℝ P (r • w)).comp (r • ContinuousLinearMap.id ℝ W)) w :=
    (hP (r • w)).hasFDerivAt.comp w
      ((ContinuousLinearMap.id ℝ W).hasFDerivAt.const_smul r)
  have h₂ := (hP w).hasFDerivAt.const_smul (r ^ 2)
  have heq : (fun x => P (r • x)) = (fun x => r ^ 2 • P x) := funext (hhom r hr)
  rw [heq] at h₁
  have hd := h₁.unique h₂
  apply smul_right_injective (M := W →L[ℝ] Z) hr.ne'
  ext v
  have hv := congrArg (fun L : W →L[ℝ] Z => L v) hd
  simpa only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, pow_two, mul_smul] using hv

theorem exists_uniform_derivative_bound {B : Type*} [TopologicalSpace B]
    [CompactSpace B] [ProperSpace W] {P : B → W → Z}
    (hzero : ∀ b, P b 0 = 0)
    (hhom : ∀ b (r : ℝ), 0 < r → ∀ w, P b (r • w) = r ^ 2 • P b w)
    (hdiff : ∀ b w, w ≠ 0 → DifferentiableAt ℝ (P b) w)
    (hD : Continuous (fun p : B × Metric.sphere (0 : W) 1 =>
      fderiv ℝ (P p.1) (p.2 : W))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b, Differentiable ℝ (P b) ∧
      ∀ w, ‖fderiv ℝ (P b) w‖ ≤ C * ‖w‖ := by
  let S : C(B × Metric.sphere (0 : W) 1, W →L[ℝ] Z) := ⟨_, hD⟩
  refine ⟨‖S‖, norm_nonneg S, fun b => ?_⟩
  have hP := differentiable_degree_two (hzero b) (hhom b) (hdiff b)
  refine ⟨hP, fun w => ?_⟩
  by_cases hw : w = 0
  · obtain ⟨A, _, hA⟩ := exists_quadratic_bound (hzero b) (hhom b)
      (fun w hw => (hdiff b w hw).continuousAt)
    have hh := (hasFDerivAt_zero_of_quadratic_bound (hzero b) hA).fderiv
    simp [hw, hh]
  let u : Metric.sphere (0 : W) 1 := ⟨‖w‖⁻¹ • w, by
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]⟩
  have hre : ‖w‖ • (u : W) = w := by simp [u, smul_smul, hw]
  have hrad : fderiv ℝ (P b) w = ‖w‖ • S (b, u) := by
    calc
      fderiv ℝ (P b) w = fderiv ℝ (P b) (‖w‖ • (u : W)) :=
        congrArg (fderiv ℝ (P b)) hre.symm
      _ = ‖w‖ • S (b, u) := fderiv_smul_degree_two hP (hhom b) (norm_pos_iff.mpr hw) u
  rw [hrad, norm_smul, Real.norm_eq_abs, abs_norm]
  calc
    ‖w‖ * ‖S (b, u)‖ ≤ ‖w‖ * ‖S‖ :=
      mul_le_mul_of_nonneg_left (S.norm_coe_le_norm _) (norm_nonneg w)
    _ = ‖S‖ * ‖w‖ := mul_comm _ _

end NearbyLagrangian.MixedRadial

namespace NearbyLagrangian.AngularExtension

open scoped Topology ContDiff
open Filter Set ContinuousLinearMap

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma contDiff_one_degree_two [ProperSpace E] {P : E → Z} (h0 : P 0 = 0)
    (hh : ∀ r : ℝ, 0 < r → ∀ x, P (r • x) = r^2 • P x)
    (hs : ∀ x ≠ 0, ContDiffAt ℝ 1 P x) : ContDiff ℝ 1 P := by
  have hd := MixedRadial.differentiable_degree_two h0 hh
    (fun x hx => (hs x hx).differentiableAt one_ne_zero)
  have hc : Continuous (fun u : Metric.sphere (0 : E) 1 => fderiv ℝ P (u : E)) := by
    rw [continuous_iff_continuousAt]
    intro u
    have hu : (u : E) ≠ 0 := by
      have hn : ‖(u : E)‖ = 1 := by simp
      exact norm_ne_zero_iff.mp (by rw [hn]; norm_num)
    exact ((hs u hu).continuousAt_fderiv one_ne_zero).comp continuous_subtype_val.continuousAt
  have hp : Continuous (fun p : Unit × Metric.sphere (0 : E) 1 => fderiv ℝ P (p.2 : E)) :=
    hc.comp continuous_snd
  obtain ⟨C, _, hC⟩ := MixedRadial.exists_uniform_derivative_bound
    (P := fun _ : Unit => P) (fun _ => h0) (fun _ => hh)
    (fun _ x hx => (hs x hx).differentiableAt one_ne_zero) hp
  obtain ⟨A, _, hA⟩ := MixedRadial.exists_quadratic_bound h0 hh
    (fun x hx => (hs x hx).continuousAt)
  have hd0 := (MixedRadial.hasFDerivAt_zero_of_quadratic_bound h0 hA).fderiv
  apply contDiff_one_iff_fderiv.mpr
  refine ⟨hd, continuous_iff_continuousAt.mpr (fun x => ?_)⟩
  by_cases hx : x = 0
  · subst x
    rw [ContinuousAt, hd0]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (fun x => norm_nonneg _) (fun x => (hC ()).2 x) ?_
    simpa using tendsto_const_nhds.mul (continuous_norm.tendsto (0 : E))
  · exact (hs x hx).continuousAt_fderiv one_ne_zero

end NearbyLagrangian.AngularExtension

namespace NearbyLagrangian.AngularExtension

open scoped Topology ContDiff
open Filter Set ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialize (f : E → ℝ) (x : E) : ℝ := ‖x‖^2 * f (NormedSpace.normalize x)

@[simp] lemma radialize_zero (f : E → ℝ) : radialize f 0 = 0 := by simp [radialize]

lemma radialize_homogeneous (f : E → ℝ) {r : ℝ} (hr : 0 < r) (x : E) :
    radialize f (r • x) = r^2 * radialize f x := by
  simp only [radialize, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    NormedSpace.normalize_smul_of_pos hr, mul_pow]
  ring

lemma radialize_on_unit (f : E → ℝ) {x : E} (hx : ‖x‖ = 1) : radialize f x = f x := by
  simp [radialize, hx, NormedSpace.normalize_eq_self_of_norm_eq_one hx]

lemma contDiffAt_normalize {x : E} (hx : x ≠ 0) {n : ℕ∞ω} :
    ContDiffAt ℝ n (NormedSpace.normalize : E → E) x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

lemma contDiffAt_radialize {f : E → ℝ} {x : E} (hx : x ≠ 0) {n : ℕ∞ω}
    (hf : ContDiffAt ℝ n f (NormedSpace.normalize x)) :
    ContDiffAt ℝ n (radialize f) x :=
  (contDiffAt_id.norm_sq ℝ).mul (hf.comp x (contDiffAt_normalize hx))

lemma contDiff_one_radialize [ProperSpace E] {f : E → ℝ}
    (hf : ∀ x, ‖x‖ = 1 → ContDiffAt ℝ 1 f x) : ContDiff ℝ 1 (radialize f) := by
  apply contDiff_one_degree_two (radialize_zero f)
    (fun r hr x => radialize_homogeneous f hr x)
  intro x hx
  exact contDiffAt_radialize hx (hf _ (NormedSpace.norm_normalize hx))

end NearbyLagrangian.AngularExtension

namespace NearbyLagrangian.AngularExtension

open scoped Topology ContDiff InnerProductSpace
open Filter Set ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasFDerivAt_normalize_unit {x : E} (hx : ‖x‖ = 1) :
    HasFDerivAt (NormedSpace.normalize : E → E)
      (ContinuousLinearMap.id ℝ E - (fderiv ℝ (norm : E → ℝ) x).smulRight x) x := by
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by rw [hx]; norm_num)
  have hn : DifferentiableAt ℝ (norm : E → ℝ) x :=
    (contDiffAt_norm ℝ hx0).differentiableAt (by simp : (1 : ℕ∞ω) ≠ 0)
  have hi := (hasDerivAt_inv (norm_ne_zero_iff.mpr hx0)).comp_hasFDerivAt x hn.hasFDerivAt
  have h := hi.smul (hasFDerivAt_id x)
  convert! h using 1
  · ext y
    simp only [sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, add_apply,
      smul_apply, hx]
    simp [hx, sub_eq_add_neg]

lemma norm_fderiv_normalize_unit_le {x : E} (hx : ‖x‖ = 1) :
    ‖fderiv ℝ (NormedSpace.normalize : E → E) x‖ ≤ 2 := by
  rw [(hasFDerivAt_normalize_unit hx).fderiv]
  refine (ContinuousLinearMap.id ℝ E -
    (fderiv ℝ (norm : E → ℝ) x).smulRight x).opNorm_le_bound (by norm_num) ?_
  intro y
  have hn : ‖fderiv ℝ (norm : E → ℝ) x‖ ≤ 1 :=
    by simpa using (norm_fderiv_le_of_lipschitz ℝ
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : E → ℝ)) (x₀ := x))
  calc
    ‖(ContinuousLinearMap.id ℝ E - (fderiv ℝ (norm : E → ℝ) x).smulRight x) y‖
        ≤ ‖y‖ + ‖(fderiv ℝ (norm : E → ℝ) x) y • x‖ := norm_sub_le _ _
    _ ≤ ‖y‖ + ‖y‖ := by
      rw [norm_smul, hx, mul_one]
      gcongr
      exact (le_opNorm _ _).trans (by simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg y))
    _ = 2 * ‖y‖ := by ring

lemma fderiv_radialize_unit {f : E → ℝ} {x : E} (hx : ‖x‖ = 1)
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (radialize f) x =
      (2 * f x) • innerSL ℝ x +
        (fderiv ℝ f x).comp (fderiv ℝ (NormedSpace.normalize : E → E) x) := by
  have he : NormedSpace.normalize x = x := NormedSpace.normalize_eq_self_of_norm_eq_one hx
  have hn := hasFDerivAt_normalize_unit hx
  have hf' : HasFDerivAt f (fderiv ℝ f x) (NormedSpace.normalize x) := by
    simpa only [he] using hf.hasFDerivAt
  have hd := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).mul (hf'.comp x hn)
  change HasFDerivAt (radialize f) _ x at hd
  rw [hd.fderiv, hn.fderiv]
  ext y
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    Function.comp_apply, hx, he, one_pow, one_smul, smul_eq_mul]
  ring

lemma radialize_eq_of_degree_two {f : E → ℝ} (h0 : f 0 = 0)
    (hh : ∀ r : ℝ, 0 < r → ∀ x, f (r • x) = r^2 * f x) : radialize f = f := by
  funext x
  by_cases hx : x = 0
  · simp [hx, h0]
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    rw [radialize, ← hh ‖x‖ hn (NormedSpace.normalize x)]
    rw [NormedSpace.norm_smul_normalize]

lemma norm_fderiv_radialize_sub_le {f g : E → ℝ} {x : E} (hx : ‖x‖ = 1)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (radialize g) x - fderiv ℝ (radialize f) x‖ ≤
      2 * ‖g x - f x‖ + 2 * ‖fderiv ℝ g x - fderiv ℝ f x‖ := by
  rw [fderiv_radialize_unit hx hg, fderiv_radialize_unit hx hf]
  have he : (2 * g x) • innerSL ℝ x +
        (fderiv ℝ g x).comp (fderiv ℝ (NormedSpace.normalize : E → E) x) -
        ((2 * f x) • innerSL ℝ x +
        (fderiv ℝ f x).comp (fderiv ℝ (NormedSpace.normalize : E → E) x)) =
      (2 * (g x - f x)) • innerSL ℝ x +
        (fderiv ℝ g x - fderiv ℝ f x).comp
          (fderiv ℝ (NormedSpace.normalize : E → E) x) := by
    ext y
    simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul]
    ring
  rw [he]
  calc
    _ ≤ ‖(2 * (g x - f x)) • innerSL ℝ x‖ +
        ‖(fderiv ℝ g x - fderiv ℝ f x).comp
          (fderiv ℝ (NormedSpace.normalize : E → E) x)‖ := norm_add_le _ _
    _ ≤ 2 * ‖g x - f x‖ + 2 * ‖fderiv ℝ g x - fderiv ℝ f x‖ := by
      rw [norm_smul, norm_mul, innerSL_apply_norm, hx, mul_one, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      gcongr
      calc
        _ ≤ ‖fderiv ℝ g x - fderiv ℝ f x‖ *
            ‖fderiv ℝ (NormedSpace.normalize : E → E) x‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖fderiv ℝ g x - fderiv ℝ f x‖ * 2 := by
          gcongr
          exact norm_fderiv_normalize_unit_le hx
        _ = _ := mul_comm _ _

end NearbyLagrangian.AngularExtension

end

end OAI
