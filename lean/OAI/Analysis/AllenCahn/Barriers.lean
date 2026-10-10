import OAI.Analysis.AllenCahn.LogGradient

namespace OAI

noncomputable section
namespace DeGiorgi
open scoped ContDiff
open Filter Topology

lemma laplacian_exp {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) (x : Space n) :
    Laplacian.laplacian (fun z => Real.exp (f z)) x =
      Real.exp (f x) * (‖gradient f x‖ ^ 2 + Laplacian.laplacian f x) := by
  rw [laplacian_comp_scalar hf hf.exp (fun _ => Real.differentiable_exp.differentiableAt)
    (fun _ => by simpa only [Real.deriv_exp] using Real.differentiable_exp.differentiableAt)]
  simp only [Real.deriv_exp]
  ring

def smoothRadius {n : ℕ} (x : Space n) : ℝ := Real.sqrt (1 + ‖x‖ ^ 2)

lemma smoothRadius_pos {n : ℕ} (x : Space n) : 0 < smoothRadius x := by
  dsimp [smoothRadius]; positivity

lemma smoothRadius_sq {n : ℕ} (x : Space n) : smoothRadius x ^ 2 = 1 + ‖x‖ ^ 2 := by
  exact Real.sq_sqrt (by positivity)

lemma norm_le_smoothRadius {n : ℕ} (x : Space n) : ‖x‖ ≤ smoothRadius x := by
  nlinarith [smoothRadius_sq x, smoothRadius_pos x, norm_nonneg x]

lemma smoothRadius_le_norm_add_one {n : ℕ} (x : Space n) : smoothRadius x ≤ ‖x‖ + 1 := by
  nlinarith [smoothRadius_sq x, smoothRadius_pos x, norm_nonneg x]

lemma smoothRadius_smooth (n : ℕ) : ContDiff ℝ ∞ (@smoothRadius n) := by
  exact (contDiff_const.add (contDiff_id.norm_sq ℝ)).sqrt (fun x => by positivity)

lemma fderiv_smoothRadius {n : ℕ} (x : Space n) :
    fderiv ℝ (@smoothRadius n) x = (smoothRadius x)⁻¹ • innerSL ℝ x := by
  have h1 : HasFDerivAt (fun z : Space n => 1 + ‖z‖ ^ 2)
      ((2 : ℝ) • innerSL ℝ x) x := by
    simpa only [← Nat.cast_smul_eq_nsmul ℝ 2, Nat.cast_ofNat] using
      ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add (1 : ℝ))
  have h2 := (Real.hasDerivAt_sqrt (show 1 + ‖x‖ ^ 2 ≠ 0 by positivity)).comp_hasFDerivAt x h1
  have h2e : fderiv ℝ (@smoothRadius n) x =
      (1 / (2 * Real.sqrt (1 + ‖x‖ ^ 2))) • ((2 : ℝ) • innerSL ℝ x) := h2.fderiv
  rw [h2e]
  dsimp only [smoothRadius]
  rw [smul_smul]
  congr 1
  field_simp

lemma gradient_smoothRadius {n : ℕ} (x : Space n) :
    gradient (@smoothRadius n) x = (smoothRadius x)⁻¹ • x := by
  rw [gradient, fderiv_smoothRadius, map_smul]
  congr 1
  exact (InnerProductSpace.toDual ℝ (Space n)).symm_apply_apply x

lemma laplacian_smoothRadius {n : ℕ} (x : Space n) :
    Laplacian.laplacian (@smoothRadius n) x = n / smoothRadius x - ‖x‖ ^ 2 / smoothRadius x ^ 3 := by
  have hs : ContDiff ℝ 2 (@smoothRadius n) := smooth_C2 (smoothRadius_smooth n)
  have hfirst (i : Fin n) : coordDeriv (@smoothRadius n) i =
      fun z => (smoothRadius z)⁻¹ * inner ℝ z (basis n i) := by
    funext z
    simp only [coordDeriv, fderiv_smoothRadius, smul_apply,
      smul_eq_mul, innerSL_apply_apply]
  rw [laplacian_eq_sum_coordDeriv hs]
  simp_rw [hfirst]
  have hie (i : Fin n) : (fun z : Space n => inner ℝ z (basis n i)) = (innerSL ℝ (basis n i)) := by
    funext z
    exact real_inner_comm _ _
  have hi (i : Fin n) : Differentiable ℝ (fun z : Space n => inner ℝ z (basis n i)) := by
    rw [hie]
    exact (innerSL ℝ (basis n i)).differentiable
  have hinv : Differentiable ℝ (fun z : Space n => (smoothRadius z)⁻¹) :=
    hs.differentiable (by norm_num) |>.inv (fun z => (smoothRadius_pos z).ne')
  have he (i : Fin n) : coordDeriv (fun z => (smoothRadius z)⁻¹ * inner ℝ z (basis n i)) i x =
      (smoothRadius x)⁻¹ - (smoothRadius x)⁻¹ ^ 3 * inner ℝ x (basis n i) ^ 2 := by
    rw [coordDeriv_mul hinv (hi i)]
    have hd : coordDeriv (fun z : Space n => inner ℝ z (basis n i)) i x = 1 := by
      have H : HasFDerivAt (fun z : Space n => inner ℝ z (basis n i))
          (innerSL ℝ (basis n i)) x := by
        rw [hie]
        exact (innerSL ℝ (basis n i)).hasFDerivAt (x := x)
      simp only [coordDeriv, H.fderiv, innerSL_apply_apply]
      simp only [real_inner_self_eq_norm_sq, (basis n).orthonormal.1 i, one_pow]
    have hd2 : coordDeriv (fun z : Space n => (smoothRadius z)⁻¹) i x =
        -(smoothRadius x)⁻¹ ^ 3 * inner ℝ x (basis n i) := by
      have hd3 := (hasDerivAt_inv (smoothRadius_pos x).ne').comp_hasFDerivAt x
        ((hs.differentiable (by norm_num) x).hasFDerivAt)
      have hd3e : fderiv ℝ (fun z : Space n => (smoothRadius z)⁻¹) x =
          (-(smoothRadius x ^ 2)⁻¹) • fderiv ℝ (@smoothRadius n) x := hd3.fderiv
      simp only [coordDeriv, hd3e, smul_apply, smul_eq_mul,
        fderiv_smoothRadius, innerSL_apply_apply]
      field_simp
    rw [hd, hd2]; ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  have hb : ∑ i : Fin n, inner ℝ x (basis n i) ^ 2 = ‖x‖ ^ 2 := by
    simpa only [real_inner_comm] using (basis n).sum_sq_inner_right x
  rw [hb]
  field_simp

lemma exterior_comparison {n : ℕ} {f g : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (b : Space n → Space n) (c : Space n → ℝ) (R : ℝ)
    (hc : ∀ x, 0 ≤ c x) (hg0 : ∀ x, 0 ≤ g x)
    (hdecay : Tendsto f (Bornology.cobounded (Space n)) (𝓝 0))
    (hinner : ∀ x, ‖x‖ ≤ R → f x ≤ g x)
    (hsub : ∀ x, R < ‖x‖ →
      -Laplacian.laplacian f x + fderiv ℝ f x (b x) + c x * f x < 0)
    (hsuper : ∀ x, 0 ≤ -Laplacian.laplacian g x + fderiv ℝ g x (b x) + c x * g x) :
    ∀ x, f x ≤ g x := by
  intro x₀
  by_contra! hbad
  let H := fun x => f x - g x
  have hp : 0 < H x₀ := sub_pos.mpr hbad
  have hevent : ∀ᶠ x in Bornology.cobounded (Space n), H x ≤ H x₀ := by
    have hh := hdecay.eventually (gt_mem_nhds hp)
    filter_upwards [hh] with x hx
    dsimp [H] at hx ⊢
    linarith [hg0 x]
  obtain ⟨x, hx⟩ := (hf.continuous.sub hg.continuous).exists_forall_ge' x₀
    (by simpa only [Metric.cobounded_eq_cocompact, H, Pi.sub_apply] using hevent)
  have hpos : 0 < f x - g x := hp.trans_le (hx x₀)
  have hr : R < ‖x‖ := by
    by_contra! hn
    linarith [hinner x hn]
  have hmax : IsLocalMax H x := Filter.Eventually.of_forall hx
  have hH : ContDiff ℝ 2 H := hf.sub hg
  have hl := laplacian_nonpos_of_local_max hH hmax
  have hz := hmax.hasFDerivAt_eq_zero (hH.differentiable (by norm_num) x).hasFDerivAt
  have hze := congrArg (fun L : Space n →L[ℝ] ℝ => L (b x)) hz
  dsimp only [H] at hl hze
  rw [laplacian_fun_sub hf hg] at hl
  rw [fderiv_fun_sub (hf.differentiable (by norm_num) x)
    (hg.differentiable (by norm_num) x)] at hze
  simp only [sub_apply, zero_apply] at hze
  have hn := mul_nonneg (hc x) hpos.le
  have hsf := hsub x hr
  have hsg := hsuper x
  nlinarith

def radialBarrier {n : ℕ} (κ : ℝ) (x : Space n) : ℝ :=
  Real.exp (-κ * smoothRadius x)

lemma radialBarrier_pos {n : ℕ} (κ : ℝ) (x : Space n) : 0 < radialBarrier κ x := Real.exp_pos _

lemma radialBarrier_smooth (n : ℕ) (κ : ℝ) : ContDiff ℝ ∞ (@radialBarrier n κ) :=
  (contDiff_const.mul (smoothRadius_smooth n)).exp

lemma radialBarrier_decay {n : ℕ} {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (@radialBarrier n κ) (Bornology.cobounded (Space n)) (𝓝 0) := by
  have hr : Tendsto (@smoothRadius n) (Bornology.cobounded (Space n)) atTop :=
    tendsto_atTop_mono (fun x => norm_le_smoothRadius x) tendsto_norm_cobounded_atTop
  have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hr.const_mul_atTop hκ)
  change Tendsto (fun x : Space n => Real.exp (-κ * smoothRadius x)) _ _
  simpa only [Function.comp_def, neg_mul] using hh

lemma fderiv_radialBarrier {n : ℕ} (κ : ℝ) (x : Space n) :
    fderiv ℝ (@radialBarrier n κ) x =
      (-κ * radialBarrier κ x / smoothRadius x) • innerSL ℝ x := by
  change fderiv ℝ (fun z : Space n => Real.exp (-κ * smoothRadius z)) x = _
  rw [fderiv_exp ((smoothRadius_smooth n).differentiable (by simp) x |>.const_mul (-κ)),
    fderiv_const_mul ((smoothRadius_smooth n).differentiable (by simp) x), fderiv_smoothRadius,
    smul_smul, smul_smul]
  congr 1
  dsimp [radialBarrier]
  ring

lemma laplacian_radialBarrier {n : ℕ} (κ : ℝ) (x : Space n) :
    Laplacian.laplacian (@radialBarrier n κ) x = radialBarrier κ x *
      (κ ^ 2 * ‖x‖ ^ 2 / smoothRadius x ^ 2 - κ * n / smoothRadius x +
        κ * ‖x‖ ^ 2 / smoothRadius x ^ 3) := by
  have hs := smooth_C2 (smoothRadius_smooth n)
  change Laplacian.laplacian (fun z : Space n => Real.exp (-κ * smoothRadius z)) x = _
  rw [laplacian_exp (contDiff_const.mul hs), laplacian_fun_const_mul hs,
    laplacian_smoothRadius]
  have hh : gradient (fun z : Space n => -κ * smoothRadius z) x =
      (-κ / smoothRadius x) • x := by
    rw [gradient, fderiv_const_mul (hs.differentiable (by norm_num) x), map_smul]
    change -κ • gradient (@smoothRadius n) x = _
    rw [gradient_smoothRadius, smul_smul]
    congr 1
  rw [hh, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  dsimp [radialBarrier]
  congr 1
  ring

lemma defectPotential_nonneg {n : ℕ} {v : Space n → ℝ}
    (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (x : Space n) :
    0 ≤ defectPotential v x := by
  dsimp [defectPotential, diffuseDefect, defectWeight]
  have hq := weight_pos (hi x)
  nlinarith [sq_nonneg ‖gradient (inverseProfile v) x‖]

lemma defectPotential_le {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hAC : AllenCahn v) (x : Space n) :
    defectPotential v x ≤ 2 * (1 - v x ^ 2) := by
  have hD := diffuseDefect_nonneg hv hi hAC x
  have hq := weight_pos (hi x)
  dsimp [defectPotential, defectWeight]
  nlinarith [mul_nonneg hq.le hD]

lemma diffuseDrift_bound_refined {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hAC : AllenCahn v) (x : Space n) :
    ‖diffuseDrift v x‖ ≤ 2 * Real.sqrt 2 * |v x| := by
  rw [diffuseDrift, norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt 2)]
  exact mul_le_of_le_one_right (by positivity) (inverseProfile_gradient_bound hv hi hAC x)

lemma sharp_potential_drift_bound {t κ : ℝ} (ht : |t| ≤ 1) (hκ : 2 * Real.sqrt 2 < κ) :
    2 * Real.sqrt 2 * κ * |t| + 2 * (1 - t ^ 2) ≤ 2 * Real.sqrt 2 * κ := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  have ha : 4 ≤ 2 * Real.sqrt 2 * κ := by
    nlinarith
  have HH := mul_nonneg (show 0 ≤ 1 - |t| by linarith)
    (show 0 ≤ 2 * Real.sqrt 2 * κ - 2 * (1 + |t|) by linarith)
  nlinarith [sq_abs t]

lemma radialBarrier_fderiv_bound {n : ℕ} {κ : ℝ} (hκ : 0 < κ) (x : Space n) :
    ‖fderiv ℝ (@radialBarrier n κ) x‖ ≤ κ * radialBarrier κ x := by
  rw [fderiv_radialBarrier, norm_smul, Real.norm_eq_abs, abs_div, abs_mul, abs_neg,
    abs_of_pos hκ, abs_of_pos (radialBarrier_pos κ x), abs_of_pos (smoothRadius_pos x),
    innerSL_apply_norm]
  calc κ * radialBarrier κ x / smoothRadius x * ‖x‖ =
      (κ * radialBarrier κ x) * (‖x‖ / smoothRadius x) := by ring
    _ ≤ κ * radialBarrier κ x := mul_le_of_le_one_right (mul_nonneg hκ.le (radialBarrier_pos κ x).le)
      ((div_le_one (smoothRadius_pos x)).mpr (norm_le_smoothRadius x))

def sharpDefectRadius (n : ℕ) (κ : ℝ) : ℝ :=
  1 + (κ ^ 2 + κ * n) / (κ ^ 2 - 2 * Real.sqrt 2 * κ)

lemma sharpDefect_gap_pos {κ : ℝ} (hκ : 2 * Real.sqrt 2 < κ) :
    0 < κ ^ 2 - 2 * Real.sqrt 2 * κ := by
  have hk : 0 < κ := lt_trans (by positivity) hκ
  nlinarith [mul_pos hk (sub_pos.mpr hκ)]

lemma sharpDefectRadius_pos (n : ℕ) {κ : ℝ} (hκ : 2 * Real.sqrt 2 < κ) :
    0 < sharpDefectRadius n κ := by
  have hgap := sharpDefect_gap_pos hκ
  have hk : 0 < κ := lt_trans (by positivity) hκ
  dsimp [sharpDefectRadius]
  positivity

lemma radialBarrier_laplacian_strict {n : ℕ} {κ : ℝ}
    (hκ : 2 * Real.sqrt 2 < κ) (x : Space n) (hx : sharpDefectRadius n κ < ‖x‖) :
    (2 * Real.sqrt 2 * κ) * radialBarrier κ x < Laplacian.laplacian (@radialBarrier n κ) x := by
  have hk : 0 < κ := lt_trans (by positivity) hκ
  have hgap := sharpDefect_gap_pos hκ
  have hr := smoothRadius_pos x
  have hr1 : 1 ≤ smoothRadius x := by nlinarith [smoothRadius_sq x, sq_nonneg ‖x‖]
  have hr2 : (κ ^ 2 + κ * n) / (κ ^ 2 - 2 * Real.sqrt 2 * κ) < smoothRadius x := by
    have H := norm_le_smoothRadius x
    dsimp [sharpDefectRadius] at hx
    linarith
  have hh : (κ ^ 2 + κ * n) / smoothRadius x < κ ^ 2 - 2 * Real.sqrt 2 * κ := by
    apply (div_lt_iff₀ hr).mpr
    have HH := (div_lt_iff₀ hgap).mp hr2
    nlinarith
  have hsmall : κ ^ 2 / smoothRadius x ^ 2 ≤ κ ^ 2 / smoothRadius x := by
    apply div_le_div_of_nonneg_left (sq_nonneg κ) hr
    nlinarith
  have hlast : 0 ≤ κ * ‖x‖ ^ 2 / smoothRadius x ^ 3 := by positivity
  have he : κ ^ 2 * ‖x‖ ^ 2 / smoothRadius x ^ 2 - κ * n / smoothRadius x +
        κ * ‖x‖ ^ 2 / smoothRadius x ^ 3 =
      κ ^ 2 - κ ^ 2 / smoothRadius x ^ 2 - κ * n / smoothRadius x +
        κ * ‖x‖ ^ 2 / smoothRadius x ^ 3 := by
    have hs := smoothRadius_sq x
    have hs' : ‖x‖ ^ 2 = smoothRadius x ^ 2 - 1 := by linarith
    rw [hs']
    field_simp
  have hcore : 2 * Real.sqrt 2 * κ <
      κ ^ 2 * ‖x‖ ^ 2 / smoothRadius x ^ 2 - κ * n / smoothRadius x +
        κ * ‖x‖ ^ 2 / smoothRadius x ^ 3 := by
    rw [he]
    rw [add_div] at hh
    linarith
  rw [laplacian_radialBarrier]
  calc (2 * Real.sqrt 2 * κ) * radialBarrier κ x = radialBarrier κ x * (2 * Real.sqrt 2 * κ) := by ring
    _ < _ := mul_lt_mul_of_pos_left hcore (radialBarrier_pos κ x)

lemma radialBarrier_defect_subsolution {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hAC : AllenCahn v) {κ : ℝ} (hκ : 2 * Real.sqrt 2 < κ) (y x : Space n)
    (hx : sharpDefectRadius n κ < ‖x‖) :
    -Laplacian.laplacian (@radialBarrier n κ) x +
      fderiv ℝ (@radialBarrier n κ) x (diffuseDrift v (y + x)) +
      defectPotential v (y + x) * radialBarrier κ x < 0 := by
  have hk : 0 < κ := lt_trans (by positivity) hκ
  have hb := radialBarrier_pos κ x
  have hd : fderiv ℝ (@radialBarrier n κ) x (diffuseDrift v (y + x)) ≤
      radialBarrier κ x * (2 * Real.sqrt 2 * κ * |v (y + x)|) := by
    calc fderiv ℝ (@radialBarrier n κ) x (diffuseDrift v (y + x)) ≤
        ‖fderiv ℝ (@radialBarrier n κ) x (diffuseDrift v (y + x))‖ := Real.le_norm_self _
      _ ≤ ‖fderiv ℝ (@radialBarrier n κ) x‖ * ‖diffuseDrift v (y + x)‖ :=
        (fderiv ℝ (@radialBarrier n κ) x).le_opNorm _
      _ ≤ (κ * radialBarrier κ x) * (2 * Real.sqrt 2 * |v (y + x)|) :=
        mul_le_mul (radialBarrier_fderiv_bound hk x) (diffuseDrift_bound_refined hv hi hAC (y + x))
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hc := mul_le_mul_of_nonneg_right (defectPotential_le hv hi hAC (y + x)) hb.le
  have ht : |v (y + x)| ≤ 1 := abs_le.mpr ⟨(hi (y+x)).1.le, (hi (y+x)).2.le⟩
  have hs := mul_le_mul_of_nonneg_left (sharp_potential_drift_bound ht hκ) hb.le
  have hlap := radialBarrier_laplacian_strict hκ x hx
  nlinarith

end DeGiorgi
end

end OAI
