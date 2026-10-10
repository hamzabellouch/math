import OAI.Analysis.AllenCahn.PoissonMaximum

namespace OAI

noncomputable section
namespace PoissonSupport.DeGiorgi
open MeasureTheory
open scoped ENNReal
open Filter Topology

lemma laplacian_poisson_at_max {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (A ε : ℝ) {x y : Space n}
    (hxy : y ≠ x) (hsmall : ‖y - x‖ < 1)
    (hm : ∀ a b : Space n,
      f b - f a - poissonPenalty A ‖b - a‖ - ε * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤
      f y - f x - poissonPenalty A ‖y - x‖ - ε * (‖x‖ ^ 2 + ‖y‖ ^ 2)) :
    Laplacian.laplacian f y - Laplacian.laplacian f x ≤ -8 * A + 4 * n * ε := by
  let r := ‖y - x‖
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let e : Space n := r⁻¹ • (y - x)
  have he : ‖e‖ = 1 := by simp [e, norm_smul, r, hr.ne']
  have her : r • e = y - x := by dsimp [e]; rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  let J := reflect e
  let a : Space n := (-2 : ℝ) • e
  let g : Space n → ℝ := fun z => r + inner ℝ a z
  have hg : ContDiff ℝ 2 g := contDiff_const.add (innerSL ℝ a).contDiff
  have hg0 : g 0 = r := by simp [g]
  have hdistance : ∀ z : Space n, y + J z - (x + z) = g z • e := by
    intro z
    have hai : inner ℝ a z = (-2 : ℝ) * inner ℝ e z := by
      dsimp only [a]
      rw [real_inner_smul_left]
    change y + reflect e z - (x + z) = (r + inner ℝ a z) • e
    rw [reflect_apply he, hai, add_smul, her, neg_mul, neg_smul]
    abel
  have hnear : ∀ᶠ z in 𝓝 (0 : Space n), 0 < g z ∧ g z < 1 :=
    ((hg.continuous.isOpen_preimage _ isOpen_Ioo).mem_nhds (by simpa [hg0] using And.intro hr hsmall))
  let F : Space n → ℝ := fun z => f (y + J z) - f (x + z) -
    A * (2 * g z - (g z) ^ 2) - ε * (‖x + z‖ ^ 2 + ‖y + J z‖ ^ 2)
  have hfy : ContDiff ℝ 2 (fun z => f (y + J z)) :=
    hf.comp (contDiff_const.add J.contDiff)
  have hfx : ContDiff ℝ 2 (fun z => f (x + z)) := hf.comp (contDiff_const.add contDiff_id)
  have hnx : ContDiff ℝ 2 (fun z : Space n => ‖x + z‖ ^ 2) :=
    (contDiff_const.add contDiff_id).norm_sq ℝ
  have hny : ContDiff ℝ 2 (fun z : Space n => ‖y + J z‖ ^ 2) :=
    (contDiff_const.add J.contDiff).norm_sq ℝ
  have hp : ContDiff ℝ 2 (fun z => A * (2 * g z - (g z) ^ 2)) := by fun_prop
  have hq : ContDiff ℝ 2 (fun z => ε * (‖x + z‖ ^ 2 + ‖y + J z‖ ^ 2)) := by fun_prop
  have hF : ContDiff ℝ 2 F := ((hfy.sub hfx).sub hp).sub hq
  have hmax : IsLocalMax F 0 := by
    filter_upwards [hnear] with z hz
    have hnorm : ‖y + J z - (x + z)‖ = g z := by
      rw [hdistance, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hz.1]
    have hh := hm (x + z) (y + J z)
    rw [hnorm, poissonPenalty_of_le A hz.2.le, poissonPenalty_of_le A hsmall.le] at hh
    simpa [F, hg0, r] using hh
  have hl := laplacian_nonpos_of_local_max hF hmax
  have hly : Laplacian.laplacian (fun z => f (y + J z)) 0 = Laplacian.laplacian f y := by
    have ht : ContDiff ℝ 2 (fun u => f (y + u)) := hf.comp (contDiff_const.add contDiff_id)
    simpa only [map_zero, laplacian_translate hf, add_zero] using laplacian_comp_isometry ht J 0
  have hns : ContDiff ℝ 2 (fun z : Space n => ‖z‖ ^ 2) := contDiff_id.norm_sq ℝ
  have hlny : Laplacian.laplacian (fun z => ‖y + J z‖ ^ 2) 0 = 2 * n := by
    have ht : ContDiff ℝ 2 (fun u : Space n => ‖y + u‖ ^ 2) :=
      (contDiff_const.add contDiff_id).norm_sq ℝ
    simpa only [map_zero, laplacian_translate hns, laplacian_norm_sq] using
      laplacian_comp_isometry ht J 0
  have hal : ‖a‖ ^ 2 = 4 := by simp [a, norm_smul, he]; norm_num
  have hlg : Laplacian.laplacian g 0 = 0 := laplacian_affine a r 0
  have hlgs : Laplacian.laplacian (fun z => g z ^ 2) 0 = 8 := by
    rw [show (fun z => g z ^ 2) = (fun z => (r + inner ℝ a z) ^ 2) from rfl,
      laplacian_affine_sq, hal]
    norm_num
  have hg2 : ContDiff ℝ 2 (fun z => 2 * g z) := contDiff_const.mul hg
  dsimp only [F] at hl
  rw [laplacian_fun_sub ((hfy.sub hfx).sub hp) hq,
    laplacian_fun_sub (hfy.sub hfx) hp, laplacian_fun_sub hfy hfx,
    hly, laplacian_translate hf,
    laplacian_fun_const_mul (hg2.sub (hg.pow 2)),
    laplacian_fun_sub hg2 (hg.pow 2),
    laplacian_fun_const_mul hg, hlg, hlgs,
    laplacian_fun_const_mul (hnx.add hny), laplacian_fun_add hnx hny,
    laplacian_translate hns, laplacian_norm_sq, hlny] at hl
  simp only [add_zero] at hl
  linarith

lemma bounded_poisson_lipschitz {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) {M C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hbound : ∀ x, |f x| ≤ M) (hlap : ∀ x, |Laplacian.laplacian f x| ≤ C) :
    ∀ x y, |f y - f x| ≤ 2 * (2 * M + C + 1) * ‖y - x‖ := by
  let A := 2 * M + C + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hlarge : 2 * M < A := by dsimp [A]; linarith
  have honeway : ∀ x y, f y - f x ≤ 2 * A * ‖y - x‖ := by
    intro x₀ y₀
    by_contra hbad
    have hbad' : 2 * A * ‖y₀ - x₀‖ < f y₀ - f x₀ := lt_of_not_ge hbad
    let δ := f y₀ - f x₀ - poissonPenalty A ‖y₀ - x₀‖
    have hδ : 0 < δ := by
      dsimp [δ]
      have hh := poissonPenalty_le_linear hA.le (norm_nonneg (y₀ - x₀))
      linarith
    let S := ‖x₀‖ ^ 2 + ‖y₀‖ ^ 2
    have hS : 0 ≤ S := by dsimp [S]; positivity
    let ε := min (δ / (2 * (S + 1))) (1 / (n + 1 : ℝ))
    have hε : 0 < ε := lt_min (by positivity) (by positivity)
    have hεS : ε * (S + 1) ≤ δ / 2 := by
      have hh := min_le_left (δ / (2 * (S + 1))) (1 / (n + 1 : ℝ))
      have hh' := (le_div_iff₀ (show 0 < 2 * (S + 1) by positivity)).mp hh
      change ε * (2 * (S + 1)) ≤ δ at hh'
      linarith
    have hεn : (n : ℝ) * ε ≤ 1 := by
      have hh := min_le_right (δ / (2 * (S + 1))) (1 / (n + 1 : ℝ))
      have hh' := (le_div_iff₀ (show 0 < (n : ℝ) + 1 by positivity)).mp hh
      change ε * ((n : ℝ) + 1) ≤ 1 at hh'
      nlinarith
    have hpos₀ : 0 < f y₀ - f x₀ - poissonPenalty A ‖y₀ - x₀‖ -
        ε * (‖x₀‖ ^ 2 + ‖y₀‖ ^ 2) := by
      change 0 < δ - ε * S
      nlinarith
    obtain ⟨x, y, hm⟩ := poisson_maximum hf.continuous hM hbound hA.le hε
    have hp : 0 < f y - f x - poissonPenalty A ‖y - x‖ - ε * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
      hpos₀.trans_le (hm x₀ y₀)
    have hpen : 0 ≤ ε * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by positivity
    have hxy : y ≠ x := by
      rintro rfl
      simp only [sub_self, norm_zero, poissonPenalty, sub_zero, max_eq_left zero_le_one,
        one_pow, sub_self, mul_zero] at hp
      linarith
    have hs : ‖y - x‖ < 1 := by
      by_contra h
      rw [poissonPenalty_of_ge A (le_of_not_gt h)] at hp
      have hb₁ := (abs_le.mp (hbound x)).1
      have hb₂ := (abs_le.mp (hbound y)).2
      linarith
    have hl := laplacian_poisson_at_max hf A ε hxy hs hm
    have hb₁ := (abs_le.mp (hlap y)).1
    have hb₂ := (abs_le.mp (hlap x)).2
    dsimp [A] at hl
    linarith
  intro x y
  apply abs_le.mpr
  constructor
  · have h := honeway y x
    rw [norm_sub_rev x y] at h
    linarith
  · exact honeway x y

lemma gradient_poisson_at_max_y {n : ℕ} {f : Space n → ℝ}
    (hf : Differentiable ℝ f) (A ε : ℝ) {x y : Space n}
    (hxy : y ≠ x) (hs : ‖y - x‖ < 1)
    (hm : ∀ b : Space n,
      f b - f x - poissonPenalty A ‖b - x‖ - ε * (‖x‖ ^ 2 + ‖b‖ ^ 2) ≤
      f y - f x - poissonPenalty A ‖y - x‖ - ε * (‖x‖ ^ 2 + ‖y‖ ^ 2)) :
    gradient f y = (2 * A * (1 - ‖y - x‖) / ‖y - x‖) • (y - x) +
      (2 * ε) • y := by
  have hn : HasFDerivAt (fun b : Space n => ‖b - x‖)
      (‖y - x‖⁻¹ • innerSL ℝ (y - x)) y := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using
      (hasFDerivAt_norm_nonzero (sub_ne_zero.mpr hxy)).comp y
      ((hasFDerivAt_id y).sub_const x)
  have hq : HasFDerivAt (fun b : Space n => ‖x‖ ^ 2 + ‖b‖ ^ 2)
      ((2 : ℝ) • innerSL ℝ y) y := by
    have hh := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_add (‖x‖ ^ 2)
    rw [← Nat.cast_smul_eq_nsmul ℝ 2, Nat.cast_ofNat] at hh
    exact hh
  have hp := ((hn.const_mul 2).sub (hn.pow 2)).const_mul A
  have hd := (((hf y).hasFDerivAt.sub_const (f x)).fun_sub hp).fun_sub (hq.const_mul ε)
  have hnear : ∀ᶠ b : Space n in 𝓝 y, ‖b - x‖ < 1 :=
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds hs
  have hmax : IsLocalMax (fun b : Space n => f b - f x -
      A * (2 * ‖b - x‖ - ‖b - x‖ ^ 2) - ε * (‖x‖ ^ 2 + ‖b‖ ^ 2)) y := by
    filter_upwards [hnear] with b hb
    simpa only [poissonPenalty_of_le A hb.le, poissonPenalty_of_le A hs.le] using hm b
  have hz := hmax.hasFDerivAt_eq_zero hd
  apply (InnerProductSpace.toDual ℝ (Space n)).injective
  ext z
  have he := congrArg (fun L : Space n →L[ℝ] ℝ => L z) hz
  simp only [sub_apply, smul_apply, smul_eq_mul, zero_apply, pow_one,
    Nat.cast_ofNat, Nat.reduceSub, nsmul_eq_mul, innerSL_apply_apply] at he
  simp only [toDual_gradient, map_add, map_smul, add_apply, smul_apply,
    InnerProductSpace.toDual_apply_apply, smul_eq_mul]
  change (fderiv ℝ f y) z = _
  change (fderiv ℝ f y) z - A * (2 * (‖y - x‖⁻¹ * inner ℝ (y - x) z) -
    (2 * ‖y - x‖) * (‖y - x‖⁻¹ * inner ℝ (y - x) z)) -
    ε * (2 * inner ℝ y z) = 0 at he
  rw [div_eq_mul_inv]
  nlinarith

lemma poisson_gradient_bounds {n : ℕ} {f : Space n → ℝ}
    (hf : Differentiable ℝ f) {M A ε : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |f x| ≤ M) (hA : 0 ≤ A) (hε : 0 < ε)
    {x y : Space n} (hxy : y ≠ x) (hs : ‖y - x‖ < 1)
    (hpos : 0 < f y - f x - poissonPenalty A ‖y - x‖ - ε * (‖x‖ ^ 2 + ‖y‖ ^ 2))
    (hm : ∀ a b : Space n,
      f b - f a - poissonPenalty A ‖b - a‖ - ε * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤
      f y - f x - poissonPenalty A ‖y - x‖ - ε * (‖x‖ ^ 2 + ‖y‖ ^ 2)) :
    ‖gradient f x‖ ≤ 2 * A + 2 * Real.sqrt (2 * M * ε) ∧
      ‖gradient f y‖ ≤ 2 * A + 2 * Real.sqrt (2 * M * ε) := by
  have hpen : ε * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤ 2 * M := by
    have hx := (abs_le.mp (hbound x)).1
    have hy := (abs_le.mp (hbound y)).2
    have hz := poissonPenalty_nonneg hA (norm_nonneg (y - x))
    linarith
  have hsmall : ∀ z : Space n, ε * ‖z‖ ^ 2 ≤ 2 * M →
      ‖(2 * ε) • z‖ ≤ 2 * Real.sqrt (2 * M * ε) := by
    intro z hz
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * ε)]
    have hsq := Real.sq_sqrt (show 0 ≤ 2 * M * ε by positivity)
    have hc := mul_le_mul_of_nonneg_right hz hε.le
    nlinarith [Real.sqrt_nonneg (2 * M * ε), norm_nonneg z]
  have hxsmall := hsmall x (by nlinarith [mul_nonneg hε.le (sq_nonneg ‖y‖)])
  have hysmall := hsmall y (by nlinarith [mul_nonneg hε.le (sq_nonneg ‖x‖)])
  have hpbound {a b : Space n} (hab : b ≠ a) (hr : ‖b - a‖ < 1) :
      ‖(2 * A * (1 - ‖b - a‖) / ‖b - a‖) • (b - a)‖ ≤ 2 * A := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hab))]
    nlinarith [norm_nonneg (b - a)]
  have hgy := gradient_poisson_at_max_y hf A ε hxy hs (hm x)
  have hnegmax : ∀ a b : Space n,
      -f b - -f a - poissonPenalty A ‖b - a‖ - ε * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤
      -f x - -f y - poissonPenalty A ‖x - y‖ - ε * (‖y‖ ^ 2 + ‖x‖ ^ 2) := by
    intro a b
    simpa only [neg_sub_neg, norm_sub_rev, add_comm] using hm b a
  have hgx := gradient_poisson_at_max_y hf.neg A ε (Ne.symm hxy)
    (by simpa only [norm_sub_rev] using hs) (hnegmax y)
  have hng : gradient (fun z => -f z) x = -gradient f x := by
    simp only [gradient, fderiv_fun_neg, map_neg]
  change gradient (fun z => -f z) x = _ at hgx
  rw [hng] at hgx
  constructor
  · calc ‖gradient f x‖ = ‖-gradient f x‖ := (norm_neg _).symm
         _ = ‖(2 * A * (1 - ‖x - y‖) / ‖x - y‖) • (x - y) + (2 * ε) • x‖ := congrArg norm hgx
         _ ≤ _ := (norm_add_le _ _).trans (add_le_add
           (hpbound (Ne.symm hxy) (by simpa only [norm_sub_rev] using hs)) hxsmall)
  · rw [hgy]
    exact (norm_add_le _ _).trans (add_le_add (hpbound hxy hs) hysmall)

lemma bounded_unit_drift_lipschitz {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (b : Space n → Space n) {M C : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ M)
    (hb : ∀ x, ‖b x‖ ≤ 1)
    (hpde : ∀ x, |Laplacian.laplacian f x - fderiv ℝ f x (b x)| ≤ C) :
    ∀ x y, |f y - f x| ≤ 2 * (2 * M + C + 3) * ‖y - x‖ := by
  let A := 2 * M + C + 3
  have hA : 0 < A := by dsimp [A]; positivity
  have hlarge : 2 * M < A := by dsimp [A]; linarith
  have honeway : ∀ x y, f y - f x ≤ 2 * A * ‖y - x‖ := by
    intro x₀ y₀
    by_contra hbad
    have hbad' : 2 * A * ‖y₀ - x₀‖ < f y₀ - f x₀ := lt_of_not_ge hbad
    let δ := f y₀ - f x₀ - poissonPenalty A ‖y₀ - x₀‖
    have hδ : 0 < δ := by
      dsimp [δ]
      have hh := poissonPenalty_le_linear hA.le (norm_nonneg (y₀ - x₀))
      linarith
    let S := ‖x₀‖ ^ 2 + ‖y₀‖ ^ 2
    have hS : 0 ≤ S := by dsimp [S]; positivity
    let ε := min (δ / (2 * (S + 1))) (min (1 / (n + 1 : ℝ)) (1 / (8 * M + 1)))
    have hε : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by positivity))
    have hεS : ε * (S + 1) ≤ δ / 2 := by
      have hh := min_le_left (δ / (2 * (S + 1))) (min (1 / (n + 1 : ℝ)) (1 / (8 * M + 1)))
      have hh' := (le_div_iff₀ (show 0 < 2 * (S + 1) by positivity)).mp hh
      change ε * (2 * (S + 1)) ≤ δ at hh'
      linarith
    have hεn : (n : ℝ) * ε ≤ 1 := by
      have hh : ε ≤ 1 / (n + 1 : ℝ) := (min_le_right _ _).trans (min_le_left _ _)
      have hh' := (le_div_iff₀ (show 0 < (n : ℝ) + 1 by positivity)).mp hh
      nlinarith
    have hεM : 2 * Real.sqrt (2 * M * ε) ≤ 1 := by
      have hh : ε ≤ 1 / (8 * M + 1) := (min_le_right _ _).trans (min_le_right _ _)
      have hh' := (le_div_iff₀ (show 0 < 8 * M + 1 by positivity)).mp hh
      have hs := Real.sq_sqrt (show 0 ≤ 2 * M * ε by positivity)
      nlinarith [Real.sqrt_nonneg (2 * M * ε)]
    have hpos₀ : 0 < f y₀ - f x₀ - poissonPenalty A ‖y₀ - x₀‖ -
        ε * (‖x₀‖ ^ 2 + ‖y₀‖ ^ 2) := by
      change 0 < δ - ε * S
      nlinarith
    obtain ⟨x, y, hm⟩ := poisson_maximum hf.continuous hM hbound hA.le hε
    have hp : 0 < f y - f x - poissonPenalty A ‖y - x‖ - ε * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
      hpos₀.trans_le (hm x₀ y₀)
    have hpen : 0 ≤ ε * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by positivity
    have hxy : y ≠ x := by
      rintro rfl
      simp only [sub_self, norm_zero, poissonPenalty, sub_zero, max_eq_left zero_le_one,
        one_pow, sub_self, mul_zero] at hp
      linarith
    have hs : ‖y - x‖ < 1 := by
      by_contra h
      rw [poissonPenalty_of_ge A (le_of_not_gt h)] at hp
      have hb₁ := (abs_le.mp (hbound x)).1
      have hb₂ := (abs_le.mp (hbound y)).2
      linarith
    have hl := laplacian_poisson_at_max hf A ε hxy hs hm
    have hg := poisson_gradient_bounds (hf.differentiable (by norm_num)) hM hbound hA.le hε hxy hs hp hm
    have hdr (z : Space n) : |fderiv ℝ f z (b z)| ≤ ‖gradient f z‖ := by
      rw [← toDual_gradient]
      change |inner ℝ (gradient f z) (b z)| ≤ _
      exact (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (gradient f z), hb z])
    have hx := (abs_le.mp (hpde x)).2
    have hy := (abs_le.mp (hpde y)).1
    have hd₁ := (abs_le.mp (hdr x)).2
    have hd₂ := (abs_le.mp (hdr y)).1
    dsimp [A] at *
    linarith
  intro x y
  apply abs_le.mpr
  constructor
  · have h := honeway y x
    rw [norm_sub_rev x y] at h
    linarith
  · exact honeway x y

lemma fderiv_dilation {n : ℕ} {f : Space n → ℝ} (hf : Differentiable ℝ f)
    (r : ℝ) (x a : Space n) :
    fderiv ℝ (fun z => f (r • z)) x a = r * fderiv ℝ f (r • x) a := by
  have hd : HasFDerivAt (fun z => f (r • z))
      ((fderiv ℝ f (r • x)).comp (r • ContinuousLinearMap.id ℝ (Space n))) x := by
    simpa only [Function.comp_def, id_eq] using
      (hf (r • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul r)
  rw [hd.fderiv]
  simp

lemma coordDeriv_dilation {n : ℕ} {f : Space n → ℝ} (hf : Differentiable ℝ f)
    (r : ℝ) (i : Fin n) (x : Space n) :
    coordDeriv (fun z => f (r • z)) i x = r * coordDeriv f i (r • x) :=
  fderiv_dilation hf r x (basis n i)

lemma coordDeriv_const_mul {n : ℕ} {f : Space n → ℝ} (hf : Differentiable ℝ f)
    (r : ℝ) (i : Fin n) (x : Space n) :
    coordDeriv (fun z => r * f z) i x = r * coordDeriv f i x := by
  dsimp [coordDeriv]
  rw [fderiv_const_mul (hf x)]
  simp

lemma laplacian_dilation {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (r : ℝ) (x : Space n) :
    Laplacian.laplacian (fun z => f (r • z)) x = r ^ 2 * Laplacian.laplacian f (r • x) := by
  have hc : ContDiff ℝ 2 (fun z => f (r • z)) := hf.comp (contDiff_id.const_smul r)
  rw [laplacian_eq_sum_coordDeriv hc, laplacian_eq_sum_coordDeriv hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : coordDeriv (fun z => f (r • z)) i = fun z => r * coordDeriv f i (r • z) :=
    funext (coordDeriv_dilation (hf.differentiable (by norm_num)) r i)
  have hd : Differentiable ℝ (fun z => coordDeriv f i (r • z)) :=
    ((coordDeriv_contDiff hf i).differentiable (by norm_num)).comp (differentiable_id.const_smul r)
  rw [he, coordDeriv_const_mul hd,
    coordDeriv_dilation ((coordDeriv_contDiff hf i).differentiable (by norm_num))]
  ring

end PoissonSupport.DeGiorgi
end

end OAI
