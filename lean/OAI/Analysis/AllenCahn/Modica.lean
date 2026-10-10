import OAI.Analysis.AllenCahn.Basic

namespace OAI

noncomputable section
namespace DeGiorgi
open MeasureTheory
open scoped ENNReal
open Filter Topology

lemma two_point_gradient_bounds {n : ℕ} {f : Space n → ℝ}
    (hf : Differentiable ℝ f) {M L ε : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |f x| ≤ M) (hL : 0 ≤ L) (hε : 0 < ε) {x y : Space n}
    (hpos : 0 < f y - f x - L * ‖y - x‖ - ε * (‖x‖ ^ 2 + ‖y‖ ^ 2))
    (hm : ∀ a b : Space n,
      f b - f a - L * ‖b - a‖ - ε * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤
      f y - f x - L * ‖y - x‖ - ε * (‖x‖ ^ 2 + ‖y‖ ^ 2)) :
    let E := 2 * Real.sqrt (2 * M * ε)
    |‖gradient f x‖ ^ 2 - L ^ 2| ≤ E * (2 * L + E) ∧
      |‖gradient f y‖ ^ 2 - L ^ 2| ≤ E * (2 * L + E) := by
  have hxy : y ≠ x := by
    rintro rfl
    simp only [sub_self, norm_zero, mul_zero] at hpos
    nlinarith [sq_nonneg ‖y‖]
  have hpen : ε * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤ 2 * M := by
    have hx := (abs_le.mp (hbound x)).1
    have hy := (abs_le.mp (hbound y)).2
    have hz := mul_nonneg hL (norm_nonneg (y - x))
    linarith
  let E := 2 * Real.sqrt (2 * M * ε)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hsmall : ∀ z : Space n, ε * ‖z‖ ^ 2 ≤ 2 * M → ‖(2 * ε) • z‖ ≤ E := by
    intro z hz
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * ε)]
    have hs := Real.sq_sqrt (show 0 ≤ 2 * M * ε by positivity)
    have hc := mul_le_mul_of_nonneg_right hz hε.le
    dsimp [E]
    nlinarith [Real.sqrt_nonneg (2 * M * ε), norm_nonneg z]
  have hxsmall := hsmall x (by nlinarith [mul_nonneg hε.le (sq_nonneg ‖y‖)])
  have hysmall := hsmall y (by nlinarith [mul_nonneg hε.le (sq_nonneg ‖x‖)])
  let p : Space n := (L / ‖y - x‖) • (y - x)
  have hp : ‖p‖ = L := by
    dsimp [p]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hL (norm_nonneg _)),
      div_mul_cancel₀ L (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))]
  have hgy := gradient_at_two_point_max_y hf L ε hxy (hm x)
  have hnegmax : ∀ a b : Space n,
      -f b - -f a - L * ‖b - a‖ - ε * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤
      -f x - -f y - L * ‖x - y‖ - ε * (‖y‖ ^ 2 + ‖x‖ ^ 2) := by
    intro a b
    simpa only [neg_sub_neg, norm_sub_rev, add_comm] using hm b a
  have hgx := gradient_at_two_point_max_y hf.neg L ε (Ne.symm hxy) (hnegmax y)
  have hng : gradient (fun z => -f z) x = -gradient f x := by
    simp only [gradient, fderiv_fun_neg, map_neg]
  change gradient (fun z => -f z) x = _ at hgx
  rw [hng] at hgx
  have hxerr : ‖gradient f x - p‖ ≤ E := by
    have hvec : gradient f x - p = -(2 * ε) • x := by
      rw [norm_sub_rev] at hgx
      have hs : (L / ‖y - x‖) • (x - y) = -p := by
        dsimp [p]
        rw [← neg_sub y x, smul_neg]
      rw [hs] at hgx
      have hh := congrArg (fun z : Space n => -z) hgx
      simp only [neg_neg] at hh
      rw [hh]
      module
    rw [hvec, neg_smul, norm_neg]
    exact hxsmall
  have hyerr : ‖gradient f y - p‖ ≤ E := by
    change gradient f y = p + (2 * ε) • y at hgy
    rw [hgy, add_sub_cancel_left]
    exact hysmall
  exact ⟨sq_norm_error hL hE hp hxerr, sq_norm_error hL hE hp hyerr⟩

lemma lipschitz_of_laplacian_monotonicity {n : ℕ} {f b h : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) {M B L κ : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hL : 0 ≤ L) (hκ : 0 < κ) (hbound : ∀ x, |f x| ≤ M)
    (hb : ∀ x, |b x| ≤ B)
    (hpde : ∀ x, Laplacian.laplacian f x = b x * ‖gradient f x‖ ^ 2 + h x)
    (hmono : ∀ x y, f x ≤ f y → κ * (f y - f x) ≤
      (b y * L ^ 2 + h y) - (b x * L ^ 2 + h x)) :
    ∀ x y, f y - f x ≤ L * ‖y - x‖ := by
  intro a c
  by_contra hn
  let δ := f c - f a - L * ‖c - a‖
  have hδ : 0 < δ := sub_pos.mpr (lt_of_not_ge hn)
  let E : ℝ → ℝ := fun t => 2 * Real.sqrt (2 * M * t)
  have hcont : Continuous (fun t : ℝ => 4 * n * t + 2 * B * (E t * (2 * L + E t))) := by
    dsimp [E]
    fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ),
      4 * n * t + 2 * B * (E t * (2 * L + E t)) < κ * δ / 2 := by
    have hzero : (fun t : ℝ => 4 * n * t + 2 * B * (E t * (2 * L + E t))) 0 = 0 := by
      simp [E]
    exact (hcont.continuousAt.eventually_lt continuousAt_const (by simpa only [E, mul_zero, Real.sqrt_zero, zero_mul, add_zero] using (show 0 < κ * δ / 2 by positivity)))
  have hcont2 : Continuous (fun t : ℝ => t * (‖a‖ ^ 2 + ‖c‖ ^ 2)) := by fun_prop
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℝ), t * (‖a‖ ^ 2 + ‖c‖ ^ 2) < δ / 2 :=
    hcont2.continuousAt.eventually_lt continuousAt_const (by simpa using half_pos hδ)
  have hex : ∃ ε : ℝ, 0 < ε ∧ ε * (‖a‖ ^ 2 + ‖c‖ ^ 2) < δ / 2 ∧
      4 * n * ε + 2 * B * (E ε * (2 * L + E ε)) < κ * δ / 2 := by
    have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧
        t * (‖a‖ ^ 2 + ‖c‖ ^ 2) < δ / 2 ∧
        4 * n * t + 2 * B * (E t * (2 * L + E t)) < κ * δ / 2 := by
      filter_upwards [self_mem_nhdsWithin, hev2.filter_mono nhdsWithin_le_nhds,
        hev.filter_mono nhdsWithin_le_nhds] with t ht h1 h2 using ⟨ht, h1, h2⟩
    exact hevent.exists
  obtain ⟨ε, hε, hseed, herr⟩ := hex
  obtain ⟨x, y, hm⟩ := two_point_maximum hf.continuous hM hbound hL hε
  have hval : δ / 2 < f y - f x - L * ‖y - x‖ - ε * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    have hh := hm a c
    dsimp [δ] at hseed ⊢
    linarith
  have hfd : δ / 2 < f y - f x := by
    have hh := mul_nonneg hL (norm_nonneg (y - x))
    have hh' := mul_nonneg hε.le (add_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖y‖))
    linarith
  have hxy : f x ≤ f y := by linarith
  have hgap := hmono x y hxy
  have hgrad := two_point_gradient_bounds (hf.differentiable (by norm_num)) hM hbound hL hε
    (lt_trans (half_pos hδ) hval) hm
  have hE : 0 ≤ E ε := by dsimp [E]; positivity
  have herror (z : Space n) (hz : |‖gradient f z‖ ^ 2 - L ^ 2| ≤ E ε * (2 * L + E ε)) :
      |b z * (‖gradient f z‖ ^ 2 - L ^ 2)| ≤ B * (E ε * (2 * L + E ε)) := by
    rw [abs_mul]
    exact mul_le_mul (hb z) hz (abs_nonneg _) hB
  have hx := abs_le.mp (herror x hgrad.1)
  have hy := abs_le.mp (herror y hgrad.2)
  have hlap := laplacian_at_two_point_max hf L ε hm
  rw [hpde y, hpde x] at hlap
  have hstrict := mul_lt_mul_of_pos_left hfd hκ
  nlinarith

def defectWeight {n : ℕ} (v : Space n → ℝ) (x : Space n) : ℝ := 1 - v x ^ 2

lemma hasDerivAt_artanh {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - t ^ 2)) t := by
  have hm : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht.2)
  have hp : 1 + t ≠ 0 := ne_of_gt (by linarith [ht.1])
  have hd : HasDerivAt (fun y : ℝ => (1 + y) / (1 - y))
      ((1 * (1 - t) - (1 + t) * (-1)) / (1 - t) ^ 2) t :=
    ((hasDerivAt_id t).const_add 1).div ((hasDerivAt_id t).const_sub 1) hm
  have heq : 1 / 2 * (((1 * (1 - t) - (1 + t) * (-1)) / (1 - t) ^ 2) /
      ((1 + t) / (1 - t))) = 1 / (1 - t ^ 2) := by
    have hs : 1 - t ^ 2 = (1 - t) * (1 + t) := by ring
    rw [hs]
    field_simp
    ring
  have hh := (hd.log (div_ne_zero hp hm)).const_mul (1 / 2 : ℝ)
  rw [heq] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy
  exact Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩

def inverseProfile {n : ℕ} (v : Space n → ℝ) (x : Space n) : ℝ :=
  Real.sqrt 2 * Real.artanh (v x)

def diffuseDefect {n : ℕ} (v : Space n → ℝ) (x : Space n) : ℝ :=
  1 - ‖gradient (inverseProfile v) x‖ ^ 2

lemma profile_inverseProfile {n : ℕ} {v : Space n → ℝ}
    (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (x : Space n) :
    profile (inverseProfile v x) = v x := by
  have h2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  simp only [profile, inverseProfile, mul_div_cancel_left₀ _ h2]
  exact Real.tanh_artanh (hi x)

lemma fderiv_inverseProfile {n : ℕ} {v : Space n → ℝ} {x : Space n}
    (hv : DifferentiableAt ℝ v x) (hi : v x ∈ Set.Ioo (-1 : ℝ) 1) :
    fderiv ℝ (inverseProfile v) x =
      (Real.sqrt 2 / defectWeight v x) • fderiv ℝ v x := by
  have H := ((hasDerivAt_artanh hi).comp_hasFDerivAt x hv.hasFDerivAt).const_mul (Real.sqrt 2)
  change fderiv ℝ (fun y => Real.sqrt 2 * Real.artanh (v y)) x = _
  simpa only [Function.comp_apply, smul_smul, mul_one_div, defectWeight]
    using H.fderiv

lemma gradient_inverseProfile {n : ℕ} {v : Space n → ℝ} {x : Space n}
    (hv : DifferentiableAt ℝ v x) (hi : v x ∈ Set.Ioo (-1 : ℝ) 1) :
    gradient (inverseProfile v) x = (Real.sqrt 2 / defectWeight v x) • gradient v x := by
  simp only [gradient, fderiv_inverseProfile hv hi, map_smul]

lemma inverseProfile_contDiff {n : ℕ} {v : Space n → ℝ} (hv : ContDiff ℝ 2 v)
    (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) : ContDiff ℝ 2 (inverseProfile v) := by
  have hm (x : Space n) : 1 - v x ≠ 0 := ne_of_gt (sub_pos.mpr (hi x).2)
  have hp (x : Space n) : 1 + v x ≠ 0 := ne_of_gt (by linarith [(hi x).1])
  have hq : ContDiff ℝ 2 (fun x => (1 + v x) / (1 - v x)) :=
    (contDiff_const.add hv).div (contDiff_const.sub hv) hm
  have hl : ContDiff ℝ 2 (fun x => (Real.sqrt 2 / 2) * Real.log ((1 + v x) / (1 - v x))) :=
    contDiff_const.mul (hq.log (fun x => div_ne_zero (hp x) (hm x)))
  convert hl using 1
  funext x
  dsimp [inverseProfile]
  rw [Real.artanh_eq_half_log ⟨(hi x).1.le, (hi x).2.le⟩]
  ring

lemma gradient_norm_sq {n : ℕ} (f : Space n → ℝ) (x : Space n) :
    ‖gradient f x‖ ^ 2 = ∑ i : Fin n, (coordDeriv f i x) ^ 2 := by
  have h := (basis n).sum_inner_mul_inner (gradient f x) (gradient f x)
  rw [real_inner_self_eq_norm_sq] at h
  simpa only [coordDeriv, real_inner_comm, inner_gradient_left, ← pow_two] using h.symm

lemma coordDeriv_mul {n : ℕ} {f g : Space n → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin n) (x : Space n) :
    coordDeriv (fun y => f y * g y) i x =
      f x * coordDeriv g i x + g x * coordDeriv f i x := by
  simp [coordDeriv, fderiv_fun_mul (hf x) (hg x)]

lemma weight_pos {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) : 0 < 1 - t ^ 2 := by
  nlinarith [mul_pos (sub_pos.mpr ht.2) (show 0 < 1 + t by linarith [ht.1])]

lemma coordDeriv_inverseProfile_coefficient {n : ℕ} {v : Space n → ℝ}
    (hv : Differentiable ℝ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (i : Fin n) (x : Space n) :
    coordDeriv (fun y => Real.sqrt 2 / defectWeight v y) i x =
      (2 * Real.sqrt 2 * v x / (defectWeight v x) ^ 2) * coordDeriv v i x := by
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt 2 / (1 - t ^ 2))
      (2 * Real.sqrt 2 * v x / (1 - v x ^ 2) ^ 2) (v x) := by
    convert (hasDerivAt_const (v x) (Real.sqrt 2)).div
      ((hasDerivAt_const (v x) (1 : ℝ)).sub ((hasDerivAt_id (v x)).pow 2))
      (ne_of_gt (weight_pos (hi x))) using 1 <;> first | rfl | (dsimp; ring)
  have hd := hs.comp_hasFDerivAt x (hv x).hasFDerivAt
  dsimp [coordDeriv, defectWeight]
  simpa only [Function.comp_def, smul_apply, smul_eq_mul] using
    congrArg (fun L : Space n →L[ℝ] ℝ => L (basis n i)) hd.fderiv

lemma laplacian_inverseProfile {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (x : Space n) :
    Laplacian.laplacian (inverseProfile v) x =
      Real.sqrt 2 / defectWeight v x * Laplacian.laplacian v x +
        (2 * Real.sqrt 2 * v x / defectWeight v x ^ 2) * ‖gradient v x‖ ^ 2 := by
  have hd := hv.differentiable (by norm_num)
  have hc : Differentiable ℝ (fun y => Real.sqrt 2 / defectWeight v y) := by
    have H : ContDiff ℝ 2 (fun y => Real.sqrt 2 / (1 - v y ^ 2)) :=
      contDiff_const.div (contDiff_const.sub (hv.pow 2)) (fun y => ne_of_gt (weight_pos (hi y)))
    exact H.differentiable (by norm_num)
  have hfirst (i : Fin n) : coordDeriv (inverseProfile v) i =
      fun y => (Real.sqrt 2 / defectWeight v y) * coordDeriv v i y := by
    funext y
    simp [coordDeriv, fderiv_inverseProfile (hd y) (hi y)]
  rw [laplacian_eq_sum_coordDeriv (inverseProfile_contDiff hv hi)]
  simp_rw [hfirst]
  simp_rw [coordDeriv_mul hc ((coordDeriv_contDiff hv _).differentiable (by norm_num)),
    coordDeriv_inverseProfile_coefficient hd hi]
  rw [laplacian_eq_sum_coordDeriv hv, gradient_norm_sq, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma laplacian_regularized_inverse {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hb : ∀ x, v x ∈ Set.Icc (-1 : ℝ) 1)
    (hAC : AllenCahn v) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (x : Space n) :
    let t := r * v x
    Laplacian.laplacian (inverseProfile (fun y => r * v y)) x =
      Real.sqrt 2 * t * ‖gradient (inverseProfile (fun y => r * v y)) x‖ ^ 2 +
        (-Real.sqrt 2 * t + Real.sqrt 2 * (1 - r ^ 2) / r ^ 2 * (t ^ 3 / (1 - t ^ 2))) := by
  have hreg : ContDiff ℝ 2 (fun y => r * v y) := contDiff_const.mul hv
  have hi (y : Space n) : r * v y ∈ Set.Ioo (-1 : ℝ) 1 := by
    have H := mul_le_mul_of_nonneg_left (hb y).1 hr.le
    have H' := mul_le_mul_of_nonneg_left (hb y).2 hr.le
    constructor <;> nlinarith
  have hq : 1 - (r * v x) ^ 2 ≠ 0 := ne_of_gt (weight_pos (hi x))
  dsimp only
  rw [laplacian_inverseProfile hreg hi, laplacian_fun_const_mul hv,
    hAC, gradient_inverseProfile (hreg.differentiable (by norm_num) x) (hi x),
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    div_pow, Real.sq_sqrt (by norm_num)]
  have hg : gradient (fun y => r * v y) x = r • gradient v x := by
    simp [gradient, fderiv_const_mul (hv.differentiable (by norm_num) x)]
  rw [hg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  dsimp [defectWeight]
  have hqq : 1 - r ^ 2 * v x ^ 2 ≠ 0 := by simpa only [mul_pow] using hq
  field_simp [ne_of_gt hr, hq, hqq]
  ring

lemma cube_div_weight_monotone :
    MonotoneOn (fun t : ℝ => t ^ 3 / (1 - t ^ 2)) (Set.Ioo (-1 : ℝ) 1) := by
  have hd (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => t ^ 3 / (1 - t ^ 2))
        (t ^ 2 * (3 - t ^ 2) / (1 - t ^ 2) ^ 2) t := by
    convert ((hasDerivAt_id t).pow 3).div
      ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2))
      (ne_of_gt (weight_pos ht)) using 1 <;> first | rfl | (dsimp; ring)
  apply monotoneOn_of_deriv_nonneg (convex_Ioo (-1 : ℝ) 1)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hd t (by simpa only [interior_Ioo] using ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have hi : t ∈ Set.Ioo (-1 : ℝ) 1 := by simpa only [interior_Ioo] using ht
    rw [(hd t hi).deriv]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith [weight_pos hi])) (sq_nonneg _)

lemma inverseProfile_scalar_quantitative {r s t : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hs : s ∈ Set.Icc (-r) r) (ht : t ∈ Set.Icc (-r) r) (hst : s ≤ t) :
    (1 - r ^ 2) * (Real.sqrt 2 * Real.artanh t - Real.sqrt 2 * Real.artanh s) ≤
      Real.sqrt 2 * (t - s) := by
  have hir : r ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hr1⟩
  have hqr := weight_pos hir
  have hi (z : ℝ) (hz : z ∈ Set.Icc (-r) r) : z ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hd (z : ℝ) (hz : z ∈ Set.Icc (-r) r) :
      HasDerivAt (fun t => Real.sqrt 2 * Real.artanh t) (Real.sqrt 2 / (1 - z ^ 2)) z := by
    simpa only [mul_one_div] using (hasDerivAt_artanh (hi z hz)).const_mul (Real.sqrt 2)
  have hbound (z : ℝ) (hz : z ∈ Set.Icc (-r) r) :
      deriv (fun t => Real.sqrt 2 * Real.artanh t) z ≤ Real.sqrt 2 / (1 - r ^ 2) := by
    rw [(hd z hz).deriv]
    have hsq : z ^ 2 ≤ r ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hz.2) (show 0 ≤ z + r by linarith [hz.1])]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hqr (by linarith)
  have H := (convex_Icc (-r) r).image_sub_le_mul_sub_of_deriv_le
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => hbound z (interior_subset hz)) s hs t ht hst
  have H' := mul_le_mul_of_nonneg_left H hqr.le
  calc
    _ ≤ (1 - r ^ 2) * (Real.sqrt 2 / (1 - r ^ 2) * (t - s)) := H'
    _ = _ := by field_simp

lemma inverseProfile_scalar_bound {r t : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (ht : t ∈ Set.Icc (-r) r) :
    |Real.sqrt 2 * Real.artanh t| ≤ Real.sqrt 2 *
      max |Real.artanh (-r)| |Real.artanh r| := by
  have hm : -r ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hp : r ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hr1⟩
  have hi : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply abs_le.mpr
  constructor
  · have H := Real.strictMonoOn_artanh.monotoneOn hm hi ht.1
    have H' := neg_abs_le (Real.artanh (-r))
    have H'' := le_max_left |Real.artanh (-r)| |Real.artanh r|
    linarith
  · exact (Real.strictMonoOn_artanh.monotoneOn hi hp ht.2).trans
      ((le_abs_self _).trans (le_max_right _ _))

end DeGiorgi
end

end OAI
