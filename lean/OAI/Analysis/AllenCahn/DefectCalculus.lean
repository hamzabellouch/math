import OAI.Analysis.AllenCahn.Modica

namespace OAI

noncomputable section
namespace DeGiorgi
open MeasureTheory
open scoped ENNReal
open Filter Topology

lemma regularized_inverse_lipschitz_gt_one {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hb : ∀ x, v x ∈ Set.Icc (-1 : ℝ) 1)
    (hAC : AllenCahn v) {r L : ℝ} (hr : 0 < r) (hr1 : r < 1) (hL : 1 < L) :
    ∀ x y, inverseProfile (fun z => r * v z) y - inverseProfile (fun z => r * v z) x ≤
      L * ‖y - x‖ := by
  have hreg : ContDiff ℝ 2 (fun y => r * v y) := contDiff_const.mul hv
  have hic (y : Space n) : r * v y ∈ Set.Icc (-r) r := by
    have H := mul_le_mul_of_nonneg_left (hb y).1 hr.le
    have H' := mul_le_mul_of_nonneg_left (hb y).2 hr.le
    constructor <;> nlinarith
  have hi (y : Space n) : r * v y ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [(hic y).1], by linarith [(hic y).2]⟩
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hqr : 0 < 1 - r ^ 2 := weight_pos ⟨by linarith, hr1⟩
  have hL2 : 0 < L ^ 2 - 1 := by nlinarith
  let B := Real.sqrt 2 * r
  let M := Real.sqrt 2 * max |Real.artanh (-r)| |Real.artanh r|
  let κ := (L ^ 2 - 1) * (1 - r ^ 2)
  let b : Space n → ℝ := fun x => Real.sqrt 2 * (r * v x)
  let h : Space n → ℝ := fun x => -Real.sqrt 2 * (r * v x) +
    Real.sqrt 2 * (1 - r ^ 2) / r ^ 2 * ((r * v x) ^ 3 / (1 - (r * v x) ^ 2))
  apply lipschitz_of_laplacian_monotonicity
    (b := b) (h := h) (M := M) (B := B) (κ := κ)
    (inverseProfile_contDiff hreg hi) (by dsimp [M]; positivity) (by dsimp [B]; positivity)
    (by linarith) (mul_pos hL2 hqr)
  · intro x
    exact inverseProfile_scalar_bound hr hr1 (hic x)
  · intro x
    dsimp [b, B]
    rw [abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr (hic x)) hs.le
  · intro x
    exact laplacian_regularized_inverse hv hb hAC hr hr1 x
  · intro x y hxy
    have ha : Real.artanh (r * v x) ≤ Real.artanh (r * v y) :=
      by
      change Real.sqrt 2 * Real.artanh (r * v x) ≤ Real.sqrt 2 * Real.artanh (r * v y) at hxy
      nlinarith only [hxy, hs]
    have ht : r * v x ≤ r * v y := (Real.strictMonoOn_artanh.le_iff_le (hi x) (hi y)).mp ha
    have H := inverseProfile_scalar_quantitative hr hr1 (hic x) (hic y) ht
    have H' := mul_le_mul_of_nonneg_left H hL2.le
    have HH := cube_div_weight_monotone (hi x) (hi y) ht
    have hc : 0 ≤ Real.sqrt 2 * (1 - r ^ 2) / r ^ 2 := by positivity
    have HH' := mul_le_mul_of_nonneg_left HH hc
    dsimp [κ, b, h, inverseProfile] at *
    nlinarith

lemma regularized_inverse_lipschitz {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hb : ∀ x, v x ∈ Set.Icc (-1 : ℝ) 1)
    (hAC : AllenCahn v) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (x y : Space n) :
    |inverseProfile (fun z => r * v z) y - inverseProfile (fun z => r * v z) x| ≤ ‖y - x‖ := by
  have H (a c : Space n) : inverseProfile (fun z => r * v z) c -
      inverseProfile (fun z => r * v z) a ≤ ‖c - a‖ := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hh := regularized_inverse_lipschitz_gt_one hv hb hAC hr hr1
      (show 1 < 1 + ε / (‖c - a‖ + 1) from lt_add_of_pos_right 1 (div_pos hε (by positivity))) a c
    have hn := norm_nonneg (c - a)
    have hratio : ε / (‖c - a‖ + 1) * ‖c - a‖ ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  apply abs_le.mpr
  constructor
  · have hh := H y x
    rw [norm_sub_rev x y] at hh
    linarith
  · exact H x y

lemma regularized_inverse_gradient_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hb : ∀ x, v x ∈ Set.Icc (-1 : ℝ) 1)
    (hAC : AllenCahn v) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (x : Space n) :
    ‖gradient (inverseProfile (fun z => r * v z)) x‖ ≤ 1 := by
  have H := norm_fderiv_le_of_lip' ℝ (f := inverseProfile (fun z => r * v z))
    (x₀ := x) (show (0 : ℝ) ≤ 1 by norm_num)
    (Filter.Eventually.of_forall (fun y => by
      simpa only [Real.norm_eq_abs, one_mul] using regularized_inverse_lipschitz hv hb hAC hr hr1 x y))
  simpa only [gradient, LinearIsometryEquiv.norm_map] using H

theorem modica_linear {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hb : ∀ x, v x ∈ Set.Icc (-1 : ℝ) 1)
    (hAC : AllenCahn v) (x : Space n) :
    Real.sqrt 2 * ‖gradient v x‖ ≤ 1 - v x ^ 2 := by
  have H (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
      Real.sqrt 2 * r * ‖gradient v x‖ ≤ 1 - (r * v x) ^ 2 := by
    have hi : r * v x ∈ Set.Ioo (-1 : ℝ) 1 := by
      have ha := mul_le_mul_of_nonneg_left (hb x).1 hr.1.le
      have hb' := mul_le_mul_of_nonneg_left (hb x).2 hr.1.le
      constructor <;> nlinarith [hr.2]
    have hq := weight_pos hi
    have hd : DifferentiableAt ℝ (fun z => r * v z) x :=
      (hv.differentiable (by norm_num) x).const_mul r
    have hg : gradient (fun z => r * v z) x = r • gradient v x := by
      simp [gradient, fderiv_const_mul (hv.differentiable (by norm_num) x)]
    have hh := regularized_inverse_gradient_bound hv hb hAC hr.1 hr.2 x
    rw [gradient_inverseProfile hd hi, hg, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr.1] at hh
    have hcoeff : 0 ≤ Real.sqrt 2 / defectWeight (fun z => r * v z) x := by
      exact div_nonneg (Real.sqrt_nonneg _) hq.le
    rw [abs_of_nonneg hcoeff] at hh
    dsimp [defectWeight] at hh
    rw [div_mul_eq_mul_div, div_le_iff₀ hq] at hh
    nlinarith
  have hc : IsClosed {r : ℝ | Real.sqrt 2 * r * ‖gradient v x‖ ≤ 1 - (r * v x) ^ 2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hsub : closure (Set.Ioo (0 : ℝ) 1) ⊆
      {r : ℝ | Real.sqrt 2 * r * ‖gradient v x‖ ≤ 1 - (r * v x) ^ 2} :=
    closure_minimal H hc
  have hmem : (1 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨zero_le_one, le_rfl⟩
  simpa using hsub hmem

theorem modica {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hb : ∀ x, v x ∈ Set.Icc (-1 : ℝ) 1)
    (hAC : AllenCahn v) (x : Space n) :
    ‖gradient v x‖ ^ 2 / 2 ≤ potential (v x) := by
  have H := modica_linear hv hb hAC x
  have hs := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) H 2
  rw [mul_pow, Real.sq_sqrt (by norm_num)] at hs
  dsimp [potential]
  linarith

theorem diffuseDefect_nonneg {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hAC : AllenCahn v) (x : Space n) : 0 ≤ diffuseDefect v x := by
  have hb (y : Space n) : v y ∈ Set.Icc (-1 : ℝ) 1 := ⟨(hi y).1.le, (hi y).2.le⟩
  have hq : 0 < defectWeight v x := weight_pos (hi x)
  have hnorm : ‖gradient (inverseProfile v) x‖ ≤ 1 := by
    rw [gradient_inverseProfile (hv.differentiable (by norm_num) x) (hi x), norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hq.le),
      div_mul_eq_mul_div, div_le_iff₀ hq]
    simpa only [one_mul, defectWeight] using modica_linear hv hb hAC x
  dsimp [diffuseDefect]
  nlinarith [norm_nonneg (gradient (inverseProfile v) x)]

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open MeasureTheory
open scoped ENNReal
open Filter Topology
open scoped ContDiff

lemma smooth_C2 {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)

lemma coordDeriv_smooth {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin n) : ContDiff ℝ ∞ (coordDeriv f i) := by
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma coordDeriv_sum {n : ℕ} {ι : Type*} (s : Finset ι) {f : ι → Space n → ℝ}
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (j : Fin n) (x : Space n) :
    coordDeriv (fun y => ∑ i ∈ s, f i y) j x = ∑ i ∈ s, coordDeriv (f i) j x := by
  simp only [coordDeriv, fderiv_fun_sum (fun i hi => hf i hi x), sum_apply]

lemma coordDeriv_comm {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (i j : Fin n) : coordDeriv (coordDeriv f i) j = coordDeriv (coordDeriv f j) i := by
  funext x
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp : minSmoothness ℝ 2 ≤ (2 : ℕ∞ω))
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  change fderiv ℝ (fun y => fderiv ℝ f y (basis n i)) x (basis n j) =
    fderiv ℝ (fun y => fderiv ℝ f y (basis n j)) x (basis n i)
  simp [fderiv_clm_apply hd (differentiableAt_const _)]
  exact hs _ _

lemma laplacian_coordDeriv {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin n) (x : Space n) :
    Laplacian.laplacian (coordDeriv f i) x = coordDeriv (Laplacian.laplacian f) i x := by
  have hf2 := smooth_C2 hf
  have he : Laplacian.laplacian f = fun y => ∑ j : Fin n, coordDeriv (coordDeriv f j) j y :=
    funext (laplacian_eq_sum_coordDeriv hf2)
  rw [laplacian_eq_sum_coordDeriv (smooth_C2 (coordDeriv_smooth hf i)), he,
    coordDeriv_sum _ (fun j _ => (coordDeriv_smooth (coordDeriv_smooth hf j) j).differentiable (by simp))]
  apply Finset.sum_congr rfl
  intro j _
  rw [coordDeriv_comm hf2 i j,
    coordDeriv_comm (smooth_C2 (coordDeriv_smooth hf j)) i j]

lemma laplacian_sum {n : ℕ} {ι : Type*} (s : Finset ι) {f : ι → Space n → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (x : Space n) :
    Laplacian.laplacian (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, Laplacian.laplacian (f i) x := by
  rw [laplacian_eq_sum_coordDeriv (ContDiff.sum (fun i hi => hf i hi))]
  have he (j : Fin n) : coordDeriv (fun y => ∑ i ∈ s, f i y) j =
      fun y => ∑ i ∈ s, coordDeriv (f i) j y :=
    funext (coordDeriv_sum s (fun i hi => (hf i hi).differentiable (by norm_num)) j)
  simp_rw [he]
  simp_rw [coordDeriv_sum _ (fun i hi => (coordDeriv_contDiff (hf i hi) _).differentiable (by norm_num))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact (laplacian_eq_sum_coordDeriv (hf i hi) x).symm

lemma laplacian_sq {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) (x : Space n) :
    Laplacian.laplacian (fun y => f y ^ 2) x =
      2 * ‖gradient f x‖ ^ 2 + 2 * f x * Laplacian.laplacian f x := by
  have hd := hf.differentiable (by norm_num)
  have hfirst (i : Fin n) : coordDeriv (fun y => f y ^ 2) i =
      fun y => 2 * f y * coordDeriv f i y := by
    funext y
    simp [coordDeriv, fderiv_fun_pow 2 (hd y), mul_assoc]
  have hsecond (i : Fin n) : coordDeriv (fun y => 2 * f y * coordDeriv f i y) i x =
      2 * (coordDeriv f i x) ^ 2 + 2 * f x * coordDeriv (coordDeriv f i) i x := by
    rw [coordDeriv_mul (hd.const_mul 2) ((coordDeriv_contDiff hf i).differentiable (by norm_num))]
    simp only [coordDeriv, fderiv_const_mul (hd x), smul_apply, smul_eq_mul]
    ring
  rw [laplacian_eq_sum_coordDeriv (hf.pow 2)]
  simp_rw [hfirst, hsecond]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← gradient_norm_sq, ← laplacian_eq_sum_coordDeriv hf]

lemma laplacian_gradient_norm_sq {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : Space n) :
    Laplacian.laplacian (fun y => ‖gradient f y‖ ^ 2) x =
      2 * (∑ i : Fin n, ‖gradient (coordDeriv f i) x‖ ^ 2) +
      2 * (∑ i : Fin n, coordDeriv f i x * coordDeriv (Laplacian.laplacian f) i x) := by
  have he : (fun y => ‖gradient f y‖ ^ 2) = fun y => ∑ i : Fin n, coordDeriv f i y ^ 2 :=
    funext (gradient_norm_sq f)
  rw [he, laplacian_sum _ (fun i _ => (smooth_C2 (coordDeriv_smooth hf i)).pow 2)]
  simp_rw [laplacian_sq (smooth_C2 (coordDeriv_smooth hf _)), laplacian_coordDeriv hf]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma inverseProfile_smooth {n : ℕ} {v : Space n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) : ContDiff ℝ ∞ (inverseProfile v) := by
  have hm (x : Space n) : 1 - v x ≠ 0 := ne_of_gt (sub_pos.mpr (hi x).2)
  have hp (x : Space n) : 1 + v x ≠ 0 := ne_of_gt (by linarith [(hi x).1])
  have hq : ContDiff ℝ ∞ (fun x => (1 + v x) / (1 - v x)) :=
    (contDiff_const.add hv).div (contDiff_const.sub hv) hm
  have hl : ContDiff ℝ ∞ (fun x => (Real.sqrt 2 / 2) * Real.log ((1 + v x) / (1 - v x))) :=
    contDiff_const.mul (hq.log (fun x => div_ne_zero (hp x) (hm x)))
  convert hl using 1
  funext x
  dsimp [inverseProfile]
  rw [Real.artanh_eq_half_log ⟨(hi x).1.le, (hi x).2.le⟩]
  ring

lemma gradient_norm_sq_smooth {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => ‖gradient f x‖ ^ 2) := by
  have he : (fun x => ‖gradient f x‖ ^ 2) = fun x => ∑ i : Fin n, coordDeriv f i x ^ 2 :=
    funext (gradient_norm_sq f)
  rw [he]
  exact ContDiff.sum (fun i _ => (coordDeriv_smooth hf i).pow 2)

lemma diffuseDefect_smooth {n : ℕ} {v : Space n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) : ContDiff ℝ ∞ (diffuseDefect v) :=
  contDiff_const.sub (gradient_norm_sq_smooth (inverseProfile_smooth hv hi))

lemma coordDeriv_profile {n : ℕ} {v : Space n → ℝ} (hv : Differentiable ℝ v)
    (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (i : Fin n) (x : Space n) :
    coordDeriv v i x = defectWeight v x / Real.sqrt 2 * coordDeriv (inverseProfile v) i x := by
  have hq : defectWeight v x ≠ 0 := ne_of_gt (weight_pos (hi x))
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  dsimp only [coordDeriv]
  rw [fderiv_inverseProfile (hv x) (hi x)]
  simp only [smul_apply, smul_eq_mul]
  field_simp

lemma inverseProfile_laplacian_eq {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hpde : AllenCahn v) (x : Space n) :
    Laplacian.laplacian (inverseProfile v) x = -Real.sqrt 2 * v x * diffuseDefect v x := by
  have hq : 0 < defectWeight v x := weight_pos (hi x)
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [laplacian_inverseProfile hv hi, hpde]
  dsimp only [diffuseDefect]
  rw [gradient_inverseProfile (hv.differentiable (by norm_num) x) (hi x), norm_smul,
    Real.norm_eq_abs, abs_of_pos (div_pos hs hq)]
  dsimp only [defectWeight] at *
  field_simp
  rw [Real.sq_sqrt (by norm_num)]
  ring

lemma inner_gradient_eq_sum {n : ℕ} (f g : Space n → ℝ) (x : Space n) :
    inner ℝ (gradient f x) (gradient g x) =
      ∑ i : Fin n, coordDeriv f i x * coordDeriv g i x := by
  have h := (basis n).sum_inner_mul_inner (gradient f x) (gradient g x)
  simpa only [coordDeriv, real_inner_comm, inner_gradient_left] using h.symm

lemma diffuseDefect_laplacian {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hpde : AllenCahn v) (x : Space n) :
    Laplacian.laplacian (diffuseDefect v) x =
      -2 * (∑ i : Fin n, ‖gradient (coordDeriv (inverseProfile v) i) x‖ ^ 2) +
      2 * Real.sqrt 2 * v x * inner ℝ (gradient (inverseProfile v) x) (gradient (diffuseDefect v) x) +
      2 * defectWeight v x * diffuseDefect v x * ‖gradient (inverseProfile v) x‖ ^ 2 := by
  have hU := inverseProfile_smooth hv hi
  have hD := diffuseDefect_smooth hv hi
  have hdv := hv.differentiable (by simp)
  have hdD := hD.differentiable (by simp)
  have he : Laplacian.laplacian (inverseProfile v) =
      fun y => -Real.sqrt 2 * v y * diffuseDefect v y :=
    funext (inverseProfile_laplacian_eq (smooth_C2 hv) hi hpde)
  have hd (i : Fin n) : coordDeriv (Laplacian.laplacian (inverseProfile v)) i x =
      -Real.sqrt 2 * v x * coordDeriv (diffuseDefect v) i x -
        defectWeight v x * diffuseDefect v x * coordDeriv (inverseProfile v) i x := by
    rw [he, coordDeriv_mul (hdv.const_mul _) hdD]
    have hh : coordDeriv (fun y => -Real.sqrt 2 * v y) i x =
      -Real.sqrt 2 * coordDeriv v i x := by
      simp [coordDeriv, fderiv_const_mul (hdv x)]
    rw [hh, coordDeriv_profile hdv hi]
    have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    field_simp
    ring
  have hsub : Laplacian.laplacian (diffuseDefect v) x =
      -Laplacian.laplacian (fun y => ‖gradient (inverseProfile v) y‖ ^ 2) x := by
    change Laplacian.laplacian ((fun _ : Space n => (1 : ℝ)) -
      (fun y => ‖gradient (inverseProfile v) y‖ ^ 2)) x = _
    rw [contDiff_const.contDiffAt.laplacian_sub (smooth_C2 (gradient_norm_sq_smooth hU)).contDiffAt,
      InnerProductSpace.laplacian_const]
    simp
  rw [hsub, laplacian_gradient_norm_sq hU]
  simp_rw [hd]
  rw [inner_gradient_eq_sum, gradient_norm_sq]
  have hsum : ∑ i : Fin n, coordDeriv (inverseProfile v) i x *
      (-Real.sqrt 2 * v x * coordDeriv (diffuseDefect v) i x -
        defectWeight v x * diffuseDefect v x * coordDeriv (inverseProfile v) i x) =
      -Real.sqrt 2 * v x * (∑ i : Fin n, coordDeriv (inverseProfile v) i x * coordDeriv (diffuseDefect v) i x) -
        defectWeight v x * diffuseDefect v x * (∑ i : Fin n, coordDeriv (inverseProfile v) i x ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  ring

lemma inverseProfile_gradient_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hAC : AllenCahn v) (x : Space n) : ‖gradient (inverseProfile v) x‖ ≤ 1 := by
  have h := diffuseDefect_nonneg hv hi hAC x
  dsimp only [diffuseDefect] at h
  nlinarith [norm_nonneg (gradient (inverseProfile v) x)]

lemma diffuseDrift_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hAC : AllenCahn v) (x : Space n) :
    ‖(2 * Real.sqrt 2 * v x) • gradient (inverseProfile v) x‖ ≤ 2 * Real.sqrt 2 := by
  have hvabs : |v x| ≤ 1 := abs_le.mpr ⟨(hi x).1.le, (hi x).2.le⟩
  rw [norm_smul, norm_mul, Real.norm_of_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)), Real.norm_eq_abs]
  calc 2 * Real.sqrt 2 * |v x| * ‖gradient (inverseProfile v) x‖ ≤
      2 * Real.sqrt 2 * 1 * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hvabs (by positivity))
        (inverseProfile_gradient_bound hv hi hAC x) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end DeGiorgi
end

end OAI
