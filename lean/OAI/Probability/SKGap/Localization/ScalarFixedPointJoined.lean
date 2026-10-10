import Mathlib
import OAI.Probability.SKGap.Gaussian.StandardGaussianProduct
import OAI.Probability.SKGap.Localization.ScalarParametersJoined

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKGap

theorem integrable_tanh {P : Measure ℝ} [IsFiniteMeasure P] : Integrable tanh P := by
  apply Integrable.of_bound continuous_tanh.aestronglyMeasurable 1
  exact ae_of_all _ (fun y => by simpa using (abs_tanh_lt_one y).le)

theorem integrable_tanh_sq {P : Measure ℝ} [IsFiniteMeasure P] :
    Integrable (fun y => tanh y ^ 2) P := by
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (tanh y))]
    using (tanh_sq_lt_one y).le)

def oddVariance (y : ℝ) : ℝ := tanh y * (1 - tanh y^2)

lemma abs_oddVariance_le_one (y : ℝ) : |oddVariance y| ≤ 1 := by
  have ht := (abs_tanh_lt_one y).le
  have hs := (tanh_sq_lt_one y).le
  dsimp [oddVariance]
  rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hs)]
  exact (mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr hs)).trans (by nlinarith [sq_nonneg (tanh y)])

lemma integrable_oddVariance {P : Measure ℝ} [IsFiniteMeasure P] :
    Integrable oddVariance P := by
  apply Integrable.of_bound (by unfold oddVariance; fun_prop) 1
  exact ae_of_all _ (fun y => by simpa using abs_oddVariance_le_one y)

lemma gaussianPDFReal_diagonal_factor {s : ℝ≥0} (hs : s ≠ 0) (y : ℝ) :
    gaussianPDFReal s s y =
      (1 / sqrt (2*π*s) * exp (-y^2/(2*s) - s/2)) * exp y := by
  have hs' : (s : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hs
  have he : -(y-(s:ℝ))^2/(2*s) = (-y^2/(2*s)-s/2)+y := by
    field_simp
    ring
  rw [gaussianPDFReal, he, exp_add]
  ring

lemma gaussianPDFReal_diagonal_symmetry {s : ℝ≥0} (hs : s ≠ 0) (y : ℝ) :
    gaussianPDFReal s s y - gaussianPDFReal s s (-y) =
      tanh y * (gaussianPDFReal s s y + gaussianPDFReal s s (-y)) := by
  rw [gaussianPDFReal_diagonal_factor hs y, gaussianPDFReal_diagonal_factor hs (-y)]
  rw [neg_sq, tanh_eq]
  have he : exp y + exp (-y) ≠ 0 := (add_pos (exp_pos _) (exp_pos _)).ne'
  field_simp

theorem gaussian_nishimori (s : ℝ≥0) :
    (∫ y, tanh y ∂gaussianReal s s) = (∫ y, tanh y^2 ∂gaussianReal s s) := by
  by_cases hs : s = 0
  · subst s
    simp
  have hi := (integrable_gaussian_iff hs).mp
    (integrable_tanh.sub (integrable_tanh_sq (P := gaussianReal s s)))
  set f : ℝ → ℝ := fun y => gaussianPDFReal s s y * (tanh y - tanh y^2)
  have hf : Integrable f := hi
  have hid (y : ℝ) : f y + f (-y) = 0 := by
    have hh := gaussianPDFReal_diagonal_symmetry hs y
    dsimp [f]
    rw [tanh_neg, neg_sq]
    nlinarith [congrArg (fun x => tanh y * x) hh]
  have hz : (∫ y, f y) + ∫ y, f (-y) = 0 := by
    rw [← integral_add hf hf.comp_neg]
    simp only [hid, integral_zero]
  rw [integral_neg_eq_self] at hz
  have h0 : ∫ y, f y = 0 := by linarith
  have hsub : ∫ y, tanh y - tanh y^2 ∂gaussianReal s s = 0 := by
    rw [integral_gaussianReal_eq_integral_smul hs]
    exact h0
  rw [integral_sub integrable_tanh integrable_tanh_sq] at hsub
  exact sub_eq_zero.mp hsub

lemma tanh_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ tanh x := by
  rw [tanh_eq]
  exact div_nonneg (sub_nonneg.mpr (exp_le_exp.mpr (by linarith))) (by positivity)

lemma tanh_nonpos_of_nonpos {x : ℝ} (hx : x ≤ 0) : tanh x ≤ 0 := by
  rw [tanh_eq]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (exp_le_exp.mpr (by linarith))) (by positivity)

lemma gaussianPDFReal_reflection_le {d : ℝ} (hd : 0 ≤ d) (s : ℝ≥0)
    {y : ℝ} (hy : 0 ≤ y) : gaussianPDFReal d s (-y) ≤ gaussianPDFReal d s y := by
  unfold gaussianPDFReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

theorem gaussian_odd_sign {d : ℝ} (hd : 0 ≤ d) (s : ℝ≥0) :
    0 ≤ ∫ y, oddVariance y ∂gaussianReal d s := by
  by_cases hs : s = 0
  · subst s
    simp only [gaussianReal_zero_var, integral_dirac]
    exact mul_nonneg (tanh_nonneg_of_nonneg hd) (sub_nonneg.mpr (tanh_sq_lt_one d).le)
  have hi := (integrable_gaussian_iff hs).mp (integrable_oddVariance (P := gaussianReal d s))
  set f : ℝ → ℝ := fun y => gaussianPDFReal d s y * oddVariance y
  have hf : Integrable f := hi
  have hodd (y : ℝ) : oddVariance (-y) = -oddVariance y := by
    simp [oddVariance, tanh_neg]
  have hid (y : ℝ) : 0 ≤ f y + f (-y) := by
    have he : f y + f (-y) = (gaussianPDFReal d s y - gaussianPDFReal d s (-y)) * oddVariance y := by
      dsimp [f]; rw [hodd]; ring
    rw [he]
    by_cases hy : 0 ≤ y
    · exact mul_nonneg (sub_nonneg.mpr (gaussianPDFReal_reflection_le hd s hy))
        (mul_nonneg (tanh_nonneg_of_nonneg hy) (sub_nonneg.mpr (tanh_sq_lt_one y).le))
    · have hy' : 0 ≤ -y := by linarith
      have hp := gaussianPDFReal_reflection_le hd s hy'
      rw [neg_neg] at hp
      apply mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hp)
      exact mul_nonpos_of_nonpos_of_nonneg (tanh_nonpos_of_nonpos (le_of_not_ge hy))
        (sub_nonneg.mpr (tanh_sq_lt_one y).le)
  have hn := MeasureTheory.integral_nonneg (μ := volume) (f := fun y : ℝ => f y + f (-y)) hid
  rw [integral_add hf hf.comp_neg, integral_neg_eq_self] at hn
  rw [integral_gaussianReal_eq_integral_smul hs]
  change 0 ≤ ∫ y, f y
  linarith

end SKGap

namespace SKGap
open Filter
open scoped Topology

lemma gaussianAverage_hasDerivAt_mean {f f' : ℝ → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ y, HasDerivAt f (f' y) y) {C C' : ℝ}
    (hb : ∀ y, ‖f y‖ ≤ C) (hb' : ∀ y, ‖f' y‖ ≤ C') (d s : ℝ) :
    HasDerivAt (fun d => gaussianAverage f d s) (gaussianAverage f' d s) d := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (s := univ) (x₀ := d)
    (F := fun d x => f (d+sqrt s*x)) (F' := fun d x => f' (d+sqrt s*x))
    (bound := fun _ => C') univ_mem
    (Eventually.of_forall (fun d => (by fun_prop : Continuous (fun x : ℝ => f (d+sqrt s*x))).aestronglyMeasurable))
    (integrable_gaussian_comp_of_bound hf hb d s)
    (by fun_prop)
    (ae_of_all _ (fun x d _ => hb' _))
    (integrable_const _)
    (ae_of_all _ (fun x d _ => by
      convert! (hd (d+sqrt s*x)).comp d ((hasDerivAt_id d).add_const (sqrt s*x)) using 1
      simp))).2

lemma gaussianAverage_tanh_mean_deriv (d s : ℝ) :
    HasDerivAt (fun d => gaussianAverage tanh d s)
      (gaussianAverage (fun y => 1-tanh y^2) d s) d := by
  apply gaussianAverage_hasDerivAt_mean continuous_tanh (by fun_prop) hasDerivAt_tanh
    (C := 1) (C' := 1)
  · intro y; simpa using (abs_tanh_lt_one y).le
  · intro y
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [tanh_sq_lt_one y, sq_nonneg (tanh y)]

lemma gaussianAverage_tanh_diff_deriv (d s : ℝ) :
    HasDerivAt (fun d => gaussianAverage (fun y => tanh y-tanh y^2) d s)
      (gaussianAverage (fun y => (1-tanh y^2)*(1-2*tanh y)) d s) d := by
  apply gaussianAverage_hasDerivAt_mean (by fun_prop) (by fun_prop)
    (C := 2) (C' := 3)
  · intro y
    convert! (hasDerivAt_tanh y).sub ((hasDerivAt_tanh y).pow 2) using 1
    ring
  · intro y
    calc
      ‖tanh y-tanh y^2‖ ≤ ‖tanh y‖+‖tanh y^2‖ := norm_sub_le _ _
      _ ≤ 2 := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (tanh y))]
        linarith [(abs_tanh_lt_one y).le, (tanh_sq_lt_one y).le]
  · intro y
    rw [norm_mul]
    have h1 : ‖1-tanh y^2‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith [tanh_sq_lt_one y, sq_nonneg (tanh y)]
    have h2 : ‖1-2*tanh y‖ ≤ 3 := by
      have ht := (abs_le.mp (abs_tanh_lt_one y).le)
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    exact (mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

end SKGap

namespace SKGap
open Filter
open scoped Topology

def gaussianF (s : ℝ) : ℝ := gaussianAverage tanh s s

lemma gaussianF_zero : gaussianF 0 = 0 := by simp [gaussianF, gaussianAverage]

lemma continuous_gaussianF : Continuous gaussianF :=
  (continuous_gaussianAverage continuous_tanh
    (fun y => by simpa using (abs_tanh_lt_one y).le)).comp (continuous_id.prodMk continuous_id)

lemma gaussianF_eq_square {s : ℝ} (hs : 0 ≤ s) :
    gaussianF s = gaussianAverage (fun y => tanh y^2) s s := by
  rw [gaussianF, gaussianAverage_eq_integral continuous_tanh s hs,
    gaussianAverage_eq_integral (by fun_prop) s hs]
  convert gaussian_nishimori s.toNNReal using 1 <;> rw [Real.coe_toNNReal _ hs]

lemma gaussianF_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ gaussianF s := by
  rw [gaussianF_eq_square hs]
  exact MeasureTheory.integral_nonneg (f := fun x => tanh (s+sqrt s*x)^2) (fun x => sq_nonneg _)

lemma gaussianF_raw_deriv {s : ℝ} (hs : 0 < s) :
    HasDerivAt gaussianF
      (∫ x, (1-tanh (s+sqrt s*x)^2)*(1+x/(2*sqrt s)) ∂gaussianReal 0 1) s := by
  let bound : ℝ → ℝ := fun x => 1+|x|/(2*sqrt (s/2))
  have hb : Integrable bound (gaussianReal 0 1) :=
    (integrable_const 1).add ((IsGaussian.integrable_id (μ := gaussianReal 0 1)).abs.div_const _)
  have hnorm (t x : ℝ) (ht : t ∈ Ioi (s/2)) :
      ‖(1-tanh (t+sqrt t*x)^2)*(1+x/(2*sqrt t))‖ ≤ bound x := by
    have ht0 : 0 < t := lt_trans (half_pos hs) ht
    have hsqrt : 0 < sqrt (s/2) := sqrt_pos.2 (half_pos hs)
    have htqrt : 0 < sqrt t := sqrt_pos.2 ht0
    have h1 : |1-tanh (t+sqrt t*x)^2| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [tanh_sq_lt_one (t+sqrt t*x), sq_nonneg (tanh (t+sqrt t*x))]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ 1*|1+x/(2*sqrt t)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ 1+|x|/(2*sqrt t) := by
        simpa only [one_mul, abs_one, abs_div, abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) htqrt)] using abs_add_le (1:ℝ) (x/(2*sqrt t))
      _ ≤ bound x := by
        dsimp [bound]
        gcongr
        exact ht.le
  have hder (t x : ℝ) (ht : t ∈ Ioi (s/2)) :
      HasDerivAt (fun t => tanh (t+sqrt t*x))
        ((1-tanh (t+sqrt t*x)^2)*(1+x/(2*sqrt t))) t := by
    have ht0 : 0 < t := lt_trans (half_pos hs) ht
    convert! (hasDerivAt_tanh (t+sqrt t*x)).comp t
      ((hasDerivAt_id t).add ((hasDerivAt_sqrt ht0.ne').mul_const x)) using 1
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (s := Ioi (s/2)) (x₀ := s)
    (F := fun t x => tanh (t+sqrt t*x))
    (F' := fun t x => (1-tanh (t+sqrt t*x)^2)*(1+x/(2*sqrt t)))
    (bound := bound) (Ioi_mem_nhds (half_lt_self hs))
    (Eventually.of_forall (fun t => (by fun_prop : Continuous (fun x : ℝ => tanh (t+sqrt t*x))).aestronglyMeasurable))
    (integrable_gaussian_comp_of_bound continuous_tanh (fun y => by simpa using (abs_tanh_lt_one y).le) s s)
    (by fun_prop)
    (ae_of_all _ (fun x t ht => hnorm t x ht)) hb
    (ae_of_all _ (fun x t ht => hder t x ht))).2

lemma gaussian_diagonal_stein (s : ℝ) :
    (∫ x, x*(1-tanh (s+sqrt s*x)^2) ∂gaussianReal 0 1) =
      -2*sqrt s * (∫ x, oddVariance (s+sqrt s*x) ∂gaussianReal 0 1) := by
  have hv (x : ℝ) : ‖1-tanh (s+sqrt s*x)^2‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [tanh_sq_lt_one (s+sqrt s*x), sq_nonneg (tanh (s+sqrt s*x))]
  have hi : Integrable (fun x => 1-tanh (s+sqrt s*x)^2) (gaussianReal 0 1) :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ hv)
  have hid : Integrable (fun x => -2*sqrt s*oddVariance (s+sqrt s*x)) (gaussianReal 0 1) :=
    (integrable_gaussian_comp_of_bound (by unfold oddVariance; fun_prop)
      (fun y => by simpa using abs_oddVariance_le_one y) s s).const_mul _
  have hxi : Integrable (fun x => (x-0)*(1-tanh (s+sqrt s*x)^2)) (gaussianReal 0 1) := by
    simpa only [sub_zero, id_eq] using
      (IsGaussian.integrable_id (μ := gaussianReal 0 1)).mul_bdd (c := 1) (by fun_prop) (ae_of_all _ hv)
  have hd (x : ℝ) : HasDerivAt (fun x => 1-tanh (s+sqrt s*x)^2)
      (-2*sqrt s*oddVariance (s+sqrt s*x)) x := by
    convert! (((hasDerivAt_tanh (s+sqrt s*x)).comp x
      (((hasDerivAt_id x).const_mul (sqrt s)).const_add s)).pow 2).const_sub 1 using 1
    dsimp [oddVariance]
    ring
  have h := gaussian_integration_by_parts (d := 0) (s := 1) (by norm_num) hd hi hid hxi
  simpa only [sub_zero, NNReal.coe_one, one_mul, integral_const_mul] using h

lemma gaussianF_deriv {s : ℝ} (hs : 0 < s) :
    HasDerivAt gaussianF (gaussianAverage (fun y => (1-tanh y^2)*(1-tanh y)) s s) s := by
  have h := gaussianF_raw_deriv hs
  convert! h using 1
  have hi := integrable_gaussian_comp_of_bound (f := fun y => 1-tanh y^2) (by fun_prop)
    (C := 1) (fun y => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith [tanh_sq_lt_one y, sq_nonneg (tanh y)]) s s
  have ho := integrable_gaussian_comp_of_bound (f := oddVariance) (by unfold oddVariance; fun_prop)
    (C := 1) (fun y => by simpa using abs_oddVariance_le_one y) s s
  have hxi : Integrable (fun x => x*(1-tanh (s+sqrt s*x)^2)) (gaussianReal 0 1) :=
    (IsGaussian.integrable_id (μ := gaussianReal 0 1)).mul_bdd (c := 1) (by fun_prop)
      (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith [tanh_sq_lt_one (s+sqrt s*x), sq_nonneg (tanh (s+sqrt s*x))]))
  have h1 : gaussianAverage (fun y => (1-tanh y^2)*(1-tanh y)) s s =
      (∫ x, 1-tanh (s+sqrt s*x)^2 ∂gaussianReal 0 1) -
        ∫ x, oddVariance (s+sqrt s*x) ∂gaussianReal 0 1 := by
    rw [← integral_sub hi ho]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by dsimp [oddVariance]; ring)
  rw [h1]
  have he (x : ℝ) : (1-tanh (s+sqrt s*x)^2)*(1+x/(2*sqrt s)) =
      (1-tanh (s+sqrt s*x)^2) + (x*(1-tanh (s+sqrt s*x)^2))/(2*sqrt s) := by ring
  simp_rw [he]
  rw [integral_add hi (hxi.div_const _), integral_div, gaussian_diagonal_stein]
  field_simp
  ring

lemma gaussianF_derivative_bounds {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ gaussianAverage (fun y => (1-tanh y^2)*(1-tanh y)) s s ∧
      gaussianAverage (fun y => (1-tanh y^2)*(1-tanh y)) s s ≤ 1 := by
  have hm (y : ℝ) : 0 ≤ (1-tanh y^2)*(1-tanh y) :=
    mul_nonneg (sub_nonneg.mpr (tanh_sq_lt_one y).le)
      (sub_nonneg.mpr (le_trans (le_abs_self _) (abs_tanh_lt_one y).le))
  constructor
  · exact MeasureTheory.integral_nonneg (f := fun x => (1-tanh (s+sqrt s*x)^2)*(1-tanh (s+sqrt s*x))) (fun x => hm _)
  · rw [gaussianAverage_eq_integral (by fun_prop) s hs]
    have he (y : ℝ) : (1-tanh y^2)*(1-tanh y) = (1-tanh y^2)-oddVariance y := by
      dsimp [oddVariance]; ring
    simp_rw [he]
    rw [integral_sub (f := fun y => 1-tanh y^2) (g := oddVariance)
      ((integrable_const 1).sub (integrable_tanh_sq (P := gaussianReal s s.toNNReal)))
      integrable_oddVariance,
      integral_sub (integrable_const 1) (integrable_tanh_sq (P := gaussianReal s s.toNNReal)), integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have ho := gaussian_odd_sign hs s.toNNReal
    have hq : 0 ≤ ∫ y, tanh y^2 ∂gaussianReal s s.toNNReal :=
      MeasureTheory.integral_nonneg (f := fun y => tanh y^2) (fun y => sq_nonneg _)
    linarith

end SKGap

namespace SKGap
open Filter
open scoped Topology

lemma gaussianF_lipschitz : LipschitzOnWith 1 gaussianF (Ici 0) := by
  have h : LipschitzOnWith 1 gaussianF (Ioi 0) :=
    Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun s hs => (gaussianF_deriv hs).differentiableAt)
      (fun s hs => by
        rw [(gaussianF_deriv hs).deriv]
        have hb := gaussianF_derivative_bounds hs.le
        exact_mod_cast (show ‖gaussianAverage (fun y => (1-tanh y^2)*(1-tanh y)) s s‖ ≤ 1 by
          rw [Real.norm_eq_abs, abs_of_nonneg hb.1]; exact hb.2))
      (convex_Ioi 0)
  simpa only [closure_Ioi] using LipschitzOnWith.closure continuous_gaussianF.continuousOn h

lemma gaussianF_le_self {s : ℝ} (hs : 0 ≤ s) : gaussianF s ≤ s := by
  have h := gaussianF_lipschitz.dist_le_mul s hs 0 (by simp)
  rw [gaussianF_zero, dist_zero_right, NNReal.coe_one, one_mul, dist_zero_right,
    Real.norm_eq_abs, abs_of_nonneg (gaussianF_nonneg hs), Real.norm_eq_abs, abs_of_nonneg hs] at h
  exact h

lemma gaussianF_le_one {s : ℝ} (hs : 0 ≤ s) : gaussianF s ≤ 1 := by
  rw [gaussianF_eq_square hs, gaussianAverage_eq_integral (by fun_prop) s hs]
  have h := integral_mono (integrable_tanh_sq (P := gaussianReal s s.toNNReal)) (integrable_const 1)
    (fun y => (tanh_sq_lt_one y).le)
  simpa using h

lemma gaussian_mean_lipschitz (s : ℝ) : LipschitzWith 1 (fun d => gaussianAverage tanh d s) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun d => (gaussianAverage_tanh_mean_deriv d s).differentiableAt)
  intro d
  rw [(gaussianAverage_tanh_mean_deriv d s).deriv]
  have hm (y : ℝ) : 0 ≤ 1-tanh y^2 ∧ 1-tanh y^2 ≤ 1 :=
    ⟨sub_nonneg.mpr (tanh_sq_lt_one y).le, by nlinarith [sq_nonneg (tanh y)]⟩
  have hlo : 0 ≤ gaussianAverage (fun y => 1-tanh y^2) d s :=
    MeasureTheory.integral_nonneg (f := fun x => 1-tanh (d+sqrt s*x)^2) (fun x => (hm _).1)
  have hhi : gaussianAverage (fun y => 1-tanh y^2) d s ≤ 1 := by
    have hi := integrable_gaussian_comp_of_bound (f := fun y => 1-tanh y^2) (by fun_prop)
      (C := 1) (fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hm y).1]; exact (hm y).2) d s
    have h := integral_mono hi (integrable_const 1) (fun x => (hm _).2)
    simpa [gaussianAverage] using h
  exact_mod_cast (show ‖gaussianAverage (fun y => 1-tanh y^2) d s‖ ≤ 1 by
    rw [Real.norm_eq_abs, abs_of_nonneg hlo]; exact hhi)

lemma gaussian_mean_zero (s : ℝ) : gaussianAverage tanh 0 s = 0 := by
  have hn : HasLaw (fun x : ℝ => -x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa only [neg_zero, Pi.neg_def, id_eq] using gaussianReal_neg (HasLaw.id (μ := gaussianReal 0 1))
  have h := hn.integral_comp (f := fun x => tanh (sqrt s*x)) (by fun_prop)
  simp only [Function.comp_def, mul_neg, tanh_neg, integral_neg] at h
  dsimp [gaussianAverage]
  simp only [zero_add]
  linarith

lemma gaussian_mean_fixed_nonneg {j t d s : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t)
    (hd : d = t+j*gaussianAverage tanh d s) : 0 ≤ d := by
  by_contra hh
  have hdneg : d < 0 := lt_of_not_ge hh
  have h := (gaussian_mean_lipschitz s).dist_le_mul d 0
  rw [gaussian_mean_zero, dist_zero_right, NNReal.coe_one, one_mul, dist_zero_right,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg hdneg] at h
  have hm := (abs_le.mp h).1
  have hmul := mul_le_mul_of_nonneg_left hm hj.le
  nlinarith

lemma gaussian_H_derivative_bounds {d s : ℝ} (hd : 0 ≤ d) (hs : 0 ≤ s) :
    -1 ≤ gaussianAverage (fun y => (1-tanh y^2)*(1-2*tanh y)) d s ∧
      gaussianAverage (fun y => (1-tanh y^2)*(1-2*tanh y)) d s ≤ 1 := by
  rw [gaussianAverage_eq_integral (by fun_prop) d hs]
  have he (y : ℝ) : (1-tanh y^2)*(1-2*tanh y) = (1-tanh y^2)-2*oddVariance y := by
    dsimp [oddVariance]; ring
  have hi : Integrable (fun y => (1-tanh y^2)*(1-2*tanh y)) (gaussianReal d s.toNNReal) := by
    simp_rw [he]
    exact ((integrable_const 1).sub integrable_tanh_sq).sub (integrable_oddVariance.const_mul 2)
  constructor
  · have hp (y : ℝ) : -1 ≤ (1-tanh y^2)*(1-2*tanh y) := by
      have hm := (abs_le.mp (abs_tanh_lt_one y).le)
      have hv : 0 ≤ 1-tanh y^2 := sub_nonneg.mpr (tanh_sq_lt_one y).le
      have h1 : -1 ≤ 1-2*tanh y := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hv
      nlinarith [sq_nonneg (tanh y)]
    have h := integral_mono (integrable_const (-1)) hi hp
    simpa using h
  · simp_rw [he]
    rw [integral_sub (f := fun y => 1-tanh y^2) (g := fun y => 2*oddVariance y)
      ((integrable_const 1).sub (integrable_tanh_sq (P := gaussianReal d s.toNNReal)))
      (integrable_oddVariance.const_mul 2),
      integral_sub (integrable_const 1) (integrable_tanh_sq (P := gaussianReal d s.toNNReal)),
      integral_const_mul, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have ho := gaussian_odd_sign hd s.toNNReal
    have hq : 0 ≤ ∫ y, tanh y^2 ∂gaussianReal d s.toNNReal :=
      MeasureTheory.integral_nonneg (f := fun y => tanh y^2) (fun y => sq_nonneg _)
    linarith

lemma gaussian_H_lipschitz {s : ℝ} (hs : 0 ≤ s) :
    LipschitzOnWith 1 (fun d => gaussianAverage (fun y => tanh y-tanh y^2) d s) (Ici 0) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun d _ => (gaussianAverage_tanh_diff_deriv d s).differentiableAt) _ (convex_Ici 0)
  intro d hd
  rw [(gaussianAverage_tanh_diff_deriv d s).deriv]
  exact_mod_cast (show ‖gaussianAverage (fun y => (1-tanh y^2)*(1-2*tanh y)) d s‖ ≤ 1 by
    rw [Real.norm_eq_abs, abs_le]; exact gaussian_H_derivative_bounds hd hs)

lemma gaussian_H_diagonal_zero {s : ℝ} (hs : 0 ≤ s) :
    gaussianAverage (fun y => tanh y-tanh y^2) s s = 0 := by
  rw [gaussianAverage_eq_integral (by fun_prop) s hs,
    integral_sub integrable_tanh integrable_tanh_sq]
  have he := gaussian_nishimori s.toNNReal
  rw [Real.coe_toNNReal _ hs] at he
  exact sub_eq_zero.mpr he

lemma consistent_gaussian_diagonal {j t d : ℝ} {s : ℝ≥0}
    (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t)
    (hd : d = t+j*(∫ y, tanh y ∂gaussianReal d s))
    (hs : (s:ℝ) = t+j*(∫ y, tanh y^2 ∂gaussianReal d s)) : d = s := by
  have he (f : ℝ → ℝ) (hf : Continuous f) : gaussianAverage f d s = ∫ y, f y ∂gaussianReal d s := by
    simpa only [Real.toNNReal_coe] using gaussianAverage_eq_integral hf d s.coe_nonneg
  have hd0 := gaussian_mean_fixed_nonneg hj hj1 ht (hd.trans (by rw [he tanh continuous_tanh]))
  have h := (gaussian_H_lipschitz s.coe_nonneg).dist_le_mul d hd0 s s.coe_nonneg
  rw [gaussian_H_diagonal_zero s.coe_nonneg, dist_zero_right, NNReal.coe_one, one_mul,
    Real.norm_eq_abs, Real.dist_eq] at h
  have hdiff : d-(s:ℝ) = j*gaussianAverage (fun y => tanh y-tanh y^2) d s := by
    rw [he _ (by fun_prop), integral_sub integrable_tanh integrable_tanh_sq]
    linarith
  have ha := congrArg abs hdiff
  rw [abs_mul, abs_of_pos hj] at ha
  have hh : |gaussianAverage (fun y => tanh y-tanh y^2) d s| = 0 := by
    nlinarith [abs_nonneg (gaussianAverage (fun y => tanh y-tanh y^2) d s)]
  have hz := abs_eq_zero.mp hh
  rw [hz, mul_zero] at hdiff
  exact sub_eq_zero.mp hdiff

end SKGap

namespace SKGap

lemma gaussianF_pos {s : ℝ} (hs : 0 < s) : 0 < gaussianF s := by
  rw [gaussianF_eq_square hs.le, gaussianAverage_eq_integral (by fun_prop) s hs.le]
  have hv : s.toNNReal ≠ 0 := by exact_mod_cast (show 0 < s.toNNReal from Real.toNNReal_pos.mpr hs).ne'
  have := nullSingletonClass_gaussianReal (μ := s) hv
  have hsupp : Function.support (fun y : ℝ => tanh y ^ 2) = ({0} : Set ℝ)ᶜ := by
    ext y
    simp only [Function.mem_support, mem_compl_iff, mem_singleton_iff, ne_eq, sq_eq_zero_iff]
    have he : tanh y = 0 ↔ y = 0 := by
      simpa only [tanh_zero] using (show tanh y = tanh 0 ↔ y = 0 from tanh_injective.eq_iff)
    exact not_congr he
  rw [integral_pos_iff_support_of_nonneg (fun y => sq_nonneg (tanh y)) integrable_tanh_sq,
    hsupp, measure_compl (measurableSet_singleton 0) (by simp)]
  simp

lemma gaussian_fixed_unique {j t s r : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hes : s = t+j*gaussianF s)
    (her : r = t+j*gaussianF r) : s = r := by
  have h := gaussianF_lipschitz.dist_le_mul s hs r hr
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
  have he : |s-r| = j*|gaussianF s-gaussianF r| := by
    have he' : s-r = j*(gaussianF s-gaussianF r) := by linarith
    rw [he', abs_mul, abs_of_pos hj]
  have hz : |s-r| = 0 := by nlinarith [abs_nonneg (s-r), abs_nonneg (gaussianF s-gaussianF r)]
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

lemma exists_gaussian_fixed {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    ∃! s : ℝ, 0 ≤ s ∧ s = t+j*gaussianF s := by
  let g : ℝ → ℝ := fun s => s-t-j*gaussianF s
  have hg : Continuous g := (continuous_id.sub continuous_const).sub (continuous_const.mul continuous_gaussianF)
  have hl : g t ≤ 0 := by dsimp [g]; nlinarith [gaussianF_nonneg ht]
  have hu : 0 ≤ g (t+j) := by dsimp [g]; nlinarith [gaussianF_le_one (by linarith : 0 ≤ t+j)]
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc (by linarith : t ≤ t+j) hg.continuousOn ⟨hl, hu⟩
  have hs0 : 0 ≤ s := le_trans ht hs.1
  have hes : s = t+j*gaussianF s := by change s-t-j*gaussianF s = 0 at he; linarith
  refine ⟨s, ⟨hs0, hes⟩, ?_⟩
  intro r hr
  exact gaussian_fixed_unique hj hj1 hr.1 hs0 hr.2 hes

def scalarFixedPoint (j t : ℝ) : ℝ :=
  if h : 0 < j ∧ j < 1 ∧ 0 ≤ t then (exists_gaussian_fixed h.1 h.2.1 h.2.2).choose else 0

lemma scalarFixedPoint_spec {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    0 ≤ scalarFixedPoint j t ∧ scalarFixedPoint j t = t+j*gaussianF (scalarFixedPoint j t) := by
  simp only [scalarFixedPoint, dite_eq_left (show 0 < j ∧ j < 1 ∧ 0 ≤ t from ⟨hj, hj1, ht⟩)]
  exact (exists_gaussian_fixed hj hj1 ht).choose_spec.1

lemma scalarFixedPoint_bounds {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    t ≤ scalarFixedPoint j t ∧ scalarFixedPoint j t ≤ t/(1-j) := by
  obtain ⟨hs, he⟩ := scalarFixedPoint_spec hj hj1 ht
  constructor
  · nlinarith [gaussianF_nonneg hs]
  · apply (le_div_iff₀ (by linarith : 0 < 1-j)).mpr
    nlinarith [gaussianF_le_self hs]

lemma scalarFixedPoint_zero {j : ℝ} (hj : 0 < j) (hj1 : j < 1) : scalarFixedPoint j 0 = 0 := by
  obtain ⟨hl, hu⟩ := scalarFixedPoint_bounds hj hj1 (le_refl 0)
  simp only [zero_div] at hu
  exact le_antisymm hu hl

lemma scalarFixedPoint_lipschitz {j t u : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (ht : 0 ≤ t) (hu : 0 ≤ u) :
    |scalarFixedPoint j t-scalarFixedPoint j u| ≤ 1/(1-j)*|t-u| := by
  obtain ⟨hst, het⟩ := scalarFixedPoint_spec hj hj1 ht
  obtain ⟨hsu, heu⟩ := scalarFixedPoint_spec hj hj1 hu
  have h := gaussianF_lipschitz.dist_le_mul _ hst _ hsu
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
  have htri : |scalarFixedPoint j t-scalarFixedPoint j u| ≤
      |t-u|+j*|gaussianF (scalarFixedPoint j t)-gaussianF (scalarFixedPoint j u)| := by
    calc
      _ = |(t-u)+j*(gaussianF (scalarFixedPoint j t)-gaussianF (scalarFixedPoint j u))| := by congr 1; linarith
      _ ≤ |t-u|+|j*(gaussianF (scalarFixedPoint j t)-gaussianF (scalarFixedPoint j u))| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_pos hj]
  rw [one_div, inv_mul_eq_div]
  apply (le_div_iff₀ (by linarith : 0 < 1-j)).mpr
  nlinarith

lemma consistent_gaussian_unique {j t d : ℝ} {s : ℝ≥0}
    (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t)
    (hd : d = t+j*(∫ y, tanh y ∂gaussianReal d s))
    (hs : (s:ℝ) = t+j*(∫ y, tanh y^2 ∂gaussianReal d s)) :
    d = scalarFixedPoint j t ∧ (s:ℝ) = scalarFixedPoint j t := by
  have hds := consistent_gaussian_diagonal hj hj1 ht hd hs
  have he : (s:ℝ) = t+j*gaussianF s := by
    rw [hds] at hd
    rw [gaussianF, gaussianAverage_eq_integral continuous_tanh _ s.coe_nonneg,
      Real.toNNReal_coe]
    exact hd
  have hroot := scalarFixedPoint_spec hj hj1 ht
  have hh := gaussian_fixed_unique hj hj1 s.coe_nonneg hroot.1 he hroot.2
  exact ⟨hds.trans hh, hh⟩

def scalarQ (j t : ℝ) : ℝ := gaussianF (scalarFixedPoint j t)

lemma scalarQ_spec {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    scalarQ j t = (∫ y, tanh y^2 ∂gaussianReal (scalarFixedPoint j t) (scalarFixedPoint j t).toNNReal) ∧
      scalarQ j t = (scalarFixedPoint j t-t)/j ∧ scalarQ j t ≤ t/(1-j) := by
  obtain ⟨hs, he⟩ := scalarFixedPoint_spec hj hj1 ht
  refine ⟨?_, ?_, ?_⟩
  · exact (gaussianF_eq_square hs).trans (gaussianAverage_eq_integral (by fun_prop) _ hs)
  · dsimp [scalarQ]; apply (eq_div_iff hj.ne').mpr; nlinarith
  · exact (gaussianF_le_self hs).trans (scalarFixedPoint_bounds hj hj1 ht).2

lemma scalar_fixed_pos {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 < t) :
    0 < scalarFixedPoint j t ∧ 0 < scalarQ j t := by
  have hs := ht.trans_le (scalarFixedPoint_bounds hj hj1 ht.le).1
  exact ⟨hs, gaussianF_pos hs⟩

end SKGap
end
end

end OAI
