import Mathlib

namespace OAI

/-! Modulo-twelve cardinal functions and Gaussian-damped radial Schwartz realization. -/

noncomputable section
open scoped BigOperators Topology FourierTransform SchwartzMap ComplexConjugate
open MeasureTheory Set Filter

namespace Triangular

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def b : ℝ := Real.sqrt 3 / 2

def h : ℝ := 2 / 5

def L : Finset ℤ := {0, 1, 3, 4, 7, 9}

def zeroSet : Set ℝ :=
  {s | ∃ j : ℤ, ∃ a : ℤ, a ∈ L ∧ s = 12 * (j : ℝ) + (a : ℝ)}

def nodes : Set ℝ := zeroSet ∩ Set.Ioi 0

def T (k : ℝ) (s : ℝ) : ℝ := k⁻¹ * Real.exp (-k * (s - 1))

def IsRadial (f : Plane → ℝ) : Prop :=
  ∀ x y : Plane, ‖x‖ = ‖y‖ → f x = f y

def realFourier (f : Plane → ℝ) : Plane → ℂ :=
  𝓕 (fun x : Plane => (f x : ℂ))

lemma b_pos : 0 < b := by
  unfold b
  positivity

lemma h_pos : 0 < h := by norm_num [h]

lemma b_sq : b ^ 2 = 3 / 4 := by
  unfold b
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

lemma k_pos {k : ℝ} (hk : (59 : ℝ) / 25 ≤ k) : 0 < k := by linarith

lemma hasDerivAt_T {k : ℝ} (hk : k ≠ 0) (s : ℝ) :
    HasDerivAt (T k) (-Real.exp (-k * (s - 1))) s := by
  have hd := ((((hasDerivAt_id s).sub_const 1).const_mul (-k)).exp).const_mul k⁻¹
  convert! hd using 1
  simp only [id_eq, mul_one]
  field_simp

lemma deriv_T {k : ℝ} (hk : k ≠ 0) (s : ℝ) :
    deriv (T k) s = -Real.exp (-k * (s - 1)) :=
  (hasDerivAt_T hk s).deriv

lemma T_pos {k : ℝ} (hk : (59 : ℝ) / 25 ≤ k) (s : ℝ) : 0 < T k s :=
  mul_pos (inv_pos.mpr (k_pos hk)) (Real.exp_pos _)

lemma realFourier_eq_integral (f : Plane → ℝ) (ξ : Plane) :
    realFourier f ξ =
      ∫ x : Plane, (f x : ℂ) *
        Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (inner ℝ x ξ : ℂ)) := by
  rw [realFourier, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  rw [mul_comm]
  apply congrArg (fun z : ℂ => (f x : ℂ) * Complex.exp z)
  push_cast
  ring

lemma zero_mem_zeroSet : (0 : ℝ) ∈ zeroSet := by
  exact ⟨0, 0, by simp [L], by norm_num⟩

lemma twentyFour_mem_nodes : (24 : ℝ) ∈ nodes := by
  exact ⟨⟨2, 0, by simp [L], by norm_num⟩, by norm_num⟩

def nodes₀ : Set ℝ := {0} ∪ nodes

abbrev Node := {n : ℝ // n ∈ nodes₀}

lemma Node.mem_zeroSet (n : Node) : n.val ∈ zeroSet := by
  rcases n.property with hn | hn
  · rw [Set.mem_singleton_iff.mp hn]
    exact zero_mem_zeroSet
  · exact hn.1

namespace Cardinal

def sineFactor (a : ℤ) (s : ℂ) : ℂ :=
  2 * Complex.sin (((Real.pi / 12 : ℝ) : ℂ) * (s - (a : ℂ)))

def rootProduct (s : ℂ) : ℂ := ∏ a ∈ L, sineFactor a s

def P (s : ℂ) : ℂ := ∏ a ∈ L, (sineFactor a s) ^ 2

lemma P_eq_square (s : ℂ) : P s = rootProduct s ^ 2 := by
  simp only [P, rootProduct, Finset.prod_pow]

lemma sineFactor_add_twelve (a : ℤ) (s : ℂ) :
    sineFactor a (s + 12) = -sineFactor a s := by
  unfold sineFactor
  have he : ((Real.pi / 12 : ℝ) : ℂ) * (s + 12 - (a : ℂ)) =
      ((Real.pi / 12 : ℝ) : ℂ) * (s - (a : ℂ)) + (Real.pi : ℂ) := by
    push_cast
    ring
  rw [he, Complex.sin_add_pi]
  ring

lemma P_periodic : Function.Periodic P 12 := by
  intro s
  simp only [P, sineFactor_add_twelve, neg_sq]

lemma P_ofReal (s : ℝ) :
    P (s : ℂ) = ((∏ a ∈ L, (2 * Real.sin (Real.pi / 12 * (s - (a : ℝ)))) ^ 2 : ℝ) : ℂ) := by
  simp only [P, sineFactor, Complex.ofReal_prod, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_sin, Complex.ofReal_sub, Complex.ofReal_intCast,
    Complex.ofReal_ofNat]

lemma P_nonneg (s : ℝ) : 0 ≤ (P (s : ℂ)).re := by
  rw [P_ofReal]
  simp only [Complex.ofReal_re]
  exact Finset.prod_nonneg (fun _ _ => sq_nonneg _)

lemma differentiable_rootProduct : Differentiable ℂ rootProduct := by
  unfold rootProduct sineFactor
  fun_prop

lemma differentiable_P : Differentiable ℂ P := by
  unfold P sineFactor
  fun_prop

lemma rootProduct_zero {n : ℝ} (hn : n ∈ zeroSet) : rootProduct (n : ℂ) = 0 := by
  obtain ⟨j, a, ha, hn⟩ := hn
  apply Finset.prod_eq_zero ha
  have he : ((n : ℂ) - (a : ℂ)) = 12 * (j : ℂ) := by
    exact_mod_cast (show n - (a : ℝ) = 12 * (j : ℝ) by linarith)
  have hh : (((Real.pi / 12 : ℝ) : ℂ) * (12 * (j : ℂ))) =
      (j : ℂ) * (Real.pi : ℂ) := by push_cast; ring
  have hz : Complex.sin ((j : ℂ) * (Real.pi : ℂ)) = 0 := by
    have hh := congrArg Complex.ofReal (Real.sin_int_mul_pi j)
    simpa only [Complex.ofReal_zero, Complex.ofReal_sin, Complex.ofReal_mul,
      Complex.ofReal_intCast] using hh
  simp only [sineFactor, he, hh, hz, mul_zero]

lemma P_zero {n : ℝ} (hn : n ∈ zeroSet) : P (n : ℂ) = 0 := by
  rw [P_eq_square, rootProduct_zero hn]
  norm_num

lemma P_real_zero_iff (s : ℝ) : P (s : ℂ) = 0 ↔ s ∈ zeroSet := by
  constructor
  · intro hP
    rw [P_eq_square, sq_eq_zero_iff] at hP
    obtain ⟨a, ha, hz⟩ := Finset.prod_eq_zero_iff.mp hP
    have hs : Complex.sin (((Real.pi / 12 : ℝ) : ℂ) * ((s : ℂ) - a)) = 0 :=
      (mul_eq_zero.mp hz).resolve_left (by norm_num)
    obtain ⟨j, hj⟩ := Complex.sin_eq_zero_iff.mp hs
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have he : (Real.pi : ℂ) * ((s : ℂ) - (12 * (j : ℂ) + a)) = 0 := by
      push_cast at hj
      linear_combination 12 * hj
    have he' := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hpi)
    exact ⟨j, a, ha, by exact_mod_cast he'⟩
  · exact P_zero

lemma hasDerivAt_P_zero {n : ℝ} (hn : n ∈ zeroSet) :
    HasDerivAt P 0 (n : ℂ) := by
  have hd := (differentiable_rootProduct (n : ℂ)).hasDerivAt.pow 2
  have he : rootProduct ^ 2 = P := funext fun s => (P_eq_square s).symm
  simpa [he, rootProduct_zero hn] using hd

lemma deriv_P_zero {n : ℝ} (hn : n ∈ zeroSet) : deriv P (n : ℂ) = 0 :=
  (hasDerivAt_P_zero hn).deriv

lemma P_node (n : Node) : P (n.val : ℂ) = 0 := P_zero n.mem_zeroSet

lemma deriv_P_node (n : Node) : deriv P (n.val : ℂ) = 0 :=
  deriv_P_zero n.mem_zeroSet

def dBasis (n : Node) : ℂ → ℂ := dslope P (n.val : ℂ)

def cBasis (n : Node) : ℂ → ℂ := dslope (dBasis n) (n.val : ℂ)

lemma differentiable_dBasis (n : Node) : Differentiable ℂ (dBasis n) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr
    differentiable_P.differentiableOn

lemma differentiable_cBasis (n : Node) : Differentiable ℂ (cBasis n) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr
    (differentiable_dBasis n).differentiableOn

lemma dBasis_node (n : Node) : dBasis n (n.val : ℂ) = 0 := by
  simp [dBasis, dslope_same, deriv_P_node]

lemma dBasis_eq (n : Node) {s : ℂ} (hs : s ≠ (n.val : ℂ)) :
    dBasis n s = P s / (s - n.val) := by
  simp [dBasis, dslope_of_ne _ hs, slope_def_field, P_node]

lemma cBasis_eq (n : Node) {s : ℂ} (hs : s ≠ (n.val : ℂ)) :
    cBasis n s = P s / (s - n.val) ^ 2 := by
  rw [cBasis, dslope_of_ne _ hs, slope_def_field, dBasis_node,
    sub_zero, dBasis_eq n hs, div_div, pow_two]

lemma node_cast_ne {m n : Node} (hmn : m ≠ n) : (m.val : ℂ) ≠ (n.val : ℂ) := by
  intro hh
  exact hmn (Subtype.ext (Complex.ofReal_injective hh))

lemma dBasis_other {m n : Node} (hmn : m ≠ n) : dBasis n (m.val : ℂ) = 0 := by
  rw [dBasis_eq n (node_cast_ne hmn), P_node, zero_div]

lemma cBasis_other {m n : Node} (hmn : m ≠ n) : cBasis n (m.val : ℂ) = 0 := by
  rw [cBasis_eq n (node_cast_ne hmn), P_node, zero_div]

lemma mul_dBasis (n : Node) :
    (fun s : ℂ => (s - n.val) * dBasis n s) = P := by
  funext s
  simpa only [smul_eq_mul, P_node, sub_zero, dBasis] using
    sub_smul_dslope P (n.val : ℂ) s

lemma mul_cBasis (n : Node) :
    (fun s : ℂ => (s - n.val) * cBasis n s) = dBasis n := by
  funext s
  simpa only [smul_eq_mul, dBasis_node, sub_zero, cBasis] using
    sub_smul_dslope (dBasis n) (n.val : ℂ) s

lemma deriv_dBasis_other {m n : Node} (hmn : m ≠ n) :
    deriv (dBasis n) (m.val : ℂ) = 0 := by
  have hd := (((hasDerivAt_id (m.val : ℂ)).sub_const (n.val : ℂ)).mul
    ((differentiable_dBasis n (m.val : ℂ)).hasDerivAt)).deriv
  simp only [Pi.mul_def, id_eq] at hd
  rw [mul_dBasis] at hd
  simp only [deriv_P_node, dBasis_other hmn, mul_zero, zero_add] at hd
  exact (mul_eq_zero.mp hd.symm).resolve_left (sub_ne_zero.mpr (node_cast_ne hmn))

lemma deriv_cBasis_other {m n : Node} (hmn : m ≠ n) :
    deriv (cBasis n) (m.val : ℂ) = 0 := by
  have hd := (((hasDerivAt_id (m.val : ℂ)).sub_const (n.val : ℂ)).mul
    ((differentiable_cBasis n (m.val : ℂ)).hasDerivAt)).deriv
  simp only [Pi.mul_def, id_eq] at hd
  rw [mul_cBasis] at hd
  simp only [deriv_dBasis_other hmn, cBasis_other hmn, mul_zero, zero_add] at hd
  exact (mul_eq_zero.mp hd.symm).resolve_left (sub_ne_zero.mpr (node_cast_ne hmn))

lemma cBasis_node (n : Node) : cBasis n (n.val : ℂ) = deriv (dBasis n) (n.val : ℂ) := by
  exact dslope_same (dBasis n) (n.val : ℂ)

lemma P_conj (s : ℂ) : conj (P s) = P (conj s) := by
  simp only [P, sineFactor, map_prod, map_pow, map_mul, ← Complex.sin_conj,
    map_sub, Complex.conj_ofReal, map_ofNat, map_intCast]

lemma dslope_conj_real {f : ℂ → ℂ} (hf : ∀ s, conj (f s) = f (conj s))
    (r : ℝ) (s : ℂ) : conj (dslope f (r : ℂ) s) = dslope f (r : ℂ) (conj s) := by
  have he : conj ∘ f ∘ conj = f := by
    ext z
    simp only [Function.comp_apply, hf, RCLike.conj_conj]
  have hd := congrFun (deriv_conj_conj (f := f)) (r : ℂ)
  rw [he] at hd
  simp only [Function.comp_apply, Complex.conj_ofReal] at hd
  by_cases hs : s = (r : ℂ)
  · subst s
    simpa only [Complex.conj_ofReal, dslope_same] using hd.symm
  · have hc : conj s ≠ (r : ℂ) := by
      intro h
      apply hs
      have hh := congrArg conj h
      simpa using hh
    rw [dslope_of_ne _ hs, dslope_of_ne _ hc]
    simp only [slope_def_field, map_div₀, map_sub, hf, Complex.conj_ofReal]

lemma dBasis_conj (n : Node) (s : ℂ) :
    conj (dBasis n s) = dBasis n (conj s) :=
  dslope_conj_real P_conj n.val s

lemma cBasis_conj (n : Node) (s : ℂ) :
    conj (cBasis n s) = cBasis n (conj s) :=
  dslope_conj_real (dBasis_conj n) n.val s

lemma norm_two_sin_le (z : ℂ) : ‖2 * Complex.sin z‖ ≤ 2 * Real.exp |z.im| := by
  rw [Complex.two_sin, norm_mul, Complex.norm_I, mul_one]
  calc
    ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖ ≤
        ‖Complex.exp (-z * Complex.I)‖ + ‖Complex.exp (z * Complex.I)‖ := norm_sub_le _ _
    _ = Real.exp z.im + Real.exp (-z.im) := by simp [Complex.norm_exp]
    _ ≤ Real.exp |z.im| + Real.exp |z.im| :=
      add_le_add (Real.exp_le_exp.mpr (le_abs_self _))
        (Real.exp_le_exp.mpr (neg_le_abs _))
    _ = 2 * Real.exp |z.im| := by ring

def stripBound (R : ℝ) : ℝ := (2 * Real.exp (Real.pi * R / 12)) ^ 12

lemma stripBound_nonneg (R : ℝ) : 0 ≤ stripBound R := by
  unfold stripBound
  positivity

lemma P_strip_bound (R : ℝ) (s : ℂ) (hs : |s.im| ≤ R) : ‖P s‖ ≤ stripBound R := by
  unfold P sineFactor
  rw [norm_prod]
  calc
    ∏ a ∈ L, ‖(2 * Complex.sin (((Real.pi / 12 : ℝ) : ℂ) * (s - a))) ^ 2‖ ≤
        ∏ _a ∈ L, (2 * Real.exp (Real.pi * R / 12)) ^ 2 := by
      apply Finset.prod_le_prod₀ (by intros; positivity)
      intro a _
      rw [norm_pow]
      apply pow_le_pow_left₀ (norm_nonneg _)
      refine (norm_two_sin_le _).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply Real.exp_le_exp.mpr
      have he : ((((Real.pi / 12 : ℝ) : ℂ) * (s - a))).im =
          Real.pi * s.im / 12 := by simp [div_eq_mul_inv]; ring
      rw [he, abs_div, abs_mul, abs_of_pos Real.pi_pos]
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 12)]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs Real.pi_pos.le) (by norm_num)
    _ = stripBound R := by simp [stripBound, ← pow_mul, L]

lemma im_le_dist_real (w : ℂ) (n : ℝ) : |w.im| ≤ dist w (n : ℂ) := by
  simpa [dist_eq_norm] using Complex.abs_im_le_norm (w - (n : ℂ))

lemma uniform_basis_bound (R : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ (n : Node) (s : ℂ), |s.im| ≤ R → ‖cBasis n s‖ ≤ M ∧ ‖dBasis n s‖ ≤ M := by
  let A := max R 2
  let M := stripBound A
  have hM : 0 ≤ M := stripBound_nonneg A
  refine ⟨M, hM, ?_⟩
  intro n s hs
  have hmapP : Set.MapsTo P (Metric.ball (n.val : ℂ) 2)
      (Metric.closedBall (P (n.val : ℂ)) M) := by
    intro w hw
    simp only [Metric.mem_closedBall, P_node, dist_zero_right]
    exact P_strip_bound A w ((im_le_dist_real w n.val).trans
      ((Metric.mem_ball.mp hw).le.trans (le_max_right _ _)))
  have hd : ∀ w ∈ Metric.ball (n.val : ℂ) 2, ‖dBasis n w‖ ≤ M / 2 := by
    intro w hw
    exact Complex.norm_dslope_le_div_of_mapsTo_ball
      differentiable_P.differentiableOn hmapP hw
  have hmapD : Set.MapsTo (dBasis n) (Metric.ball (n.val : ℂ) 1)
      (Metric.closedBall (dBasis n (n.val : ℂ)) (M / 2)) := by
    intro w hw
    simp only [Metric.mem_closedBall, dBasis_node, dist_zero_right]
    apply hd w
    exact (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hw
  have hc : ∀ w ∈ Metric.ball (n.val : ℂ) 1, ‖cBasis n w‖ ≤ M / 2 := by
    intro w hw
    simpa [cBasis] using Complex.norm_dslope_le_div_of_mapsTo_ball
      (differentiable_dBasis n).differentiableOn hmapD hw
  have hPs : ‖P s‖ ≤ M := P_strip_bound A s (hs.trans (le_max_left _ _))
  have hhalf : M / 2 ≤ M := by linarith
  by_cases hnear : dist s (n.val : ℂ) < 1
  · exact ⟨(hc s hnear).trans hhalf,
      (hd s (lt_trans hnear (by norm_num : (1 : ℝ) < 2))).trans hhalf⟩
  · have hfar : 1 ≤ ‖s - (n.val : ℂ)‖ := by
      simpa [dist_eq_norm] using le_of_not_gt hnear
    have hne : s ≠ (n.val : ℂ) := by intro he; norm_num [he] at hfar
    rw [cBasis_eq n hne, dBasis_eq n hne, norm_div, norm_div, norm_pow]
    constructor
    · exact (div_le_self (norm_nonneg _) (one_le_pow₀ hfar)).trans hPs
    · exact (div_le_self (norm_nonneg _) hfar).trans hPs

structure Coefficients where
  C : ℝ
  c : Node → ℝ
  d : Node → ℝ
  summable : Summable (fun n => |c n| + |d n|)

def profile (a : Coefficients) (s : ℂ) : ℂ :=
  (a.C : ℂ) * P s +
    ∑' n : Node, ((a.c n : ℂ) * cBasis n s + (a.d n : ℂ) * dBasis n s)

lemma summand_norm_bound (a : Coefficients) {R M : ℝ}
    (hM : ∀ (n : Node) (s : ℂ), |s.im| ≤ R → ‖cBasis n s‖ ≤ M ∧ ‖dBasis n s‖ ≤ M)
    (n : Node) (s : ℂ) (hs : |s.im| ≤ R) :
    ‖(a.c n : ℂ) * cBasis n s + (a.d n : ℂ) * dBasis n s‖ ≤
      (|a.c n| + |a.d n|) * M := by
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |a.c n| * M + |a.d n| * M :=
      add_le_add (mul_le_mul_of_nonneg_left (hM n s hs).1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hM n s hs).2 (abs_nonneg _))
    _ = _ := by ring

lemma differentiable_profile (a : Coefficients) : Differentiable ℂ (profile a) := by
  intro s
  obtain ⟨M, hM, hB⟩ := uniform_basis_bound (|s.im| + 1)
  let U : Set ℂ := {w | |w.im| < |s.im| + 1}
  have hU : IsOpen U := isOpen_lt Complex.continuous_im.abs continuous_const
  have hs : s ∈ U := by dsimp [U]; linarith
  have hd : DifferentiableOn ℂ
      (fun w => ∑' n : Node, ((a.c n : ℂ) * cBasis n w + (a.d n : ℂ) * dBasis n w)) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm (a.summable.mul_right M)
    · intro n
      exact ((differentiable_cBasis n).const_mul _ |>.add
        ((differentiable_dBasis n).const_mul _)).differentiableOn
    · exact hU
    · intro n w hw
      exact summand_norm_bound a hB n w (le_of_lt hw)
  exact ((differentiable_P s).const_mul _).add (hd.differentiableAt (hU.mem_nhds hs))

lemma profile_strip (a : Coefficients) (R : ℝ) :
    ∃ M : ℝ, ∀ s : ℂ, |s.im| ≤ R → ‖profile a s‖ ≤ M := by
  obtain ⟨M, hM, hB⟩ := uniform_basis_bound R
  refine ⟨|a.C| * stripBound R + ∑' n : Node, (|a.c n| + |a.d n|) * M, ?_⟩
  intro s hs
  have hsum := (a.summable.mul_right M).of_norm_bounded
    (fun n => summand_norm_bound a hB n s hs)
  unfold profile
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left (P_strip_bound R s hs) (abs_nonneg a.C)
  · exact (norm_tsum_le_tsum_norm hsum.norm).trans
      (hsum.norm.tsum_le_tsum (fun n => summand_norm_bound a hB n s hs)
        (a.summable.mul_right M))

lemma profile_conj (a : Coefficients) (s : ℂ) :
    conj (profile a s) = profile a (conj s) := by
  simp only [profile, map_add, map_mul, Complex.conj_ofReal, P_conj,
    Complex.conj_tsum, cBasis_conj, dBasis_conj]

lemma profile_real (a : Coefficients) (s : ℝ) : (profile a (s : ℂ)).im = 0 := by
  have hh : conj (profile a (s : ℂ)) = profile a (s : ℂ) := by
    simpa only [Complex.conj_ofReal] using profile_conj a (s : ℂ)
  exact Complex.conj_eq_iff_im.mp hh

lemma profile_eq (a : Coefficients) (s : ℂ) (hs : ∀ n : Node, s ≠ (n.val : ℂ)) :
    profile a s = P s * ((a.C : ℂ) +
      ∑' n : Node, ((a.c n : ℂ) / (s - n.val) ^ 2 + (a.d n : ℂ) / (s - n.val))) := by
  simp_rw [profile, cBasis_eq _ (hs _), dBasis_eq _ (hs _)]
  rw [mul_add, ← tsum_mul_left]
  congr 1
  · ring
  · apply tsum_congr
    intro n
    ring

lemma deriv_profile (a : Coefficients) (s : ℂ) :
    deriv (profile a) s = (a.C : ℂ) * deriv P s +
      ∑' n : Node, ((a.c n : ℂ) * deriv (cBasis n) s +
        (a.d n : ℂ) * deriv (dBasis n) s) := by
  obtain ⟨M, hM, hB⟩ := uniform_basis_bound (|s.im| + 1)
  let U : Set ℂ := {w | |w.im| < |s.im| + 1}
  let F : Node → ℂ → ℂ := fun n w => (a.c n : ℂ) * cBasis n w + (a.d n : ℂ) * dBasis n w
  have hU : IsOpen U := isOpen_lt Complex.continuous_im.abs continuous_const
  have hs : s ∈ U := by dsimp [U]; linarith
  have hd (n : Node) : Differentiable ℂ (F n) :=
    ((differentiable_cBasis n).const_mul _).add ((differentiable_dBasis n).const_mul _)
  have hF (n : Node) (w : ℂ) (hw : w ∈ U) : ‖F n w‖ ≤ (|a.c n| + |a.d n|) * M :=
    summand_norm_bound a hB n w (le_of_lt hw)
  have hsum := Complex.hasSum_deriv_of_summable_norm (a.summable.mul_right M)
    (fun n => (hd n).differentiableOn) hU hF hs
  have hdiff := (Complex.differentiableOn_tsum_of_summable_norm (a.summable.mul_right M)
    (fun n => (hd n).differentiableOn) hU hF).differentiableAt (hU.mem_nhds hs)
  change deriv (fun z => (a.C : ℂ) * P z + ∑' n : Node, F n z) s = _
  rw [deriv_fun_add ((differentiable_P s).const_mul _) hdiff,
    deriv_const_mul _ (differentiable_P s), ← hsum.tsum_eq]
  congr 1
  apply tsum_congr
  intro n
  exact ((((differentiable_cBasis n s).hasDerivAt.const_mul (a.c n : ℂ)).add
    ((differentiable_dBasis n s).hasDerivAt.const_mul (a.d n : ℂ))).deriv)

lemma profile_node (a : Coefficients) (n : Node) :
    profile a (n.val : ℂ) = (a.c n : ℂ) * cBasis n (n.val : ℂ) := by
  classical
  simp only [profile, P_node, mul_zero, zero_add]
  rw [tsum_eq_single n]
  · simp only [dBasis_node, mul_zero, add_zero]
  · intro m hmn
    simp only [cBasis_other hmn.symm, dBasis_other hmn.symm, mul_zero, add_zero]

lemma deriv_profile_node (a : Coefficients) (n : Node) :
    deriv (profile a) (n.val : ℂ) =
      (a.c n : ℂ) * deriv (cBasis n) (n.val : ℂ) +
        (a.d n : ℂ) * cBasis n (n.val : ℂ) := by
  classical
  rw [deriv_profile, deriv_P_node, mul_zero, zero_add, tsum_eq_single n]
  · rw [cBasis_node]
  · intro m hmn
    simp only [deriv_cBasis_other hmn.symm, deriv_dBasis_other hmn.symm,
      mul_zero, add_zero]

end Cardinal

namespace Analysis

lemma polynomial_gaussian_bound {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → (1+r)^m * Real.exp (-c*r^2) ≤ C := by
  let B : ℝ := 2+c⁻¹
  refine ⟨B^m*(m.factorial:ℝ)*Real.exp 1, by positivity, ?_⟩
  intro r hr
  have hc' : 0 < c⁻¹ := inv_pos.mpr hc
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have h : 1+r ≤ B*(1+c*r^2) := by
    dsimp [B]
    have hsq := sq_nonneg (r-1)
    have hmul : c⁻¹*c=1 := inv_mul_cancel₀ hc.ne'
    nlinarith [sq_nonneg r, mul_nonneg hc.le (sq_nonneg r)]
  have hp : (1+c*r^2)^m ≤ (m.factorial:ℝ)*Real.exp (1+c*r^2) := by
    have hh := Real.pow_div_factorial_le_exp (1+c*r^2) (by positivity : 0 ≤ 1+c*r^2) m
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (m.factorial : ℝ))).mp hh |>.trans_eq (mul_comm _ _)
  calc
    (1+r)^m * Real.exp (-c*r^2) ≤ (B*(1+c*r^2))^m * Real.exp (-c*r^2) := by gcongr
    _ = B^m * ((1+c*r^2)^m * Real.exp (-c*r^2)) := by rw [mul_pow]; ring
    _ ≤ B^m * (((m.factorial:ℝ)*Real.exp (1+c*r^2))*Real.exp (-c*r^2)) := by gcongr
    _ = B^m*(m.factorial:ℝ)*Real.exp 1 := by
      rw [mul_assoc (m.factorial:ℝ), ← Real.exp_add]
      rw [show 1+c*r^2 + -c*r^2 = 1 by ring]
      ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gaussian_schwartz_decay {c : ℝ} (hc : 0 < c) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : E, ‖x‖^k * ‖iteratedFDeriv ℝ n (fun y : E => Real.exp (-c*‖y‖^2)) x‖ ≤ C := by
  have ht : (fun x : E => -c*‖x‖^2).HasTemperateGrowth := by fun_prop
  obtain ⟨l,B,hB,hder⟩ := ht.norm_iteratedFDeriv_le_uniform n
  obtain ⟨C,hC,hCbound⟩ := polynomial_gaussian_bound hc (k+l*n)
  refine ⟨(n.factorial:ℝ)*(B+1)^n*C, fun x => ?_⟩
  have hw : 1 ≤ (B+1)*(1+‖x‖)^l := by
    have hh : 1 ≤ (1+‖x‖)^l := one_le_pow₀ (by linarith [norm_nonneg x])
    nlinarith
  have hD (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun x : E => -c*‖x‖^2) x‖ ≤ ((B+1)*(1+‖x‖)^l)^i := by
    calc
      _ ≤ B*(1+‖x‖)^l := hder i hin x
      _ ≤ (B+1)*(1+‖x‖)^l := by gcongr; linarith
      _ ≤ ((B+1)*(1+‖x‖)^l)^i := le_self_pow₀ hw (by omega)
  have hexp (i : ℕ) (_hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i Real.exp (-c*‖x‖^2)‖ ≤ Real.exp (-c*‖x‖^2) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_eq_iterate,Real.iter_deriv_exp]
    exact le_of_eq (Real.norm_of_nonneg (Real.exp_pos _).le)
  have hd := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) Real.contDiff_exp ht.1 (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)) x hexp hD
  calc
    _ ≤ ‖x‖^k * ((n.factorial:ℝ)*Real.exp (-c*‖x‖^2)*((B+1)*(1+‖x‖)^l)^n) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ (1+‖x‖)^k * ((n.factorial:ℝ)*Real.exp (-c*‖x‖^2)*((B+1)*(1+‖x‖)^l)^n) := by gcongr; linarith
    _ = (n.factorial:ℝ)*(B+1)^n*((1+‖x‖)^(k+l*n)*Real.exp (-c*‖x‖^2)) := by
      rw [mul_pow,pow_add,pow_mul]
      ring
    _ ≤ (n.factorial:ℝ)*(B+1)^n*C := by gcongr; exact hCbound ‖x‖ (norm_nonneg _)

def gaussianSchwartz (c : ℝ) (hc : 0 < c) : 𝓢(E,ℝ) where
  toFun x := Real.exp (-c*‖x‖^2)
  smooth' := Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ))
  decay' := gaussian_schwartz_decay hc

@[simp] lemma gaussianSchwartz_apply (c : ℝ) (hc : 0 < c) (x : E) :
    gaussianSchwartz c hc x = Real.exp (-c*‖x‖^2) := rfl

lemma iteratedDeriv_real_of_complex {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => (f x).re) = fun x : ℝ => (iteratedDeriv n f x).re := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    exact ((hf.contDiff (n := ⊤)).differentiable_iteratedDeriv n (by simp) (x : ℂ)).hasDerivAt.real_of_complex.deriv

lemma entire_real_temperate {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hstrip : ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → ‖f z‖ ≤ M) :
    Function.HasTemperateGrowth (fun x : ℝ => (f x).re) := by
  obtain ⟨M,hM⟩ := hstrip
  refine ⟨hf.contDiff.real_of_complex, fun n => ⟨0,(n.factorial:ℝ)*M,?_⟩⟩
  intro x
  rw [pow_zero,mul_one,norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_real_of_complex hf]
  apply (Complex.abs_re_le_norm _).trans
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := f) n
    (by norm_num : (0:ℝ)<1) hf.diffContOnCl (c := (x:ℂ)) (C := M) (fun z hz => hM z (by
      have hi := Complex.abs_im_le_norm (z-(x:ℂ))
      have he := Metric.mem_sphere.mp hz
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero,← dist_eq_norm,he] using hi))
  simpa using hh

def dampedEntireSchwartz (c : ℝ) (hc : 0 < c) (b : ℝ) (f : ℂ → ℂ)
    (_hf : Differentiable ℂ f) (_hstrip : ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → ‖f z‖ ≤ M) : 𝓢(E,ℝ) :=
  SchwartzMap.smulLeftCLM ℝ (fun x : E => (f (b*‖x‖^2)).re) (gaussianSchwartz c hc)

lemma dampedEntireSchwartz_apply (c : ℝ) (hc : 0 < c) (b : ℝ) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hstrip : ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → ‖f z‖ ≤ M) (x : E) :
    dampedEntireSchwartz c hc b f hf hstrip x = Real.exp (-c*‖x‖^2)*(f (b*‖x‖^2)).re := by
  have ht := entire_real_temperate hf hstrip
  have hg : Function.HasTemperateGrowth (fun x : E => (f (b*‖x‖^2)).re) := by
    convert ht.comp (by fun_prop : Function.HasTemperateGrowth (fun x : E => b*‖x‖^2)) using 1
    funext x
    simp
  rw [dampedEntireSchwartz,SchwartzMap.smulLeftCLM_apply_apply hg,gaussianSchwartz_apply]
  simp [mul_comm]

end Analysis

namespace Cardinal

def dampedProfile (a : Coefficients) : SchwartzMap Plane ℝ :=
  Analysis.dampedEntireSchwartz (Real.pi * h * b)
    (mul_pos (mul_pos Real.pi_pos h_pos) b_pos) b (profile a)
    (differentiable_profile a) (profile_strip a 1)

lemma dampedProfile_apply (a : Coefficients) (x : Plane) :
    dampedProfile a x = Real.exp (-Real.pi * h * b * ‖x‖ ^ 2) *
      (profile a ((b * ‖x‖ ^ 2 : ℝ) : ℂ)).re := by
  rw [dampedProfile, Analysis.dampedEntireSchwartz_apply]
  push_cast
  congr 3; ring

lemma dampedProfile_complex (a : Coefficients) (x : Plane) :
    (dampedProfile a x : ℂ) = (Real.exp (-Real.pi * h * b * ‖x‖ ^ 2) : ℂ) *
      profile a ((b * ‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [dampedProfile_apply, Complex.ofReal_mul]
  have hh : ((profile a ((b * ‖x‖ ^ 2 : ℝ) : ℂ)).re : ℂ) =
      profile a ((b * ‖x‖ ^ 2 : ℝ) : ℂ) :=
    Complex.conj_eq_iff_re.mp (by
      simpa only [Complex.conj_ofReal] using profile_conj a ((b * ‖x‖ ^ 2 : ℝ) : ℂ))
  rw [hh]

lemma dampedProfile_radial (a : Coefficients) : IsRadial (dampedProfile a) := by
  intro x y hxy
  simp only [dampedProfile_apply, hxy]

theorem cardinal_realization (a : Coefficients) :
    Differentiable ℂ (profile a) ∧
    (∀ s : ℝ, (profile a (s : ℂ)).im = 0) ∧
    ∃ f : SchwartzMap Plane ℝ, IsRadial f ∧
      ∀ x : Plane, (f x : ℂ) =
        (Real.exp (-Real.pi * h * b * ‖x‖ ^ 2) : ℂ) *
          profile a ((b * ‖x‖ ^ 2 : ℝ) : ℂ) := by
  exact ⟨differentiable_profile a, profile_real a, dampedProfile a,
    dampedProfile_radial a, dampedProfile_complex a⟩

end Cardinal

end Triangular

end

end OAI
