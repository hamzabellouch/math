import OAI.Geometry.CylinderCovering.Angular.CubicAreaDefinitions
import OAI.Geometry.CylinderCovering.Angular.Taylor
import OAI.Geometry.CylinderCovering.Angular.Margins

namespace OAI

open Set MeasureTheory
open scoped Interval

noncomputable section
namespace CylinderCovering.Cubic

lemma profile_le_one {q : ℝ} (hq : |q| ≤ 1) : profile q ≤ 1 := by
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have hq4 : q ^ 4 ≤ 1 := by nlinarith [sq_nonneg (q ^ 2), sq_nonneg q]
  unfold profile
  linarith

lemma areaDensity_identity (q : ℝ) :
    2 * profile q - (((1 + q ^ 2) / 2) ^ 2 + 2 * q ^ 2) / 2 =
      areaDensity q := by
  unfold profile areaDensity
  ring

lemma areaDensity_integral :
    (∫ q in (-1 : ℝ)..1, areaDensity q) = -(1 / 15 : ℝ) := by
  unfold areaDensity
  have h₁ : IntervalIntegrable (fun q : ℝ => -(1 / 8 : ℝ) - q ^ 2 / 4)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h₂ : IntervalIntegrable (fun q : ℝ => 7 * q ^ 4 / 8) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h₃ : IntervalIntegrable (fun q : ℝ => q ^ 2 / 4) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add h₁ h₂,
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) h₃]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow,
    intervalIntegral.integral_const]
  norm_num

lemma inverseSqrt_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 1 / Real.sqrt (1 + x) ∧
    1 / Real.sqrt (1 + x) ≤ 1 ∧
    |1 / Real.sqrt (1 + x) - 1| ≤ x / 2 := by
  let t := Real.sqrt (1 + x)
  have ht : 1 ≤ t := by
    dsimp [t]
    exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have ht0 : 0 < t := by linarith
  have ht2 : t ^ 2 = 1 + x := Real.sq_sqrt (by linarith)
  have hu : 1 / t ≤ 1 := (div_le_one ht0).2 ht
  have hl : 1 - x / 2 ≤ 1 / t := by
    apply (le_div_iff₀ ht0).2
    have hfac : 0 ≤ (t - 1) ^ 2 * (t + 2) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith only [hfac, ht2]
  change 0 ≤ 1 / t ∧ 1 / t ≤ 1 ∧ |1 / t - 1| ≤ x / 2
  refine ⟨by positivity, hu, ?_⟩
  rw [abs_of_nonpos (by linarith : 1 / t - 1 ≤ 0)]
  linarith

theorem scalar_cubic_remainder {eps D A : ℝ}
    (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2)
    (hD0 : 0 ≤ D) (hD1 : D ≤ 1) (hA0 : 0 ≤ A) (hA1 : A ≤ 3) :
    |(1 + eps ^ 2 * D + 100 * eps ^ 3) ^ 2 /
        Real.sqrt (1 + eps ^ 2 * A) -
      (1 + eps ^ 2 * (2 * D - A / 2))| ≤ 1600 * eps ^ 3 := by
  let d := eps ^ 2 * D + 100 * eps ^ 3
  let x := eps ^ 2 * A
  let F := 1 / Real.sqrt (1 + x)
  have he2 : 0 ≤ eps ^ 2 := sq_nonneg eps
  have he3 : 0 ≤ eps ^ 3 := pow_nonneg he0 _
  have he4 : 0 ≤ eps ^ 4 := pow_nonneg he0 _
  have he32 : eps ^ 3 ≤ eps ^ 2 / 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right he1 he2]
  have he43 : eps ^ 4 ≤ eps ^ 3 / 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right he1 he3]
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hd : d ≤ 51 * eps ^ 2 := by
    dsimp [d]
    nlinarith only [mul_le_mul_of_nonneg_left hD1 he2, he32]
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx : x ≤ 3 * eps ^ 2 := by
    dsimp [x]
    nlinarith only [mul_le_mul_of_nonneg_left hA1 he2]
  have hx2 : x ^ 2 ≤ 9 * eps ^ 4 := by
    nlinarith only [mul_self_le_mul_self hx0 hx]
  have hd2 : d ^ 2 ≤ 2601 * eps ^ 4 := by
    nlinarith only [mul_self_le_mul_self hd0 hd]
  have hdx : d * x ≤ 153 * eps ^ 4 := by
    nlinarith only [mul_le_mul hd hx hx0 (by positivity : 0 ≤ 51 * eps ^ 2)]
  obtain ⟨hF0, hF1, hFd⟩ := inverseSqrt_bounds hx0
  change 0 ≤ F at hF0
  change F ≤ 1 at hF1
  change |F - 1| ≤ x / 2 at hFd
  have hR : |F - (1 - x / 2)| ≤ (3 / 8) * x ^ 2 :=
    AngularTaylor.inv_sqrt_remainder hx0
  have hcross : |2 * d * (F - 1)| ≤ d * x := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * d)]
    nlinarith only [mul_le_mul_of_nonneg_left hFd (by positivity : 0 ≤ 2 * d)]
  have hquad : |d ^ 2 * F| ≤ d ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg d) hF0)]
    exact mul_le_of_le_one_right (sq_nonneg d) hF1
  have hid : (1 + eps ^ 2 * D + 100 * eps ^ 3) ^ 2 /
        Real.sqrt (1 + eps ^ 2 * A) - (1 + eps ^ 2 * (2 * D - A / 2)) =
      (F - (1 - x / 2)) + 2 * d * (F - 1) + d ^ 2 * F + 200 * eps ^ 3 := by
    dsimp [F, x, d]
    ring
  rw [hid]
  have hab := abs_add_le (F - (1 - x / 2)) (2 * d * (F - 1))
  have habc := abs_add_le ((F - (1 - x / 2)) + 2 * d * (F - 1)) (d ^ 2 * F)
  have habcd := abs_add_le ((F - (1 - x / 2)) + 2 * d * (F - 1) + d ^ 2 * F)
    (200 * eps ^ 3)
  rw [abs_of_nonneg (by positivity : 0 ≤ 200 * eps ^ 3)] at habcd
  nlinarith only [hab, habc, habcd, hR, hcross, hquad, hx2, hd2, hdx, he43, he3]

lemma coefficient_bounds {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    0 ≤ alpha a b ∧ alpha a b ≤ 1 ∧ |beta a b| ≤ 1 ∧
    0 ≤ profileMax a b ∧ profileMax a b ≤ 1 ∧
    0 ≤ speedSq a b ∧ speedSq a b ≤ 3 := by
  have hab : |a * b| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul ha hb (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hsum : |a + b| ≤ 2 := (abs_add_le a b).trans (by linarith)
  have ha0 : 0 ≤ alpha a b := by
    unfold alpha
    linarith [(abs_le.mp hab).1]
  have ha1 : alpha a b ≤ 1 := by
    unfold alpha
    linarith [(abs_le.mp hab).2]
  have hb1 : |beta a b| ≤ 1 := by
    unfold beta
    rw [abs_div]
    norm_num
    linarith
  have hM0 : 0 ≤ profileMax a b :=
    (profile_nonneg a).trans (le_max_left _ _)
  have hM1 : profileMax a b ≤ 1 := max_le (profile_le_one ha) (profile_le_one hb)
  refine ⟨ha0, ha1, hb1, hM0, hM1, ?_, ?_⟩
  · unfold speedSq
    positivity
  · have ha2 : alpha a b ^ 2 ≤ 1 := by nlinarith only [ha0, ha1]
    have hb2 : beta a b ^ 2 ≤ 1 := by
      nlinarith only [(abs_le.mp hb1).1, (abs_le.mp hb1).2]
    unfold speedSq
    linarith

lemma profile_lipschitz {a q : ℝ} (ha : |a| ≤ 1) (hq : |q| ≤ 1) :
    |profile a - profile q| ≤ 3 * |a - q| := by
  have ha2 : a ^ 2 ≤ 1 := by nlinarith only [(abs_le.mp ha).1, (abs_le.mp ha).2]
  have hq2 : q ^ 2 ≤ 1 := by nlinarith only [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have hsum : |a + q| ≤ 2 := (abs_add_le a q).trans (by linarith)
  have hpoly : |1 + a ^ 2 + q ^ 2| ≤ 3 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 1 + a ^ 2 + q ^ 2)]
    linarith
  have hid : profile a - profile q = (a - q) * (a + q) * (1 + a ^ 2 + q ^ 2) / 2 := by
    unfold profile
    ring
  rw [hid, abs_div, abs_mul, abs_mul]
  norm_num
  have hmul := mul_le_mul hsum hpoly (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have hfinal := mul_le_mul_of_nonneg_left hmul (abs_nonneg (a - q))
  nlinarith only [hfinal]

lemma profileMax_error {a b q : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hqa : a ≤ q) (hqb : q ≤ b) :
    |profileMax a b - profile q| ≤ 3 * (b - a) := by
  have hq := abs_le_of_interval ha hb hqa hqb
  have h₁ := profile_lipschitz ha hq
  have h₂ := profile_lipschitz hb hq
  rw [abs_of_nonpos (by linarith : a - q ≤ 0)] at h₁
  rw [abs_of_nonneg (by linarith : 0 ≤ b - q)] at h₂
  have hlo : profile q ≤ profileMax a b := profile_le_max_endpoints hqa hqb
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  have hupper : profileMax a b ≤ profile q + 3 * (b - a) := by
    apply max_le
    · linarith [(abs_le.mp h₁).2]
    · linarith [(abs_le.mp h₂).2]
  linarith

lemma square_error {x y e : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hxy : |x - y| ≤ e) : |x ^ 2 - y ^ 2| ≤ 2 * e := by
  have hsum : |x + y| ≤ 2 := (abs_add_le x y).trans (by linarith)
  have he : 0 ≤ e := (abs_nonneg _).trans hxy
  calc
    |x ^ 2 - y ^ 2| = |x - y| * |x + y| := by rw [← abs_mul]; congr 1; ring
    _ ≤ e * 2 := mul_le_mul hxy hsum (abs_nonneg _) he
    _ = 2 * e := by ring

lemma density_error {a b q : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hqa : a ≤ q) (hqb : q ≤ b) :
    |2 * profileMax a b - speedSq a b / 2 - areaDensity q| ≤ 8 * (b - a) := by
  have hq := abs_le_of_interval ha hb hqa hqb
  have hc := coefficient_bounds ha hb
  have hα := alpha_error ha hq hqa hqb
  have hβ := beta_error hqa hqb
  have hq2 : q ^ 2 ≤ 1 := by nlinarith only [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have hαq : |(1 + q ^ 2) / 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ (1 + q ^ 2) / 2)]
    linarith
  have hαabs : |alpha a b| ≤ 1 := by rw [abs_of_nonneg hc.1]; exact hc.2.1
  have hαsq := square_error hαabs hαq hα
  have hβsq := square_error hc.2.2.1 hq hβ
  have hspeed : |speedSq a b - (((1 + q ^ 2) / 2) ^ 2 + 2 * q ^ 2)| ≤ 4 * (b - a) := by
    have hid : speedSq a b - (((1 + q ^ 2) / 2) ^ 2 + 2 * q ^ 2) =
      (alpha a b ^ 2 - ((1 + q ^ 2) / 2) ^ 2) + 2 * (beta a b ^ 2 - q ^ 2) := by
      unfold speedSq
      ring
    rw [hid]
    have hh := abs_add_le (alpha a b ^ 2 - ((1 + q ^ 2) / 2) ^ 2)
      (2 * (beta a b ^ 2 - q ^ 2))
    rw [abs_mul] at hh
    norm_num at hh
    linarith
  have hM := profileMax_error ha hb hqa hqb
  have hid : 2 * profileMax a b - speedSq a b / 2 - areaDensity q =
      2 * (profileMax a b - profile q) -
      (speedSq a b - (((1 + q ^ 2) / 2) ^ 2 + 2 * q ^ 2)) / 2 := by
    rw [← areaDensity_identity]
    ring
  rw [hid]
  have hh := abs_add_le (2 * (profileMax a b - profile q))
    (-((speedSq a b - (((1 + q ^ 2) / 2) ^ 2 + 2 * q ^ 2)) / 2))
  rw [← sub_eq_add_neg, abs_neg] at hh
  rw [abs_mul, abs_div] at hh
  norm_num at hh
  linarith

lemma continuous_areaDensity : Continuous areaDensity := by
  unfold areaDensity
  fun_prop

lemma interval_density_error {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hab : a ≤ b) :
    |(b - a) * (2 * profileMax a b - speedSq a b / 2) -
      (∫ q in a..b, areaDensity q)| ≤ 8 * (b - a) ^ 2 := by
  have hu : ∀ q ∈ Ι a b,
      ‖2 * profileMax a b - speedSq a b / 2 - areaDensity q‖ ≤ 8 * (b - a) := by
    intro q hq
    rw [Set.uIoc_of_le hab] at hq
    simpa only [Real.norm_eq_abs] using density_error ha hb hq.1.le hq.2
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hu
  rw [intervalIntegral.integral_sub
    (f := fun _ : ℝ => 2 * profileMax a b - speedSq a b / 2)
    (g := areaDensity) (continuous_const.intervalIntegrable _ _)
    (continuous_areaDensity.intervalIntegrable _ _), intervalIntegral.integral_const,
    Real.norm_eq_abs, smul_eq_mul, abs_of_nonneg (sub_nonneg.mpr hab)] at h
  nlinarith only [h]

lemma count_mul_step {N : ℕ} (hN : 0 < N) : (N : ℝ) * step N = 2 := by
  have h := node_last hN
  dsimp [node] at h
  linarith only [h]

def areaCoefficientSum (N : ℕ) : ℝ := ∑ j : Fin N,
  step N * (2 * profileMax (node N j) (node N (j + 1)) -
    speedSq (node N j) (node N (j + 1)) / 2)

lemma integral_mesh_sum {N : ℕ} (hN : 0 < N) :
    (∑ j : Fin N, ∫ q in node N j..node N (j + 1), areaDensity q) = -(1 / 15 : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => ∫ q in node N j..node N (j + 1), areaDensity q) N]
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun _ _ => continuous_areaDensity.intervalIntegrable _ _)]
  rw [node_zero, node_last hN, areaDensity_integral]

lemma areaCoefficientSum_error {N : ℕ} (hN : 0 < N) :
    |areaCoefficientSum N + 1 / 15| ≤ 16 * step N := by
  have hi := integral_mesh_sum hN
  have hid : areaCoefficientSum N + 1 / 15 =
      ∑ j : Fin N, (step N * (2 * profileMax (node N j) (node N (j + 1)) -
        speedSq (node N j) (node N (j + 1)) / 2) -
        ∫ q in node N j..node N (j + 1), areaDensity q) := by
    rw [Finset.sum_sub_distrib, hi]
    dsimp [areaCoefficientSum]
    ring
  rw [hid]
  calc
    _ ≤ ∑ j : Fin N, |step N * (2 * profileMax (node N j) (node N (j + 1)) -
        speedSq (node N j) (node N (j + 1)) / 2) -
        ∫ q in node N j..node N (j + 1), areaDensity q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin N, 8 * (step N) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have hab : node N j ≤ node N (j + 1) := by
        have := node_succ N j
        have := step_pos hN
        linarith
      have h := interval_density_error (node_abs_le hN j.isLt.le)
        (node_abs_le hN (Nat.succ_le_of_lt j.isLt)) hab
      simpa only [node_succ] using h
    _ = 16 * step N := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc
        (N : ℝ) * (8 * (step N) ^ 2) = 8 * ((N : ℝ) * step N) * step N := by ring
        _ = 16 * step N := by rw [count_mul_step hN]; ring

lemma areaTerm_remainder {eps a b : ℝ} (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : a ≤ b) :
    |areaTerm eps a b - (b - a) * (1 + eps ^ 2 *
      (2 * profileMax a b - speedSq a b / 2))| ≤ (b - a) * 1600 * eps ^ 3 := by
  rcases coefficient_bounds ha hb with ⟨_, _, _, hD0, hD1, hA0, hA1⟩
  have h := scalar_cubic_remainder he0 he1 hD0 hD1 hA0 hA1
  have hid : areaTerm eps a b - (b - a) * (1 + eps ^ 2 *
      (2 * profileMax a b - speedSq a b / 2)) =
      (b - a) * ((1 + eps ^ 2 * profileMax a b + 100 * eps ^ 3) ^ 2 /
        Real.sqrt (1 + eps ^ 2 * speedSq a b) -
        (1 + eps ^ 2 * (2 * profileMax a b - speedSq a b / 2))) := by
    unfold areaTerm cap
    ring
  rw [hid, abs_mul, abs_of_nonneg (sub_nonneg.mpr hab)]
  nlinarith only [mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hab)]

lemma areaSum_coefficient_remainder {eps : ℝ} {N : ℕ}
    (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2) (hN : 0 < N) :
    |areaSum eps N - (2 + eps ^ 2 * areaCoefficientSum N)| ≤ 3200 * eps ^ 3 := by
  let f : Fin N → ℝ := fun j => step N * (1 + eps ^ 2 *
    (2 * profileMax (node N j) (node N (j + 1)) -
      speedSq (node N j) (node N (j + 1)) / 2))
  have hsum : (∑ j : Fin N, f j) = 2 + eps ^ 2 * areaCoefficientSum N := by
    dsimp [f, areaCoefficientSum]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    have heq : (∑ j : Fin N, step N * (eps ^ 2 *
        (2 * profileMax (node N j) (node N (j + 1)) -
          speedSq (node N j) (node N (j + 1)) / 2))) =
        ∑ j : Fin N, eps ^ 2 * (step N *
        (2 * profileMax (node N j) (node N (j + 1)) -
          speedSq (node N j) (node N (j + 1)) / 2)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    congr 1
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact count_mul_step hN
  rw [← hsum]
  unfold areaSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin N, |areaTerm eps (node N j) (node N (j + 1)) - f j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin N, step N * 1600 * eps ^ 3 := by
      apply Finset.sum_le_sum
      intro j _
      have hab : node N j ≤ node N (j + 1) := by
        have := node_succ N j
        have := step_pos hN
        linarith
      have h := areaTerm_remainder he0 he1 (node_abs_le hN j.isLt.le)
        (node_abs_le hN (Nat.succ_le_of_lt j.isLt)) hab
      simpa only [node_succ, f] using h
    _ = 3200 * eps ^ 3 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc
        (N : ℝ) * (step N * 1600 * eps ^ 3) = ((N : ℝ) * step N) * 1600 * eps ^ 3 := by ring
        _ = 3200 * eps ^ 3 := by rw [count_mul_step hN]; ring

theorem areaSum_expansion {eps : ℝ} {N : ℕ}
    (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2) (hN : 0 < N)
    (hstep : step N ≤ eps ^ 2) :
    |areaSum eps N - (2 - eps ^ 2 / 15)| ≤ 3208 * eps ^ 3 := by
  have hR := areaSum_coefficient_remainder he0 he1 hN
  have hC := areaCoefficientSum_error hN
  have hc : |eps ^ 2 * (areaCoefficientSum N + 1 / 15)| ≤ 8 * eps ^ 3 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    have h₁ := mul_le_mul_of_nonneg_left hC (sq_nonneg eps)
    have h₂ := mul_le_mul_of_nonneg_left hstep (by positivity : 0 ≤ 16 * eps ^ 2)
    have h₃ := mul_le_mul_of_nonneg_right he1 (pow_nonneg he0 3)
    nlinarith only [h₁, h₂, h₃]
  have hid : areaSum eps N - (2 - eps ^ 2 / 15) =
      (areaSum eps N - (2 + eps ^ 2 * areaCoefficientSum N)) +
      eps ^ 2 * (areaCoefficientSum N + 1 / 15) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith only [hR, hc])

end CylinderCovering.Cubic

end

end OAI
