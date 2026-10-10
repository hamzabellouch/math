import OAI.InformationTheory.BooleanNoise.Basic
import OAI.InformationTheory.BooleanNoise.EntropySeries
import OAI.InformationTheory.BooleanNoise.PairEntropy
import OAI.InformationTheory.BooleanNoise.LambdaScalars
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

namespace OAI

noncomputable section

open scoped BigOperators

universe u

namespace LeanBlast.CourtadeKumar

theorem pow_tangent_remainder_nonneg (n : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ x ^ (n + 1) - y ^ (n + 1) - (n + 1 : ℝ) * y ^ n * (x - y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := add_nonneg (mul_nonneg hx ih)
      (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ n + 1) (pow_nonneg hy n))
        (sq_nonneg (x - y)))
    convert hp using 1
    push_cast
    simp only [pow_succ]
    ring

theorem pow_tangent_remainder_lower (n : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (n + 1 : ℝ) * y ^ n * (x - y) ^ 2 ≤
      x ^ (n + 2) - y ^ (n + 2) - (n + 2 : ℝ) * y ^ (n + 1) * (x - y) := by
  have hp := mul_nonneg hx (pow_tangent_remainder_nonneg n x y hx hy)
  have hid : x ^ (n + 2) - y ^ (n + 2) - (n + 2 : ℝ) * y ^ (n + 1) * (x - y) =
      x * (x ^ (n + 1) - y ^ (n + 1) - (n + 1 : ℝ) * y ^ n * (x - y)) +
        (n + 1 : ℝ) * y ^ n * (x - y) ^ 2 := by
    simp only [pow_succ]
    ring
  rw [hid]
  linarith

section Weighted

variable {ι : Type u} [Fintype ι]

private abbrev entropySeriesCoeff (j : ℕ) : ℝ := psiCoeff j

theorem weighted_even_pow_jensen (w x : ι → ℝ) (n : ℕ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) :
    (∑ i, w i * x i) ^ (2 * n) ≤ ∑ i, w i * (x i) ^ (2 * n) := by
  have hc : ConvexOn ℝ Set.univ (fun t : ℝ => t ^ (2 * n)) :=
    (even_two_mul n).convexOn_pow
  simpa only [smul_eq_mul] using hc.map_sum_le (fun i _ => hw i) hprob
    (fun i _ => Set.mem_univ (x i))

theorem weighted_centered_second_moment (w x : ι → ℝ) (y : ℝ)
    (hprob : ∑ i, w i = 1) (hmean : ∑ i, w i * x i = y) :
    (∑ i, w i * (x i - y) ^ 2) = (∑ i, w i * (x i) ^ 2) - y ^ 2 := by
  calc
    (∑ i, w i * (x i - y) ^ 2) =
        ∑ i, (w i * (x i) ^ 2 - 2 * y * (w i * x i) + y ^ 2 * w i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, w i * (x i) ^ 2) - 2 * y * (∑ i, w i * x i) + y ^ 2 * (∑ i, w i) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hprob, hmean]; ring

theorem weighted_pow_gap_lower (w x : ι → ℝ) (y : ℝ) (n : ℕ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hx : ∀ i, 0 ≤ x i) (hy : 0 ≤ y) (hmean : ∑ i, w i * x i = y) :
    (n + 1 : ℝ) * y ^ n * ((∑ i, w i * (x i) ^ 2) - y ^ 2) ≤
      (∑ i, w i * (x i) ^ (n + 2)) - y ^ (n + 2) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (pow_tangent_remainder_lower n (x i) y (hx i) hy) (hw i))
  have hleft : (∑ i, w i * ((n + 1 : ℝ) * y ^ n * (x i - y) ^ 2)) =
      (n + 1 : ℝ) * y ^ n * ((∑ i, w i * (x i) ^ 2) - y ^ 2) := by
    rw [← weighted_centered_second_moment w x y hprob hmean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hright : (∑ i, w i *
      ((x i) ^ (n + 2) - y ^ (n + 2) - (n + 2 : ℝ) * y ^ (n + 1) * (x i - y))) =
      (∑ i, w i * (x i) ^ (n + 2)) - y ^ (n + 2) := by
    calc
      _ = ∑ i, (w i * (x i) ^ (n + 2) - y ^ (n + 2) * w i -
          (n + 2 : ℝ) * y ^ (n + 1) * (w i * x i - y * w i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, w i * (x i) ^ (n + 2)) - y ^ (n + 2) * (∑ i, w i) -
          (n + 2 : ℝ) * y ^ (n + 1) * ((∑ i, w i * x i) - y * (∑ i, w i)) := by
        simp only [Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
      _ = _ := by rw [hprob, hmean]; ring
  rwa [hleft, hright] at h

theorem weighted_series_gap_hasSum (c : ℕ → ℝ) (p : ℕ → ℕ) (F : ℝ → ℝ)
    (w x : ι → ℝ) (y : ℝ)
    (hx : ∀ i, HasSum (fun j => c j * (x i) ^ (p j)) (F (x i)))
    (hy : HasSum (fun j => c j * y ^ (p j)) (F y)) :
    HasSum (fun j => 2 * c j * ((∑ i, w i * (x i) ^ (p j)) - y ^ (p j)))
      (2 * ((∑ i, w i * F (x i)) - F y)) := by
  have hsum := hasSum_sum (s := Finset.univ) (fun i _ => (hx i).mul_left (w i))
  have h := (hsum.sub hy).mul_left 2
  have heq : ∀ j, (∑ i, w i * (c j * (x i) ^ (p j))) =
      c j * (∑ i, w i * (x i) ^ (p j)) := by
    intro j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [heq] at h
  convert h using 1
  ext j
  ring

private theorem entropy_series_gap_lower (F : ℝ → ℝ) (w x : ι → ℝ) (y : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (hmean : ∑ i, w i * x i = y)
    (hx : ∀ i, HasSum (fun j => entropySeriesCoeff j * (x i) ^ (2 * (j + 1))) (F (x i)))
    (hy : HasSum (fun j => entropySeriesCoeff j * y ^ (2 * (j + 1))) (F y)) :
    (∑ i, w i * (x i) ^ 2) - y ^ 2 ≤ 2 * ((∑ i, w i * F (x i)) - F y) := by
  have hsum := weighted_series_gap_hasSum entropySeriesCoeff (fun j => 2 * (j + 1)) F w x y hx hy
  apply hasSum_le _ (hasSum_ite_eq (0 : ℕ) ((∑ i, w i * (x i) ^ 2) - y ^ 2)) hsum
  intro j
  by_cases hj : j = 0
  · subst j
    norm_num [entropySeriesCoeff]
  · simp only [ite_eq_right hj]
    have hp := weighted_even_pow_jensen w x (j + 1) hw hprob
    rw [hmean] at hp
    exact mul_nonneg (mul_nonneg (by norm_num) (psiCoeff_nonneg j)) (sub_nonneg.mpr hp)

private theorem entropy_series_gap_strengthened (F : ℝ → ℝ) (w x : ι → ℝ) (y : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (hmean : ∑ i, w i * x i = y)
    (hx0 : ∀ i, 0 ≤ x i) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hx : ∀ i, HasSum (fun j => entropySeriesCoeff j * (x i) ^ (2 * (j + 1))) (F (x i)))
    (hy : HasSum (fun j => entropySeriesCoeff j * y ^ (2 * (j + 1))) (F y)) :
    ((∑ i, w i * (x i) ^ 2) - y ^ 2) * lambda (y ^ 2) ≤
      2 * ((∑ i, w i * F (x i)) - F y) := by
  have hsum := weighted_series_gap_hasSum entropySeriesCoeff (fun j => 2 * (j + 1)) F w x y hx hy
  have hlambda := (hasSum_lambda (sq_nonneg y) (by nlinarith : y ^ 2 < 1)).mul_left
    ((∑ i, w i * (x i) ^ 2) - y ^ 2)
  apply hasSum_le _ hlambda hsum
  intro j
  have hp := weighted_pow_gap_lower w x y (2 * j) hw hprob hx0 hy0 hmean
  have hc : 0 ≤ 2 * entropySeriesCoeff j := mul_nonneg (by norm_num) (psiCoeff_nonneg j)
  have h := mul_le_mul_of_nonneg_left hp hc
  have heq : 2 * entropySeriesCoeff j *
      ((2 * j + 1 : ℝ) * y ^ (2 * j) * ((∑ i, w i * (x i) ^ 2) - y ^ 2)) =
      ((∑ i, w i * (x i) ^ 2) - y ^ 2) * ((y ^ 2) ^ j / ((j : ℝ) + 1)) := by
    simp only [entropySeriesCoeff, psiCoeff, pow_mul]
    field_simp
  rw [show 2 * j + 2 = 2 * (j + 1) by omega] at h
  push_cast at h
  rwa [heq] at h

theorem weighted_psi_gap (w x : ι → ℝ) (y : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (hmean : ∑ i, w i * x i = y)
    (hx : ∀ i, |x i| < 1) :
    (∑ i, w i * (x i) ^ 2) - y ^ 2 ≤ 2 * ((∑ i, w i * psi (x i)) - psi y) := by
  have hy : |y| < 1 := by
    apply abs_lt.mpr
    rw [← hmean]
    simpa only [smul_eq_mul, Set.mem_Ioo] using (convex_Ioo (-1 : ℝ) 1).sum_mem
      (fun i _ => hw i) hprob (fun i _ => abs_lt.mp (hx i))
  exact entropy_series_gap_lower psi w x y hw hprob hmean
    (fun i => hasSum_psi (hx i)) (hasSum_psi hy)

theorem weighted_psi_gap_strengthened (w x : ι → ℝ) (y : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (hmean : ∑ i, w i * x i = y)
    (hx : ∀ i, |x i| < 1) (hx0 : ∀ i, 0 ≤ x i) :
    ((∑ i, w i * (x i) ^ 2) - y ^ 2) * lambda (y ^ 2) ≤
      2 * ((∑ i, w i * psi (x i)) - psi y) := by
  have hy : |y| < 1 := by
    apply abs_lt.mpr
    rw [← hmean]
    simpa only [smul_eq_mul, Set.mem_Ioo] using (convex_Ioo (-1 : ℝ) 1).sum_mem
      (fun i _ => hw i) hprob (fun i _ => abs_lt.mp (hx i))
  have hy0 : 0 ≤ y := by
    rw [← hmean]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hx0 i))
  exact entropy_series_gap_strengthened psi w x y hw hprob hmean hx0 hy0
    (abs_lt.mp hy).2 (fun i => hasSum_psi (hx i)) (hasSum_psi hy)

private theorem normalized_ratio_weights_data (w t b : ι → ℝ) (T k : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hmass : ∑ i, w i * t i = T) (hmean : ∑ i, w i * b i = k) :
    (∀ i, 0 ≤ w i * t i / T) ∧ (∑ i, w i * t i / T) = 1 ∧
      (∑ i, (w i * t i / T) * (b i / t i)) = k / T := by
  refine ⟨fun i => div_nonneg (mul_nonneg (hw i) (ht i).le) hT.le, ?_, ?_⟩
  · rw [← Finset.sum_div, hmass, div_self hT.ne']
  · calc
      _ = ∑ i, (w i * b i) / T := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [(ht i).ne']
      _ = k / T := by rw [← Finset.sum_div, hmean]

private theorem rescale_perspective_gap (w t b : ι → ℝ) (T k C : ℝ)
    (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hgap : ((∑ i, (w i * t i / T) * (b i / t i) ^ 2) - (k / T) ^ 2) * C ≤
      2 * ((∑ i, (w i * t i / T) * psi (b i / t i)) - psi (k / T))) :
    ((∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T) * C ≤
      2 * ((∑ i, w i * t i * psi (b i / t i)) - T * psi (k / T)) := by
  have hsecond : (∑ i, (w i * t i / T) * (b i / t i) ^ 2) =
      (∑ i, w i * (b i) ^ 2 / t i) / T := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(ht i).ne']
  have hentropy : (∑ i, (w i * t i / T) * psi (b i / t i)) =
      (∑ i, w i * t i * psi (b i / t i)) / T := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsecond, hentropy] at hgap
  have h := mul_le_mul_of_nonneg_left hgap hT.le
  convert h using 1 <;> field_simp

theorem weighted_perspective_gap (w t b : ι → ℝ) (T k : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hmass : ∑ i, w i * t i = T) (hmean : ∑ i, w i * b i = k)
    (hdom : ∀ i, |b i| < t i) :
    (∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T ≤
      2 * ((∑ i, w i * t i * psi (b i / t i)) - T * psi (k / T)) := by
  obtain ⟨hq0, hq1, hqm⟩ := normalized_ratio_weights_data w t b T k hw ht hT hmass hmean
  have hx : ∀ i, |b i / t i| < 1 := by
    intro i
    rw [abs_div, abs_of_pos (ht i)]
    exact (div_lt_one (ht i)).mpr (hdom i)
  have hg := weighted_psi_gap (fun i => w i * t i / T) (fun i => b i / t i)
    (k / T) hq0 hq1 hqm hx
  simpa only [mul_one] using rescale_perspective_gap w t b T k 1 ht hT
    (by simpa only [mul_one] using hg)

theorem weighted_perspective_gap_strengthened (w t b : ι → ℝ) (T k : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hmass : ∑ i, w i * t i = T) (hmean : ∑ i, w i * b i = k)
    (hdom : ∀ i, |b i| < t i) (hb : ∀ i, 0 ≤ b i) :
    ((∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T) * lambda ((k / T) ^ 2) ≤
      2 * ((∑ i, w i * t i * psi (b i / t i)) - T * psi (k / T)) := by
  obtain ⟨hq0, hq1, hqm⟩ := normalized_ratio_weights_data w t b T k hw ht hT hmass hmean
  have hx : ∀ i, |b i / t i| < 1 := by
    intro i
    rw [abs_div, abs_of_pos (ht i)]
    exact (div_lt_one (ht i)).mpr (hdom i)
  have hg := weighted_psi_gap_strengthened (fun i => w i * t i / T) (fun i => b i / t i)
    (k / T) hq0 hq1 hqm hx (fun i => div_nonneg (hb i) (ht i).le)
  exact rescale_perspective_gap w t b T k (lambda ((k / T) ^ 2)) ht hT hg

theorem weighted_abs_mean_le (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    |∑ i, w i * x i| ≤ ∑ i, w i * |x i| := by
  calc
    |∑ i, w i * x i| ≤ ∑ i, |w i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_of_nonneg (hw _)]

theorem weighted_pair_mean_interior (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hdom : ∀ i, |a i| + |b i| < 1) :
    |∑ i, w i * a i| + |∑ i, w i * b i| < 1 := by
  have havg : (∑ i, w i * (|a i| + |b i|)) < 1 := by
    simpa only [smul_eq_mul, Set.mem_Iio] using (convex_Iio (1 : ℝ)).sum_mem
      (fun i _ => hw i) hprob (fun i _ => hdom i)
  have h := add_le_add (weighted_abs_mean_le w a hw) (weighted_abs_mean_le w b hw)
  rw [← Finset.sum_add_distrib] at h
  simp only [← mul_add] at h
  exact h.trans_lt havg

theorem weighted_positive_mean (w t : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (ht : ∀ i, 0 < t i) :
    0 < ∑ i, w i * t i := by
  simpa only [smul_eq_mul, Set.mem_Ioi] using (convex_Ioi (0 : ℝ)).sum_mem
    (fun i _ => hw i) hprob (fun i _ => ht i)

theorem weighted_ratio_centered_identity (w t b : ι → ℝ) (y : ℝ)
    (ht : ∀ i, t i ≠ 0) :
    (∑ i, w i * t i * (b i / t i - y) ^ 2) =
      (∑ i, w i * (b i) ^ 2 / t i) - 2 * y * (∑ i, w i * b i) +
        y ^ 2 * (∑ i, w i * t i) := by
  calc
    _ = ∑ i, (w i * (b i) ^ 2 / t i - 2 * y * (w i * b i) +
        y ^ 2 * (w i * t i)) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [ht i]
      ring
    _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

theorem weighted_ratio_variance_identity (w t b : ι → ℝ) (T k : ℝ)
    (ht : ∀ i, t i ≠ 0) (hT : T ≠ 0)
    (hmass : ∑ i, w i * t i = T) (hmean : ∑ i, w i * b i = k) :
    (∑ i, w i * t i * (b i / t i - k / T) ^ 2) =
      (∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T := by
  rw [weighted_ratio_centered_identity w t b _ ht, hmass, hmean]
  field_simp
  ring

theorem weighted_ratio_variance_nonneg (w t b : ι → ℝ) (T k : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hmass : ∑ i, w i * t i = T) (hmean : ∑ i, w i * b i = k) :
    0 ≤ (∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T := by
  rw [← weighted_ratio_variance_identity w t b T k (fun i => (ht i).ne') hT.ne'
    hmass hmean]
  exact Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (hw i) (ht i).le) (sq_nonneg _))

theorem weighted_variance_gap_lower_bound (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hdom : ∀ i, |a i| + |b i| < 1) :
    (∑ i, w i * b i) ^ 2 / (∑ i, w i * (1 - (a i) ^ 2)) -
        (∑ i, w i * b i) ^ 2 / (1 - (∑ i, w i * a i) ^ 2) ≤
      (∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) -
        (∑ i, w i * b i) ^ 2 / (1 - (∑ i, w i * a i) ^ 2) := by
  have ht : ∀ i, 0 < 1 - (a i) ^ 2 := by
    intro i
    have hi := hdom i
    have hsq := sq_abs (a i)
    nlinarith [abs_nonneg (a i), abs_nonneg (b i)]
  have hT := weighted_positive_mean w (fun i => 1 - (a i) ^ 2) hw hprob ht
  have h := weighted_ratio_variance_nonneg w (fun i => 1 - (a i) ^ 2) b _ _
    hw ht hT rfl rfl
  linarith

theorem weighted_variance_gap_nonneg (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hdom : ∀ i, |a i| + |b i| < 1) :
    0 ≤ (∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) -
      (∑ i, w i * b i) ^ 2 / (1 - (∑ i, w i * a i) ^ 2) := by
  have ht : ∀ i, 0 < 1 - (a i) ^ 2 := by
    intro i
    have hi := hdom i
    nlinarith [sq_abs (a i), abs_nonneg (a i), abs_nonneg (b i)]
  have hT := weighted_positive_mean w (fun i => 1 - (a i) ^ 2) hw hprob ht
  have hj := weighted_even_pow_jensen w a 1 hw hprob
  norm_num only [Nat.mul_one] at hj
  have hW : (∑ i, w i * (1 - (a i) ^ 2)) ≤ 1 - (∑ i, w i * a i) ^ 2 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hprob]
    linarith
  have hdiv := div_le_div_of_nonneg_left (sq_nonneg (∑ i, w i * b i)) hT hW
  have h := weighted_variance_gap_lower_bound w a b hw hprob hdom
  linarith

private theorem pair_reciprocal_square_identity (a b : ℝ) (h : |a| + |b| < 1) :
    b ^ 2 / (1 + a) + b ^ 2 / (1 - a) = 2 * (b ^ 2 / (1 - a ^ 2)) := by
  have hp := (pair_denom_add_pos a b h).ne'
  have hm := (pair_denom_sub_pos a b h).ne'
  have hv := (pair_variance_pos a b h).ne'
  field_simp
  ring

private theorem weighted_pair_gap_combine (w a b : ι → ℝ) (m k C : ℝ)
    (hdom : ∀ i, |a i| + |b i| < 1) (hcenter : |m| + |k| < 1)
    (hp : ((∑ i, w i * (b i) ^ 2 / (1 + a i)) - k ^ 2 / (1 + m)) * C ≤
      2 * ((∑ i, w i * (1 + a i) * psi (b i / (1 + a i))) -
        (1 + m) * psi (k / (1 + m))))
    (hm : ((∑ i, w i * (b i) ^ 2 / (1 - a i)) - k ^ 2 / (1 - m)) * C ≤
      2 * ((∑ i, w i * (1 - a i) * psi (b i / (1 - a i))) -
        (1 - m) * psi (k / (1 - m)))) :
    ((∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) - k ^ 2 / (1 - m ^ 2)) * C ≤
      2 * ((∑ i, w i * pairEntropyGap (a i) (b i)) - pairEntropyGap m k) := by
  have hv : (∑ i, w i * (b i) ^ 2 / (1 + a i)) +
      (∑ i, w i * (b i) ^ 2 / (1 - a i)) =
      2 * (∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = w i * ((b i) ^ 2 / (1 + a i) + (b i) ^ 2 / (1 - a i)) := by ring
      _ = _ := by rw [pair_reciprocal_square_identity (a i) (b i) (hdom i)]; ring
  have hvc := pair_reciprocal_square_identity m k hcenter
  have he : (∑ i, w i * (1 + a i) * psi (b i / (1 + a i))) +
      (∑ i, w i * (1 - a i) * psi (b i / (1 - a i))) =
      2 * (∑ i, w i * pairEntropyGap (a i) (b i)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pairEntropyGap_weighted (a i) (b i) (hdom i)]
    ring
  have hec : (1 + m) * psi (k / (1 + m)) + (1 - m) * psi (k / (1 - m)) =
      2 * pairEntropyGap m k := by
    rw [pairEntropyGap_weighted m k hcenter]
    ring
  have hvC := congrArg (fun z : ℝ => z * C) hv
  have hvcC := congrArg (fun z : ℝ => z * C) hvc
  nlinarith only [hp, hm, hvC, hvcC, he, hec]

theorem weighted_pair_jensen_gap (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hdom : ∀ i, |a i| + |b i| < 1) :
    (∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) -
      (∑ i, w i * b i) ^ 2 / (1 - (∑ i, w i * a i) ^ 2) ≤
      2 * ((∑ i, w i * pairEntropyGap (a i) (b i)) -
        pairEntropyGap (∑ i, w i * a i) (∑ i, w i * b i)) := by
  let m := ∑ i, w i * a i
  let k := ∑ i, w i * b i
  have hc : |m| + |k| < 1 := weighted_pair_mean_interior w a b hw hprob hdom
  have hmp : (∑ i, w i * (1 + a i)) = 1 + m := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hprob, m]
  have hmm : (∑ i, w i * (1 - a i)) = 1 - m := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hprob, m]
  have hp := weighted_perspective_gap w (fun i => 1 + a i) b (1 + m) k hw
    (fun i => pair_denom_add_pos (a i) (b i) (hdom i))
    (pair_denom_add_pos m k hc) hmp rfl
    (fun i => pair_abs_lt_denom_add (a i) (b i) (hdom i))
  have hm := weighted_perspective_gap w (fun i => 1 - a i) b (1 - m) k hw
    (fun i => pair_denom_sub_pos (a i) (b i) (hdom i))
    (pair_denom_sub_pos m k hc) hmm rfl
    (fun i => pair_abs_lt_denom_sub (a i) (b i) (hdom i))
  simpa only [mul_one] using weighted_pair_gap_combine w a b m k 1 hdom hc
    (by simpa only [mul_one] using hp) (by simpa only [mul_one] using hm)

private theorem lambda_ratio_min_le (m k t : ℝ) (hk : 0 ≤ k)
    (ht : 0 < t) (htmax : t ≤ 1 + |m|) (hkt : k < t) :
    lambda ((k / (1 + |m|)) ^ 2) ≤ lambda ((k / t) ^ 2) := by
  have hmax : 0 < 1 + |m| := by positivity
  have hx : 0 ≤ k / (1 + |m|) := div_nonneg hk hmax.le
  have hy : 0 ≤ k / t := div_nonneg hk ht.le
  have hxy := div_le_div_of_nonneg_left hk ht htmax
  have hy1 : k / t < 1 := (div_lt_one ht).mpr hkt
  apply monotoneOn_lambda
  · exact ⟨sq_nonneg _, by nlinarith⟩
  · exact ⟨sq_nonneg _, by nlinarith⟩
  · exact pow_le_pow_left₀ hx hxy 2

theorem weighted_pair_jensen_gap_strengthened (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hdom : ∀ i, |a i| + |b i| < 1) (hb : ∀ i, 0 ≤ b i) :
    ((∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) -
      (∑ i, w i * b i) ^ 2 / (1 - (∑ i, w i * a i) ^ 2)) *
        lambda (((∑ i, w i * b i) / (1 + |∑ i, w i * a i|)) ^ 2) ≤
      2 * ((∑ i, w i * pairEntropyGap (a i) (b i)) -
        pairEntropyGap (∑ i, w i * a i) (∑ i, w i * b i)) := by
  let m := ∑ i, w i * a i
  let k := ∑ i, w i * b i
  have hc : |m| + |k| < 1 := weighted_pair_mean_interior w a b hw hprob hdom
  have hk : 0 ≤ k := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hb i))
  have htp := pair_denom_add_pos m k hc
  have htm := pair_denom_sub_pos m k hc
  have hp0 : ∀ i, 0 < 1 + a i := fun i => pair_denom_add_pos (a i) (b i) (hdom i)
  have hm0 : ∀ i, 0 < 1 - a i := fun i => pair_denom_sub_pos (a i) (b i) (hdom i)
  have hmp : (∑ i, w i * (1 + a i)) = 1 + m := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hprob, m]
  have hmm : (∑ i, w i * (1 - a i)) = 1 - m := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hprob, m]
  have hp := weighted_perspective_gap_strengthened w (fun i => 1 + a i) b (1 + m) k
    hw hp0 htp hmp rfl (fun i => pair_abs_lt_denom_add (a i) (b i) (hdom i)) hb
  have hm := weighted_perspective_gap_strengthened w (fun i => 1 - a i) b (1 - m) k
    hw hm0 htm hmm rfl (fun i => pair_abs_lt_denom_sub (a i) (b i) (hdom i)) hb
  have hvp := weighted_ratio_variance_nonneg w (fun i => 1 + a i) b (1 + m) k
    hw hp0 htp hmp rfl
  have hvm := weighted_ratio_variance_nonneg w (fun i => 1 - a i) b (1 - m) k
    hw hm0 htm hmm rfl
  have hcp := lambda_ratio_min_le m k (1 + m) hk htp (by linarith [le_abs_self m])
    (by simpa only [abs_of_nonneg hk] using pair_abs_lt_denom_add m k hc)
  have hcm := lambda_ratio_min_le m k (1 - m) hk htm (by linarith [neg_le_abs m])
    (by simpa only [abs_of_nonneg hk] using pair_abs_lt_denom_sub m k hc)
  exact weighted_pair_gap_combine w a b m k _ hdom hc
    ((mul_le_mul_of_nonneg_left hcp hvp).trans hp)
    ((mul_le_mul_of_nonneg_left hcm hvm).trans hm)

end Weighted

private theorem cube_uniform_weights_sum_one (n : ℕ) :
    ∑ _ : Cube n, ((2 : ℝ) ^ n)⁻¹ = 1 := by
  simp [Cube, LeanBlast.GotsmanLinial.Cube]

private theorem cubeAverage_as_weighted_sum {n : ℕ} (f : Cube n → ℝ) :
    cubeAverage f = ∑ x, ((2 : ℝ) ^ n)⁻¹ * f x := by
  rw [cubeAverage, ← Finset.mul_sum]
  ring

theorem convexOn_cubeAverage_le {n : ℕ} (F : ℝ → ℝ) {s : Set ℝ}
    (hF : ConvexOn ℝ s F) (v : Cube n → ℝ) (hv : ∀ x, v x ∈ s) :
    F (cubeAverage v) ≤ cubeAverage (fun x => F (v x)) := by
  simp only [cubeAverage_as_weighted_sum]
  simpa only [smul_eq_mul] using hF.map_sum_le
    (fun (_ : Cube n) _ => inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))
    (cube_uniform_weights_sum_one n) (fun x _ => hv x)

theorem pair_variance_gap_lower_bound {n : ℕ} (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) :
    (cubeAverage b) ^ 2 / cubeAverage (fun x => 1 - (a x) ^ 2) -
        (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2) ≤
      cubeAverage (fun x => (b x) ^ 2 / (1 - (a x) ^ 2)) -
        (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2) := by
  simpa only [cubeAverage_as_weighted_sum, ← mul_div_assoc] using
    weighted_variance_gap_lower_bound (fun _ => ((2 : ℝ) ^ n)⁻¹) a b
      (fun _ => by positivity) (cube_uniform_weights_sum_one n) hdom

theorem pair_variance_gap_nonneg {n : ℕ} (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) :
    0 ≤ cubeAverage (fun x => (b x) ^ 2 / (1 - (a x) ^ 2)) -
      (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2) := by
  simpa only [cubeAverage_as_weighted_sum, ← mul_div_assoc] using
    weighted_variance_gap_nonneg (fun _ => ((2 : ℝ) ^ n)⁻¹) a b
      (fun _ => by positivity) (cube_uniform_weights_sum_one n) hdom

theorem pair_jensen_gap {n : ℕ} (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) :
    cubeAverage (fun x => (b x) ^ 2 / (1 - (a x) ^ 2)) -
      (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2) ≤
      2 * (cubeAverage (fun x => pairEntropyGap (a x) (b x)) -
        pairEntropyGap (cubeAverage a) (cubeAverage b)) := by
  simpa only [cubeAverage_as_weighted_sum, ← mul_div_assoc] using
    weighted_pair_jensen_gap (fun _ => ((2 : ℝ) ^ n)⁻¹) a b
      (fun _ => by positivity) (cube_uniform_weights_sum_one n) hdom

theorem pair_jensen_gap_strengthened {n : ℕ} (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) (hb : ∀ x, 0 ≤ b x) :
    (cubeAverage (fun x => (b x) ^ 2 / (1 - (a x) ^ 2)) -
      (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2)) *
        lambda (((cubeAverage b) / (1 + |cubeAverage a|)) ^ 2) ≤
      2 * (cubeAverage (fun x => pairEntropyGap (a x) (b x)) -
        pairEntropyGap (cubeAverage a) (cubeAverage b)) := by
  simpa only [cubeAverage_as_weighted_sum, ← mul_div_assoc] using
    weighted_pair_jensen_gap_strengthened (fun _ => ((2 : ℝ) ^ n)⁻¹) a b
      (fun _ => by positivity) (cube_uniform_weights_sum_one n) hdom hb

theorem pair_jensen_gap_nonneg {n : ℕ} (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) :
    pairEntropyGap (cubeAverage a) (cubeAverage b) ≤
      cubeAverage (fun x => pairEntropyGap (a x) (b x)) := by
  have hv := pair_variance_gap_nonneg a b hdom
  have hj := pair_jensen_gap a b hdom
  linarith

end LeanBlast.CourtadeKumar

end

end OAI
