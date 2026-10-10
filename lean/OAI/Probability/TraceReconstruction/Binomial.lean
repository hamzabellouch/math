import Mathlib

namespace OAI

/-!
# Binomial

Fair and biased binomial laws, generating series, differences, concentration, Gaussian overlap, hidden counts, and local lower bounds.
-/

open scoped ENNReal
noncomputable section

namespace TraceReconstruction

/-! ## Quantitative fair-binomial anti-concentration

A direct inductive bound, avoiding an unformalized appeal to Stirling.
It is one of the estimates needed for signed binomial smoothing and
for the local/global anchor kernels.
-/

/-- Fair-binomial mass, extended by zero beyond its natural support. -/
def fairBinomial (n k : ℕ) : ℝ := (n.choose k : ℝ) / 2 ^ n

theorem fairBinomial_nonneg (n k : ℕ) : 0 ≤ fairBinomial n k := by
  unfold fairBinomial
  positivity

theorem centralBinom_square_bound (n : ℕ) :
    ((n : ℝ) + 1) * (n.centralBinom : ℝ) ^ 2 ≤ (16 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hr : ((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ) =
        2 * (2 * n + 1) * (n.centralBinom : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hc : 4 * (2 * (n : ℝ) + 1) ^ 2 * (n + 2) ≤
        16 * (n + 1) ^ 3 := by nlinarith [sq_nonneg (n : ℝ)]
    have hh : ((n : ℝ) + 1) ^ 2 *
        ((n + 2) * ((n + 1).centralBinom : ℝ) ^ 2) ≤
        ((n : ℝ) + 1) ^ 2 * (16 * 16 ^ n) := by
      calc
        _ = (n + 2) * (((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ)) ^ 2 := by ring
        _ = (4 * (2 * (n : ℝ) + 1) ^ 2 * (n + 2)) *
            (n.centralBinom : ℝ) ^ 2 := by rw [hr]; ring
        _ ≤ (16 * ((n : ℝ) + 1) ^ 3) * (n.centralBinom : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hc (sq_nonneg _)
        _ = (16 * ((n : ℝ) + 1) ^ 2) *
            (((n : ℝ) + 1) * (n.centralBinom : ℝ) ^ 2) := by ring
        _ ≤ (16 * ((n : ℝ) + 1) ^ 2) * 16 ^ n :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = _ := by ring
    have := (mul_le_mul_iff_right₀ (sq_pos_of_pos hn)).mp hh
    rw [pow_succ (16 : ℝ) n]
    convert this using 1 <;> push_cast <;> first | rfl | ring

theorem choose_odd_le_twice_central (n k : ℕ) :
    (2 * n + 1).choose k ≤ 2 * n.centralBinom := by
  cases k with
  | zero => simp only [Nat.choose_zero_right]; have := Nat.centralBinom_pos n; omega
  | succ k =>
    rw [Nat.choose_succ_succ]
    have h₁ := Nat.choose_le_centralBinom k n
    have h₂ := Nat.choose_le_centralBinom (k + 1) n
    simpa [Nat.succ_eq_add_one, two_mul] using Nat.add_le_add h₁ h₂

theorem fairBinomial_square_bound (n k : ℕ) :
    ((n : ℝ) + 1) * fairBinomial n k ^ 2 ≤ 2 := by
  have hcases : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  rcases hcases with he | ho
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have hc : ((2 * m).choose k : ℝ) ≤ (m.centralBinom : ℝ) :=
      by exact_mod_cast Nat.choose_le_centralBinom k m
    have hcs : ((2 * m).choose k : ℝ) ^ 2 ≤ (m.centralBinom : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hc 2
    have ht := centralBinom_square_bound m
    have hp : ((2 : ℝ) ^ (2 * m)) ^ 2 = 16 ^ m := by
      rw [← pow_mul, show 2 * m * 2 = 4 * m by omega, pow_mul]
      norm_num
    unfold fairBinomial
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (2 ^ (2 * m)) ^ 2)]
    rw [hp]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hcs (show (0 : ℝ) ≤ m + 1 by positivity),
      sq_nonneg ((2 * m).choose k : ℝ)]
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    have hc : ((2 * m + 1).choose k : ℝ) ≤ 2 * (m.centralBinom : ℝ) :=
      by exact_mod_cast choose_odd_le_twice_central m k
    have hcs : ((2 * m + 1).choose k : ℝ) ^ 2 ≤ 4 * (m.centralBinom : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((2 * m + 1).choose k : ℝ)) hc 2
      nlinarith
    have ht := centralBinom_square_bound m
    have hp : ((2 : ℝ) ^ (2 * m + 1)) ^ 2 = 4 * 16 ^ m := by
      rw [pow_add, mul_pow, ← pow_mul, show 2 * m * 2 = 4 * m by omega, pow_mul]
      norm_num
      ring
    unfold fairBinomial
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (2 ^ (2 * m + 1)) ^ 2)]
    rw [hp]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hcs (show (0 : ℝ) ≤ m + 1 by positivity)]


/-! ## Discrete convolution estimates for the hidden displacement kernels -/

abbrev IntSeries := AddMonoidAlgebra ℝ ℤ

def seriesL1 (f : IntSeries) : ℝ := ∑' z : ℤ, |f.coeff z|
def seriesL2Sq (f : IntSeries) : ℝ := ∑' z : ℤ, f.coeff z ^ 2

theorem series_summable (f : IntSeries) (φ : ℝ → ℝ) (hφ : φ 0 = 0) :
    Summable (fun z : ℤ => φ (f.coeff z)) :=
  summable_of_hasFiniteSupport (f.coeff.hasFiniteSupport.fun_comp hφ)

theorem seriesL1_nonneg (f : IntSeries) : 0 ≤ seriesL1 f :=
  tsum_nonneg fun _ => abs_nonneg _

theorem seriesL2Sq_nonneg (f : IntSeries) : 0 ≤ seriesL2Sq f :=
  tsum_nonneg fun _ => sq_nonneg _

theorem seriesL1_eq_sum (f : IntSeries) :
    seriesL1 f = ∑ z ∈ f.coeff.support, |f.coeff z| := by
  apply tsum_eq_sum
  intro z hz
  simp [Finsupp.notMem_support_iff.mp hz]

theorem seriesL2Sq_eq_sum (f : IntSeries) :
    seriesL2Sq f = ∑ z ∈ f.coeff.support, f.coeff z ^ 2 := by
  apply tsum_eq_sum
  intro z hz
  simp [Finsupp.notMem_support_iff.mp hz]

theorem series_summable_shift (f : IntSeries) (φ : ℝ → ℝ)
    (hφ : φ 0 = 0) (a : ℤ) :
    Summable (fun z : ℤ => φ (f.coeff (a + z))) := by
  exact (Equiv.addLeft a).summable_iff.mpr (series_summable f φ hφ)

theorem series_sum_shift (f : IntSeries) (φ : ℝ → ℝ) (a : ℤ) :
    (∑' z : ℤ, φ (f.coeff (a + z))) = ∑' z : ℤ, φ (f.coeff z) :=
  (Equiv.addLeft a).tsum_eq (fun z => φ (f.coeff z))

theorem series_coeff_mul_abs_le (f g : IntSeries) (z : ℤ) :
    |(f * g).coeff z| ≤ ∑ a ∈ f.coeff.support, |f.coeff a| * |g.coeff (-a + z)| := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
  simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
    (fun a => f.coeff a * g.coeff (-a + z)) f.coeff.support

theorem seriesL1_mul_le (f g : IntSeries) :
    seriesL1 (f * g) ≤ seriesL1 f * seriesL1 g := by
  have hh (a : ℤ) : Summable (fun z : ℤ => |f.coeff a| * |g.coeff (-a + z)|) :=
    (series_summable_shift g abs (by simp) (-a)).mul_left _
  calc
    seriesL1 (f * g) ≤ ∑' z : ℤ, ∑ a ∈ f.coeff.support,
        |f.coeff a| * |g.coeff (-a + z)| :=
      Summable.tsum_le_tsum (series_coeff_mul_abs_le f g) (series_summable (f * g) abs (by simp))
        (summable_sum fun a _ => hh a)
    _ = ∑ a ∈ f.coeff.support, ∑' z : ℤ, |f.coeff a| * |g.coeff (-a + z)| :=
      Summable.tsum_finsetSum fun a _ => hh a
    _ = (∑ a ∈ f.coeff.support, |f.coeff a|) * seriesL1 g := by
      simp_rw [tsum_mul_left, series_sum_shift]
      exact (Finset.sum_mul _ _ _).symm
    _ = seriesL1 f * seriesL1 g := by rw [seriesL1_eq_sum f]

theorem series_coeff_mul_sq_le (f g : IntSeries) (z : ℤ) :
    (f * g).coeff z ^ 2 ≤ seriesL1 f *
      ∑ a ∈ f.coeff.support, |f.coeff a| * (g.coeff (-a + z)) ^ 2 := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum, seriesL1_eq_sum]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro a _; exact abs_nonneg _
  · intro a _; positivity
  · intro a _
    rw [mul_pow, ← mul_assoc, ← sq, sq_abs]

theorem seriesL2Sq_mul_le (f g : IntSeries) :
    seriesL2Sq (f * g) ≤ seriesL1 f ^ 2 * seriesL2Sq g := by
  have hh (a : ℤ) : Summable (fun z : ℤ => |f.coeff a| * (g.coeff (-a + z)) ^ 2) :=
    (series_summable_shift g (fun x => x ^ 2) (by simp) (-a)).mul_left _
  calc
    seriesL2Sq (f * g) ≤ ∑' z : ℤ, seriesL1 f *
        ∑ a ∈ f.coeff.support, |f.coeff a| * (g.coeff (-a + z)) ^ 2 :=
      Summable.tsum_le_tsum (series_coeff_mul_sq_le f g)
        (series_summable (f * g) (fun x => x ^ 2) (by simp))
        ((summable_sum fun a _ => hh a).mul_left _)
    _ = seriesL1 f * ∑ a ∈ f.coeff.support,
        ∑' z : ℤ, |f.coeff a| * (g.coeff (-a + z)) ^ 2 := by
      rw [tsum_mul_left, Summable.tsum_finsetSum fun a _ => hh a]
    _ = seriesL1 f ^ 2 * seriesL2Sq g := by
      simp_rw [tsum_mul_left, series_sum_shift g (fun x => x ^ 2)]
      rw [← Finset.sum_mul, ← seriesL1_eq_sum]
      unfold seriesL2Sq
      ring

theorem series_coeff_mul_bound (f g : IntSeries) (M : ℝ)
    (hg : ∀ z, |g.coeff z| ≤ M) (z : ℤ) :
    |(f * g).coeff z| ≤ seriesL1 f * M := by
  calc
    _ ≤ ∑ a ∈ f.coeff.support, |f.coeff a| * |g.coeff (-a + z)| :=
      series_coeff_mul_abs_le f g z
    _ ≤ ∑ a ∈ f.coeff.support, |f.coeff a| * M :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hg _) (abs_nonneg _)
    _ = seriesL1 f * M := by rw [← Finset.sum_mul, ← seriesL1_eq_sum]

/-! The probability generating series of the fair binomial kernel. -/
def fairSeries (n : ℕ) : IntSeries :=
  (AddMonoidAlgebra.single 1 (1 / 2) + AddMonoidAlgebra.single 0 (1 / 2)) ^ n

theorem fairSeries_add (m n : ℕ) : fairSeries (m + n) = fairSeries m * fairSeries n :=
  pow_add _ m n

theorem fairSeries_sum (n : ℕ) :
    fairSeries n = ∑ k ∈ Finset.range (n + 1),
      AddMonoidAlgebra.single (k : ℤ) (fairBinomial n k) := by
  unfold fairSeries
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  rw [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.single_mul_single]
  simp only [nsmul_eq_mul, mul_one, mul_zero, add_zero]
  congr 1
  rw [← pow_add, Nat.add_sub_of_le hkn]
  unfold fairBinomial
  rw [div_pow]
  simp [div_eq_mul_inv, mul_comm]

theorem fairSeries_coeff_nat (n k : ℕ) :
    (fairSeries n).coeff (k : ℤ) = fairBinomial n k := by
  rw [fairSeries_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  by_cases hk : k ≤ n
  · rw [Finset.sum_eq_single k]
    · simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_true]
    · intro b _ hb
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Nat.cast_inj, ite_eq_right hb]
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  · rw [Finset.sum_eq_zero]
    · simp [fairBinomial, Nat.choose_eq_zero_of_lt (by omega : n < k)]
    · intro b hb
      have hbk : b ≠ k := by simp only [Finset.mem_range] at hb; omega
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Nat.cast_inj, ite_eq_right hbk]

theorem fairSeries_coeff_neg (n : ℕ) (z : ℤ) (hz : z < 0) :
    (fairSeries n).coeff z = 0 := by
  rw [fairSeries_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b _
  have h : (b : ℤ) ≠ z := by omega
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right h]

theorem seriesL1_eq_sum_range (f : IntSeries) (n : ℕ)
    (hneg : ∀ z < 0, f.coeff z = 0)
    (hhigh : ∀ k : ℕ, n < k → f.coeff k = 0) :
    seriesL1 f = ∑ k ∈ Finset.range (n + 1), |f.coeff (k : ℤ)| := by
  let e : ℕ ↪ ℤ := ⟨Nat.cast, Nat.cast_injective⟩
  calc
    seriesL1 f = ∑ z ∈ (Finset.range (n + 1)).map e, |f.coeff z| := by
      apply tsum_eq_sum
      intro z hz
      by_cases h : 0 ≤ z
      · have heq : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg h
        have hh : n < z.toNat := by
          by_contra hn
          apply hz
          exact Finset.mem_map.mpr ⟨z.toNat, Finset.mem_range.mpr (by omega), heq⟩
        rw [← heq, hhigh _ hh, abs_zero]
      · rw [hneg z (by omega), abs_zero]
    _ = _ := Finset.sum_map _ e _

def firstDifference : IntSeries :=
  AddMonoidAlgebra.single 0 1 - AddMonoidAlgebra.single 1 1

theorem firstDifference_coeff (f : IntSeries) (z : ℤ) :
    (firstDifference * f).coeff z = f.coeff z - f.coeff (z - 1) := by
  rw [firstDifference, sub_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    mul_comm _ f, AddMonoidAlgebra.coeff_mul_single_apply,
    mul_comm _ f, AddMonoidAlgebra.coeff_mul_single_apply]
  simp only [neg_zero, add_zero, mul_one, sub_eq_add_neg]

theorem fairSeries_difference_coeff_zero (n : ℕ) :
    (firstDifference * fairSeries n).coeff 0 = fairBinomial n 0 := by
  rw [firstDifference_coeff]
  norm_num only [zero_sub]
  rw [fairSeries_coeff_neg n (-1) (by norm_num), sub_zero]
  exact fairSeries_coeff_nat n 0

theorem fairSeries_difference_coeff_succ (n k : ℕ) :
    (firstDifference * fairSeries n).coeff (↑(k + 1) : ℤ) =
      fairBinomial n (k + 1) - fairBinomial n k := by
  rw [firstDifference_coeff, fairSeries_coeff_nat]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, fairSeries_coeff_nat]

theorem fairBinomial_unimodal_left (n k : ℕ) (hk : k < n / 2) :
    fairBinomial n k ≤ fairBinomial n (k + 1) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.choose_le_succ_of_lt_half_left hk

theorem fairBinomial_unimodal_right (n k : ℕ) (hk : n / 2 ≤ k) :
    fairBinomial n (k + 1) ≤ fairBinomial n k := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hnk : n - k ≤ k + 1 := by omega
  have hmul := Nat.mul_le_mul_left (n.choose k) hnk
  rw [← Nat.choose_succ_right_eq] at hmul
  exact_mod_cast Nat.le_of_mul_le_mul_right hmul (by omega : 0 < k + 1)

theorem fairBinomial_variation (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), |fairBinomial n (k + 1) - fairBinomial n k|) =
      2 * fairBinomial n (n / 2) - fairBinomial n 0 := by
  have hmid : n / 2 ≤ n + 1 := by omega
  rw [← Finset.sum_range_add_sum_Ico _ hmid]
  have hl : (∑ k ∈ Finset.range (n / 2),
      |fairBinomial n (k + 1) - fairBinomial n k|) =
      fairBinomial n (n / 2) - fairBinomial n 0 := by
    rw [← Finset.sum_range_sub (fairBinomial n) (n / 2)]
    apply Finset.sum_congr rfl
    intro k hk
    exact abs_of_nonneg (sub_nonneg.mpr
      (fairBinomial_unimodal_left n k (Finset.mem_range.mp hk)))
  have hr : (∑ k ∈ Finset.Ico (n / 2) (n + 1),
      |fairBinomial n (k + 1) - fairBinomial n k|) =
      fairBinomial n (n / 2) - fairBinomial n (n + 1) := by
    calc
      _ = ∑ k ∈ Finset.Ico (n / 2) (n + 1),
          -(fairBinomial n (k + 1) - fairBinomial n k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact abs_of_nonpos (sub_nonpos.mpr
          (fairBinomial_unimodal_right n k (Finset.mem_Ico.mp hk).1))
      _ = _ := by rw [Finset.sum_neg_distrib, Finset.sum_Ico_sub _ hmid]; ring
  rw [hl, hr]
  have hzero : fairBinomial n (n + 1) = 0 := by simp [fairBinomial]
  rw [hzero]
  ring

theorem fairSeries_difference_L1 (n : ℕ) :
    seriesL1 (firstDifference * fairSeries n) = 2 * fairBinomial n (n / 2) := by
  rw [seriesL1_eq_sum_range _ (n + 1)]
  · rw [Finset.sum_range_succ', Nat.cast_zero, fairSeries_difference_coeff_zero,
      abs_of_nonneg (fairBinomial_nonneg n 0)]
    simp_rw [fairSeries_difference_coeff_succ]
    rw [fairBinomial_variation]
    ring
  · intro z hz
    rw [firstDifference_coeff, fairSeries_coeff_neg n z hz,
      fairSeries_coeff_neg n (z - 1) (by omega), sub_zero]
  · intro k hk
    have hkpos : 0 < k := by omega
    obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
    rw [fairSeries_difference_coeff_succ]
    simp [fairBinomial, Nat.choose_eq_zero_of_lt (by omega : n < v),
      Nat.choose_eq_zero_of_lt (by omega : n < v + 1)]

def binomialBound (n : ℕ) : ℝ := Real.sqrt (2 / ((n : ℝ) + 1))

theorem binomialBound_nonneg (n : ℕ) : 0 ≤ binomialBound n := Real.sqrt_nonneg _

theorem fairBinomial_le_bound (n k : ℕ) : fairBinomial n k ≤ binomialBound n := by
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
  simpa only [mul_comm] using fairBinomial_square_bound n k

theorem fairSeries_nonneg (n : ℕ) (z : ℤ) : 0 ≤ (fairSeries n).coeff z := by
  by_cases hz : 0 ≤ z
  · rw [← Int.toNat_of_nonneg hz, fairSeries_coeff_nat]
    exact fairBinomial_nonneg _ _
  · rw [fairSeries_coeff_neg n z (by omega)]

theorem fairSeries_coeff_bound (n : ℕ) (z : ℤ) :
    |(fairSeries n).coeff z| ≤ binomialBound n := by
  by_cases hz : 0 ≤ z
  · rw [← Int.toNat_of_nonneg hz, fairSeries_coeff_nat,
      abs_of_nonneg (fairBinomial_nonneg _ _)]
    exact fairBinomial_le_bound _ _
  · rw [fairSeries_coeff_neg n z (by omega), abs_zero]
    exact binomialBound_nonneg n

theorem fairSeries_L1 (n : ℕ) : seriesL1 (fairSeries n) = 1 := by
  rw [seriesL1_eq_sum_range _ n (fairSeries_coeff_neg n)]
  · simp_rw [fairSeries_coeff_nat, abs_of_nonneg (fairBinomial_nonneg _ _)]
    unfold fairBinomial
    rw [← Finset.sum_div]
    have hsum : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ)) = (2 : ℝ) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    rw [hsum, div_self (by positivity)]
  · intro k hk
    rw [fairSeries_coeff_nat]
    simp [fairBinomial, Nat.choose_eq_zero_of_lt hk]

theorem seriesL2Sq_le_L1_mul_bound (f : IntSeries) (M : ℝ)
    (hf : ∀ z, |f.coeff z| ≤ M) : seriesL2Sq f ≤ seriesL1 f * M := by
  calc
    _ ≤ ∑' z : ℤ, |f.coeff z| * M := by
      apply Summable.tsum_le_tsum
      · intro z
        calc
          f.coeff z ^ 2 = |f.coeff z| * |f.coeff z| := by rw [← sq, sq_abs]
          _ ≤ _ := mul_le_mul_of_nonneg_left (hf z) (abs_nonneg _)
      · exact series_summable f (fun x => x ^ 2) (by simp)
      · exact (series_summable f abs (by simp)).mul_right M
    _ = _ := tsum_mul_right

theorem fairSeries_L2Sq_bound (n : ℕ) : seriesL2Sq (fairSeries n) ≤ binomialBound n := by
  simpa only [fairSeries_L1, one_mul] using
    seriesL2Sq_le_L1_mul_bound (fairSeries n) (binomialBound n) (fairSeries_coeff_bound n)

theorem fairSeries_difference_L1_bound (n : ℕ) :
    seriesL1 (firstDifference * fairSeries n) ≤ 2 * binomialBound n := by
  rw [fairSeries_difference_L1]
  exact mul_le_mul_of_nonneg_left (fairBinomial_le_bound n (n / 2)) (by norm_num)

theorem seriesL1_single (z : ℤ) (r : ℝ) :
    seriesL1 (AddMonoidAlgebra.single z r) = |r| := by
  unfold seriesL1
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp only [apply_ite abs, abs_zero]
  exact tsum_ite_eq' z (fun _ : ℤ => |r|)

theorem seriesL1_one : seriesL1 (1 : IntSeries) = 1 := by
  change seriesL1 (AddMonoidAlgebra.single 0 1) = 1
  rw [seriesL1_single, abs_one]

theorem seriesL1_pow_le (f : IntSeries) (s : ℕ) : seriesL1 (f ^ s) ≤ seriesL1 f ^ s := by
  induction s with
  | zero => simp only [pow_zero, seriesL1_one, le_refl]
  | succ s ih =>
    rw [pow_succ, pow_succ]
    exact (seriesL1_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (seriesL1_nonneg f))

theorem fairSeries_mul_power (n s : ℕ) :
    firstDifference ^ s * fairSeries ((s + 1) * n) =
      (firstDifference * fairSeries n) ^ s * fairSeries n := by
  simp only [fairSeries, add_mul, one_mul, pow_add, pow_mul, mul_pow]
  ring

/-- Quantitative higher-order smoothing, with n trials assigned to each
    difference and one further group reserved for anti-concentration. -/
theorem binomial_difference_coeff_bound (n s : ℕ) (z : ℤ) :
    |(firstDifference ^ s * fairSeries ((s + 1) * n)).coeff z| ≤
      (2 * binomialBound n) ^ s * binomialBound n := by
  rw [fairSeries_mul_power]
  apply (series_coeff_mul_bound _ _ _ (fairSeries_coeff_bound n) z).trans
  apply mul_le_mul_of_nonneg_right _ (binomialBound_nonneg n)
  exact (seriesL1_pow_le _ _).trans
    (pow_le_pow_left₀ (seriesL1_nonneg _) (fairSeries_difference_L1_bound n) s)

theorem binomial_difference_L2Sq_bound (n s : ℕ) :
    seriesL2Sq (firstDifference ^ s * fairSeries ((s + 1) * n)) ≤
      ((2 * binomialBound n) ^ s) ^ 2 * binomialBound n := by
  rw [fairSeries_mul_power]
  apply (seriesL2Sq_mul_le _ _).trans
  apply mul_le_mul
  · apply pow_le_pow_left₀ (seriesL1_nonneg _)
    exact (seriesL1_pow_le _ _).trans
      (pow_le_pow_left₀ (seriesL1_nonneg _) (fairSeries_difference_L1_bound n) s)
  · exact fairSeries_L2Sq_bound n
  · exact seriesL2Sq_nonneg _
  · positivity

theorem seriesL1_add_le (f g : IntSeries) :
    seriesL1 (f + g) ≤ seriesL1 f + seriesL1 g := by
  calc
    _ ≤ ∑' z : ℤ, (|f.coeff z| + |g.coeff z|) := by
      apply Summable.tsum_le_tsum
      · intro z
        simpa only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
          abs_add_le (f.coeff z) (g.coeff z)
      · exact series_summable (f + g) abs (by simp)
      · exact (series_summable f abs (by simp)).add (series_summable g abs (by simp))
    _ = _ := (series_summable f abs (by simp)).tsum_add (series_summable g abs (by simp))

theorem seriesL1_zero : seriesL1 (0 : IntSeries) = 0 := by
  simp [seriesL1]

theorem seriesL1_sum_le {ι : Type*} (A : Finset ι) (f : ι → IntSeries) :
    seriesL1 (∑ i ∈ A, f i) ≤ ∑ i ∈ A, seriesL1 (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, seriesL1_zero, le_refl]
  | @insert a A ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (seriesL1_add_le _ _).trans (add_le_add le_rfl ih)

theorem seriesL1_prod_le {ι : Type*} (A : Finset ι) (f : ι → IntSeries) :
    seriesL1 (∏ i ∈ A, f i) ≤ ∏ i ∈ A, seriesL1 (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, seriesL1_one, le_refl]
  | @insert a A ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (seriesL1_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (seriesL1_nonneg _))

def geomSeries (k : ℕ) : IntSeries := ∑ a ∈ Finset.range k, (AddMonoidAlgebra.single 1 1) ^ a

def prouhetSeries (s : ℕ) : IntSeries :=
  ∏ v ∈ Finset.range s, (1 - (AddMonoidAlgebra.single 1 1) ^ (2 ^ v))

def prouhetQuotient (s : ℕ) : IntSeries :=
  ∏ v ∈ Finset.range s, geomSeries (2 ^ v)

theorem geomSeries_difference (k : ℕ) :
    geomSeries k * firstDifference = 1 - (AddMonoidAlgebra.single 1 1 : IntSeries) ^ k := by
  exact geom_sum_mul_neg _ _

theorem geomSeries_L1_le (k : ℕ) : seriesL1 (geomSeries k) ≤ k := by
  apply (seriesL1_sum_le _ _).trans
  simp only [AddMonoidAlgebra.single_pow, one_pow, seriesL1_single, abs_one,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, le_refl]

theorem prouhetSeries_factor (s : ℕ) :
    prouhetSeries s = prouhetQuotient s * firstDifference ^ s := by
  unfold prouhetSeries prouhetQuotient
  simp_rw [← geomSeries_difference]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_range]

theorem prouhetQuotient_L1_le (s : ℕ) :
    seriesL1 (prouhetQuotient s) ≤ (2 : ℝ) ^ (s * s) := by
  calc
    _ ≤ ∏ v ∈ Finset.range s, seriesL1 (geomSeries (2 ^ v)) := seriesL1_prod_le _ _
    _ ≤ ∏ _v ∈ Finset.range s, ((2 : ℝ) ^ s) := by
      apply Finset.prod_le_prod₀
      · intro v _; exact seriesL1_nonneg _
      · intro v hv
        apply (geomSeries_L1_le _).trans
        push_cast
        apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        exact (Finset.mem_range.mp hv).le
    _ = _ := by simp only [Finset.prod_const, Finset.card_range, ← pow_mul]

/-- Prouhet smoothing in an explicit finite-trial form.  The constants
    2^(s*s) and (2 sqrt(2/(n+1)))^s are exp(O(s^2)) after assigning
    n = floor(g/(s+1)) trials to each group.  No Fourier theorem or
    probabilistic estimate is assumed. -/
theorem prouhet_binomial_coeff_bound (n s : ℕ) (z : ℤ) :
    |(prouhetSeries s * fairSeries ((s + 1) * n)).coeff z| ≤
      (2 : ℝ) ^ (s * s) * ((2 * binomialBound n) ^ s * binomialBound n) := by
  rw [prouhetSeries_factor, mul_assoc]
  apply (series_coeff_mul_bound _ _ _ (binomial_difference_coeff_bound n s) z).trans
  exact mul_le_mul_of_nonneg_right (prouhetQuotient_L1_le s)
    (by positivity [binomialBound_nonneg n])

theorem prouhet_binomial_L2Sq_bound (n s : ℕ) :
    seriesL2Sq (prouhetSeries s * fairSeries ((s + 1) * n)) ≤
      ((2 : ℝ) ^ (s * s)) ^ 2 * (((2 * binomialBound n) ^ s) ^ 2 * binomialBound n) := by
  rw [prouhetSeries_factor, mul_assoc]
  apply (seriesL2Sq_mul_le _ _).trans
  apply mul_le_mul
  · exact pow_le_pow_left₀ (seriesL1_nonneg _) (prouhetQuotient_L1_le s) 2
  · exact binomial_difference_L2Sq_bound n s
  · exact seriesL2Sq_nonneg _
  · positivity

/-- Arbitrary trial counts are obtained by convolving with the independent
    unused trials; this cannot enlarge the coefficient or squared-L2 bounds. -/
theorem prouhet_binomial_coeff_bound_remainder (n s r : ℕ) (z : ℤ) :
    |(prouhetSeries s * fairSeries ((s + 1) * n + r)).coeff z| ≤
      (2 : ℝ) ^ (s * s) * ((2 * binomialBound n) ^ s * binomialBound n) := by
  rw [fairSeries_add, ← mul_assoc, mul_comm (prouhetSeries s * _)]
  simpa only [fairSeries_L1, one_mul] using
    series_coeff_mul_bound (fairSeries r) (prouhetSeries s * fairSeries ((s + 1) * n))
      _ (prouhet_binomial_coeff_bound n s) z

theorem prouhet_binomial_L2Sq_bound_remainder (n s r : ℕ) :
    seriesL2Sq (prouhetSeries s * fairSeries ((s + 1) * n + r)) ≤
      ((2 : ℝ) ^ (s * s)) ^ 2 * (((2 * binomialBound n) ^ s) ^ 2 * binomialBound n) := by
  rw [fairSeries_add, ← mul_assoc, mul_comm (prouhetSeries s * _)]
  calc
    _ ≤ seriesL1 (fairSeries r) ^ 2 *
        seriesL2Sq (prouhetSeries s * fairSeries ((s + 1) * n)) := seriesL2Sq_mul_le _ _
    _ ≤ _ := by simpa only [fairSeries_L1, one_pow, one_mul] using
        prouhet_binomial_L2Sq_bound n s

theorem signed_binomial_smoothing (g s : ℕ) :
    (∀ z : ℤ, |(prouhetSeries s * fairSeries g).coeff z| ≤
      (2 : ℝ) ^ (s * s) * ((2 * binomialBound (g / (s + 1))) ^ s *
        binomialBound (g / (s + 1)))) ∧
    (seriesL2Sq (prouhetSeries s * fairSeries g) ≤
      ((2 : ℝ) ^ (s * s)) ^ 2 * (((2 * binomialBound (g / (s + 1))) ^ s) ^ 2 *
        binomialBound (g / (s + 1)))) := by
  have hg : (s + 1) * (g / (s + 1)) + g % (s + 1) = g := Nat.div_add_mod g (s + 1)
  constructor
  · intro z
    simpa only [hg] using prouhet_binomial_coeff_bound_remainder (g / (s + 1)) s
      (g % (s + 1)) z
  · simpa only [hg] using prouhet_binomial_L2Sq_bound_remainder (g / (s + 1)) s
      (g % (s + 1))

theorem binomialBound_quotient_le (g s : ℕ) :
    binomialBound (g / (s + 1)) ≤
      Real.sqrt (2 * ((s : ℝ) + 1) / ((g : ℝ) + 1)) := by
  apply Real.sqrt_le_sqrt
  have hn : g + 1 ≤ (g / (s + 1) + 1) * (s + 1) := by
    have hmod := Nat.mod_lt g (by omega : 0 < s + 1)
    have hdiv := Nat.div_add_mod g (s + 1)
    nlinarith
  have hnr : (g : ℝ) + 1 ≤ ((g / (s + 1) : ℕ) + (1 : ℝ)) * ((s : ℝ) + 1) := by
    exact_mod_cast hn
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (g / (s + 1) : ℕ) + 1)
    (by positivity : (0 : ℝ) < g + 1)).mpr
  nlinarith

theorem prouhetSeries_succ_coeff (s : ℕ) (z : ℤ) :
    (prouhetSeries (s + 1)).coeff z =
    (prouhetSeries s).coeff z - (prouhetSeries s).coeff (z - (2 ^ s : ℕ)) := by
  rw [prouhetSeries, Finset.prod_range_succ, mul_sub, mul_one]
  change (prouhetSeries s - prouhetSeries s *
    (AddMonoidAlgebra.single 1 1 : IntSeries) ^ (2 ^ s)).coeff z = _
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  simp only [AddMonoidAlgebra.single_pow, one_pow, nsmul_eq_mul, mul_one,
    AddMonoidAlgebra.coeff_mul_single_apply, sub_eq_add_neg]

/-- The exact generating polynomial from the manuscript has unit signed
    coefficients at every index 0,...,2^s-1, and no other coefficients. -/
theorem prouhetSeries_coeff_spec (s : ℕ) :
    (∀ z : ℤ, (z < 0 ∨ (2 ^ s : ℕ) ≤ z) → (prouhetSeries s).coeff z = 0) ∧
    (∀ z : ℤ, 0 ≤ z → z < (2 ^ s : ℕ) → |(prouhetSeries s).coeff z| = 1) := by
  induction s with
  | zero =>
    have hcoeff (z : ℤ) : (prouhetSeries 0).coeff z = if 0 = z then 1 else 0 := by
      change (AddMonoidAlgebra.single 0 (1 : ℝ)).coeff z = _
      exact Finsupp.single_apply
    constructor
    · intro z hz
      rw [hcoeff, ite_eq_right]
      norm_num only [pow_zero, Nat.cast_one] at hz
      omega
    · intro z h0 h1
      have hz : z = 0 := by norm_num only [pow_zero, Nat.cast_one] at h1; omega
      subst hz
      rw [hcoeff, ite_eq_left rfl, abs_one]
  | succ s ih =>
    have hp : (0 : ℤ) < (2 ^ s : ℕ) := by positivity
    have hd : ((2 ^ (s + 1) : ℕ) : ℤ) = 2 * (2 ^ s : ℕ) := by push_cast; ring
    constructor
    · intro z hz
      rw [prouhetSeries_succ_coeff]
      rcases hz with hz | hz
      · rw [ih.1 z (Or.inl hz), ih.1 _ (Or.inl (by omega)), sub_zero]
      · rw [hd] at hz
        rw [ih.1 z (Or.inr (by omega)), ih.1 _ (Or.inr (by omega)), sub_zero]
    · intro z h0 h1
      rw [hd] at h1
      rw [prouhetSeries_succ_coeff]
      by_cases hz : z < (2 ^ s : ℕ)
      · rw [ih.1 (z - (2 ^ s : ℕ)) (Or.inl (by omega)), sub_zero]
        exact ih.2 z h0 hz
      · rw [ih.1 z (Or.inr (by omega)), zero_sub, abs_neg]
        exact ih.2 _ (by omega) (by omega)


/-! ## Nonfair anti-concentration without an assumed Stirling estimate -/

def binomialMass (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

theorem binomialMass_nonneg (n k : ℕ) {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    0 ≤ binomialMass n p k := by
  unfold binomialMass
  positivity [hp.1, sub_nonneg.mpr hp.2]

theorem sum_binomialMass (n : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (n + 1), binomialMass n p k = 1 := by
  have h := add_pow p (1 - p) n
  rw [show p + (1 - p) = 1 by ring, one_pow] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  unfold binomialMass
  ring

theorem binomialMass_harmonic_step (n k : ℕ) (p : ℝ) :
    ((n : ℝ) + 1) * p * (binomialMass n p k / ((k : ℝ) + 1)) =
      binomialMass (n + 1) p (k + 1) := by
  have hc : ((n : ℝ) + 1) * (n.choose k : ℝ) =
      ((n + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  unfold binomialMass
  rw [Nat.add_sub_add_right, pow_succ]
  field_simp
  nlinarith [congrArg (fun x : ℝ => x * p ^ k * (1 - p) ^ (n - k) * p) hc]

theorem binomialMass_harmonic_identity (n : ℕ) (p : ℝ) :
    ((n : ℝ) + 1) * p *
      (∑ k ∈ Finset.range (n + 1), binomialMass n p k / ((k : ℝ) + 1)) =
    1 - (1 - p) ^ (n + 1) := by
  rw [Finset.mul_sum]
  simp_rw [binomialMass_harmonic_step]
  have h := sum_binomialMass (n + 1) p
  rw [Finset.sum_range_succ'] at h
  simp only [binomialMass, Nat.choose_zero_right, Nat.cast_one, pow_zero,
    mul_one, one_mul, Nat.sub_zero] at h ⊢
  linarith

theorem binomialMass_harmonic_le (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioc 0 1) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n p k / ((k : ℝ) + 1)) ≤
      1 / (((n : ℝ) + 1) * p) := by
  apply (le_div_iff₀ (mul_pos (by positivity) hp.1)).mpr
  rw [mul_comm, binomialMass_harmonic_identity]
  have h := pow_nonneg (sub_nonneg.mpr hp.2) (n + 1)
  linarith

/-- The weighted Cauchy--Schwarz step for mixing the fair estimates. -/
theorem weighted_sum_sq_le {ι : Type*} (S : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    (∑ i ∈ S, w i * f i) ^ 2 ≤ (∑ i ∈ S, w i) * ∑ i ∈ S, w i * f i ^ 2 := by
  have heq (i : ι) : w i * f i = Real.sqrt (w i) * (Real.sqrt (w i) * f i) := by
    rw [← mul_assoc, ← sq, Real.sq_sqrt (hw i)]
  simp_rw [heq]
  apply (Finset.sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * f i)).trans_eq
  simp only [mul_pow, Real.sq_sqrt (hw _)]

theorem mixed_binomialBound_le (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioc 0 1) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n p k * binomialBound k) ≤
      Real.sqrt (2 / (((n : ℝ) + 1) * p)) := by
  have hw (k : ℕ) := binomialMass_nonneg n k (show p ∈ Set.Icc 0 1 from ⟨hp.1.le, hp.2⟩)
  have hs := weighted_sum_sq_le (Finset.range (n + 1)) (binomialMass n p)
    binomialBound hw
  rw [sum_binomialMass, one_mul] at hs
  have hb (k : ℕ) : binomialBound k ^ 2 = 2 / ((k : ℝ) + 1) :=
    Real.sq_sqrt (by positivity)
  simp_rw [hb] at hs
  have heq : (∑ k ∈ Finset.range (n + 1), binomialMass n p k * (2 / ((k : ℝ) + 1))) =
      2 * ∑ k ∈ Finset.range (n + 1), binomialMass n p k / ((k : ℝ) + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq] at hs
  have hh := binomialMass_harmonic_le n hp
  have hp0 := hp.1
  have hbound : (∑ k ∈ Finset.range (n + 1), binomialMass n p k * binomialBound k) ^ 2 ≤
      2 / (((n : ℝ) + 1) * p) := by
    calc
      _ ≤ 2 * ∑ k ∈ Finset.range (n + 1), binomialMass n p k / ((k : ℝ) + 1) := hs
      _ ≤ 2 * (1 / (((n : ℝ) + 1) * p)) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  have hsr := Real.sq_sqrt (show (0 : ℝ) ≤ 2 / (((n : ℝ) + 1) * p) by positivity)
  have hpos := Real.sqrt_nonneg (2 / (((n : ℝ) + 1) * p))
  nlinarith only [hbound, hsr, hpos]


def mixedFairSeries (n : ℕ) (p : ℝ) : IntSeries :=
  (p • fairSeries 1 + (1 - p) • (1 : IntSeries)) ^ n

def biasedSeries (n : ℕ) (p : ℝ) : IntSeries :=
  (AddMonoidAlgebra.single 1 p + AddMonoidAlgebra.single 0 (1 - p)) ^ n

theorem mixedFairSeries_expansion (n : ℕ) (p : ℝ) :
    mixedFairSeries n p =
      ∑ k ∈ Finset.range (n + 1), binomialMass n p k • fairSeries k := by
  rw [mixedFairSeries, add_pow]
  apply Finset.sum_congr rfl
  intro k _
  simp only [smul_pow, one_pow, smul_mul_smul, mul_one, fairSeries, pow_one]
  rw [mul_comm, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  unfold binomialMass
  ring

theorem mixedFairSeries_eq_biased (n : ℕ) (p : ℝ) :
    mixedFairSeries n p = biasedSeries n (p / 2) := by
  unfold mixedFairSeries biasedSeries
  congr 1
  ext z
  simp only [fairSeries, pow_one, smul_add, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    smul_eq_mul, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> first | omega | ring

theorem mixedFairSeries_coeff_bound (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioc 0 1) (z : ℤ) :
    |(mixedFairSeries n p).coeff z| ≤ Real.sqrt (2 / (((n : ℝ) + 1) * p)) := by
  rw [mixedFairSeries_expansion, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), |binomialMass n p k * (fairSeries k).coeff z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), binomialMass n p k * binomialBound k := by
      apply Finset.sum_le_sum
      intro k _
      have hw := binomialMass_nonneg n k (show p ∈ Set.Icc 0 1 from ⟨hp.1.le, hp.2⟩)
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (fairSeries_coeff_bound k z) hw
    _ ≤ _ := mixed_binomialBound_le n hp

/-- At success probabilities at most 1/2, this gives the sharp variance
    scale up to an absolute constant, using only the fair-coin estimate. -/
theorem biasedSeries_coeff_bound_low (n : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioc 0 (1 / 2)) (z : ℤ) :
    |(biasedSeries n p).coeff z| ≤ Real.sqrt (1 / (((n : ℝ) + 1) * p)) := by
  have h2p : 2 * p ∈ Set.Ioc 0 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have h := mixedFairSeries_coeff_bound n h2p z
  rw [mixedFairSeries_eq_biased, show 2 * p / 2 = p by ring] at h
  have heq : 2 / (((n : ℝ) + 1) * (2 * p)) = 1 / (((n : ℝ) + 1) * p) := by
    field_simp
  rwa [heq] at h


theorem biasedSeries_sum (n : ℕ) (p : ℝ) :
    biasedSeries n p = ∑ k ∈ Finset.range (n + 1),
      AddMonoidAlgebra.single (k : ℤ) (binomialMass n p k) := by
  rw [biasedSeries, add_pow]
  apply Finset.sum_congr rfl
  intro k _
  rw [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.single_mul_single]
  simp only [nsmul_eq_mul, mul_one, mul_zero, add_zero]
  congr 1
  unfold binomialMass
  ring

theorem biasedSeries_coeff_nat (n k : ℕ) (p : ℝ) :
    (biasedSeries n p).coeff (k : ℤ) = binomialMass n p k := by
  rw [biasedSeries_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  by_cases hk : k ≤ n
  · rw [Finset.sum_eq_single k]
    · simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_true]
    · intro b _ hb
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Nat.cast_inj, ite_eq_right hb]
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  · rw [Finset.sum_eq_zero]
    · simp [binomialMass, Nat.choose_eq_zero_of_lt (by omega : n < k)]
    · intro b hb
      have hbk : b ≠ k := by simp only [Finset.mem_range] at hb; omega
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Nat.cast_inj, ite_eq_right hbk]

theorem biasedSeries_coeff_neg (n : ℕ) (p : ℝ) (z : ℤ) (hz : z < 0) :
    (biasedSeries n p).coeff z = 0 := by
  rw [biasedSeries_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b _
  have h : (b : ℤ) ≠ z := by omega
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right h]

theorem biasedSeries_coeff_high (n : ℕ) (p : ℝ) (z : ℤ) (hz : (n : ℤ) < z) :
    (biasedSeries n p).coeff z = 0 := by
  rw [biasedSeries_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b hb
  have h : (b : ℤ) ≠ z := by simp only [Finset.mem_range] at hb; omega
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right h]

theorem binomialMass_symm (n k : ℕ) (p : ℝ) (hk : k ≤ n) :
    binomialMass n (1 - p) (n - k) = binomialMass n p k := by
  unfold binomialMass
  rw [Nat.choose_symm hk, Nat.sub_sub_self hk, show 1 - (1 - p) = p by ring]
  ring

theorem biasedSeries_coeff_reflect (n : ℕ) (p : ℝ) (z : ℤ) :
    (biasedSeries n (1 - p)).coeff ((n : ℤ) - z) = (biasedSeries n p).coeff z := by
  by_cases hz : z < 0
  · rw [biasedSeries_coeff_neg n p z hz,
      biasedSeries_coeff_high n (1 - p) _ (by omega)]
  by_cases hz' : (n : ℤ) < z
  · rw [biasedSeries_coeff_high n p z hz',
      biasedSeries_coeff_neg n (1 - p) _ (by omega)]
  have h0 : 0 ≤ z := by omega
  have hk : z.toNat ≤ n := by omega
  have hzN : (z.toNat : ℤ) = z := Int.toNat_of_nonneg h0
  have hsub : (n : ℤ) - z = ((n - z.toNat : ℕ) : ℤ) := by omega
  rw [hsub, ← hzN, biasedSeries_coeff_nat, biasedSeries_coeff_nat]
  exact binomialMass_symm n z.toNat p hk

/-- Uniform nonfair-binomial anti-concentration.  This is the absolute
    variance-scale upper bound used in the manuscript's rank kernels. -/
theorem biasedSeries_coeff_bound (n : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (z : ℤ) :
    |(biasedSeries n p).coeff z| ≤
      Real.sqrt (1 / (((n : ℝ) + 1) * p * (1 - p))) := by
  by_cases hlow : p ≤ 1 / 2
  · apply (biasedSeries_coeff_bound_low n ⟨hp.1, hlow⟩ z).trans
    apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le
    · exact mul_pos (mul_pos (by positivity) hp.1) (sub_pos.mpr hp.2)
    · have hn : (0 : ℝ) ≤ n + 1 := by positivity
      nlinarith [mul_nonneg hn (sq_nonneg p)]
  · have hq : 1 - p ∈ Set.Ioc 0 (1 / 2) := ⟨by linarith [hp.2], by linarith⟩
    rw [← biasedSeries_coeff_reflect n p z]
    apply (biasedSeries_coeff_bound_low n hq ((n : ℤ) - z)).trans
    apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le
    · exact mul_pos (mul_pos (by positivity) hp.1) (sub_pos.mpr hp.2)
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ n + 1 by positivity)
        (mul_nonneg (sub_nonneg.mpr hp.2.le) (sub_nonneg.mpr hp.2.le))]


theorem binomialMass_mul_index (n k : ℕ) (p : ℝ) :
    binomialMass (n + 1) p (k + 1) * ((k : ℝ) + 1) =
      ((n : ℝ) + 1) * p * binomialMass n p k := by
  have h := binomialMass_harmonic_step n k p
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [← h]
  field_simp

theorem binomialMass_index_sum (n : ℕ) (p : ℝ) (F : ℕ → ℝ) :
    (∑ k ∈ Finset.range (n + 2), binomialMass (n + 1) p k * (k : ℝ) * F k) =
      ((n : ℝ) + 1) * p *
        ∑ k ∈ Finset.range (n + 1), binomialMass n p k * F (k + 1) := by
  rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
  simp_rw [binomialMass_mul_index]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem binomialMass_mean (n : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (n + 1), binomialMass n p k * (k : ℝ) = (n : ℝ) * p := by
  cases n with
  | zero => simp
  | succ n =>
    simpa only [mul_one, sum_binomialMass, Nat.cast_add, Nat.cast_one] using
      binomialMass_index_sum n p (fun _ => 1)

theorem binomialMass_second_moment (n : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (n + 1), binomialMass n p k * (k : ℝ) ^ 2 =
      (n : ℝ) * ((n : ℝ) - 1) * p ^ 2 + (n : ℝ) * p := by
  cases n with
  | zero => simp
  | succ n =>
    have h := binomialMass_index_sum n p (fun k => k)
    simp only [Nat.cast_add, Nat.cast_one] at h ⊢
    simp_rw [mul_add, mul_one, Finset.sum_add_distrib, binomialMass_mean,
      sum_binomialMass] at h
    calc
      _ = ∑ k ∈ Finset.range (n + 2), binomialMass (n + 1) p k * (k : ℝ) * (k : ℝ) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [h]; ring

theorem binomialMass_variance (n : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n p k * ((k : ℝ) - (n : ℝ) * p) ^ 2) =
      (n : ℝ) * p * (1 - p) := by
  calc
    _ = (∑ k ∈ Finset.range (n + 1), binomialMass n p k * (k : ℝ) ^ 2) -
        2 * (n : ℝ) * p * (∑ k ∈ Finset.range (n + 1), binomialMass n p k * (k : ℝ)) +
        ((n : ℝ) * p) ^ 2 * (∑ k ∈ Finset.range (n + 1), binomialMass n p k) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [binomialMass_second_moment, binomialMass_mean, sum_binomialMass]; ring

theorem binomialMass_adjacent (n k : ℕ) (p : ℝ) (hk : k < n) :
    ((k : ℝ) + 1) * (1 - p) * binomialMass n p (k + 1) =
      ((n : ℝ) - k) * p * binomialMass n p k := by
  have hc : (n.choose (k + 1) : ℝ) * ((k : ℝ) + 1) =
      (n.choose k : ℝ) * ((n : ℝ) - (k : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk.le] using
      congrArg (fun t : ℕ => (t : ℝ)) (Nat.choose_succ_right_eq n k)
  have hnk : n - k = (n - (k + 1)) + 1 := by omega
  unfold binomialMass
  rw [hnk, pow_succ, pow_succ]
  linear_combination p ^ k * p * (1 - p) ^ (n - (k + 1)) * (1 - p) * hc

theorem binomialMass_le_mode (n l k : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (hl : l ≤ n) (hmean : (n : ℝ) * p = l) :
    binomialMass n p k ≤ binomialMass n p l := by
  have h0 (j : ℕ) := binomialMass_nonneg n j ⟨hp.1.le, hp.2.le⟩
  have hleft (j : ℕ) (hj : j < l) : binomialMass n p j ≤ binomialMass n p (j + 1) := by
    have hrec := binomialMass_adjacent n j p (by omega)
    have hjr : (j : ℝ) + 1 ≤ l := by exact_mod_cast hj
    have hcoef : (0 : ℝ) < ((j : ℝ) + 1) * (1 - p) := by
      exact mul_pos (by positivity) (sub_pos.mpr hp.2)
    have hdiff : ((j : ℝ) + 1) * (1 - p) ≤ ((n : ℝ) - j) * p := by
      nlinarith [hp.1]
    have := mul_le_mul_of_nonneg_right hdiff (h0 j)
    nlinarith only [hrec, this, hcoef]
  have hright (j : ℕ) (hj : l ≤ j) : binomialMass n p (j + 1) ≤ binomialMass n p j := by
    by_cases hjn : j < n
    · have hrec := binomialMass_adjacent n j p hjn
      have hjr : (l : ℝ) ≤ j := by exact_mod_cast hj
      have hcoef : (0 : ℝ) < ((j : ℝ) + 1) * (1 - p) := by
        exact mul_pos (by positivity) (sub_pos.mpr hp.2)
      have hdiff : ((n : ℝ) - j) * p ≤ ((j : ℝ) + 1) * (1 - p) := by
        nlinarith [hp.2]
      have := mul_le_mul_of_nonneg_right hdiff (h0 j)
      nlinarith only [hrec, this, hcoef]
    · have hjn' : n < j + 1 := by omega
      simp only [binomialMass, Nat.choose_eq_zero_of_lt hjn', Nat.cast_zero, zero_mul]
      exact h0 j
  rcases le_total k l with hk | hk
  · have haux : ∀ b : ℕ, k ≤ b → b ≤ l → binomialMass n p k ≤ binomialMass n p b := by
      intro b hkb
      induction b, hkb using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ b hb ih =>
        intro hbl
        exact (ih (by omega)).trans (hleft b (by omega))
    exact haux l hk le_rfl
  · induction k, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih => exact (hright j hj).trans ih


/-- A discrete law cannot have a very small maximum when its variance is bounded.
The explicit constant is deliberately loose, avoiding any use of Stirling. -/
theorem discrete_mode_lower (n l : ℕ) (f : ℕ → ℝ) (M v : ℝ)
    (hf : ∀ k, 0 ≤ f k) (hsum : ∑ k ∈ Finset.range (n + 1), f k = 1)
    (hmax : ∀ k, f k ≤ M)
    (hvar : ∑ k ∈ Finset.range (n + 1), f k * ((k : ℝ) - l) ^ 2 = v)
    (hv : 1 ≤ v) : 1 / (12 * Real.sqrt v) ≤ M := by
  classical
  let r : ℕ := ⌈2 * Real.sqrt v⌉₊
  have hv0 : 0 ≤ v := by linarith
  have hs : 1 ≤ Real.sqrt v := Real.one_le_sqrt.mpr hv
  have hs2 := Real.sq_sqrt hv0
  have hrlo : 2 * Real.sqrt v ≤ (r : ℝ) := Nat.le_ceil _
  have hrhi : (r : ℝ) < 2 * Real.sqrt v + 1 := Nat.ceil_lt_add_one (by positivity)
  have hrpos : (0 : ℝ) < r := by linarith
  have hM : 0 ≤ M := (hf 0).trans (hmax 0)
  let S := (Finset.range (n + 1)).filter (fun k => l - r ≤ k ∧ k ≤ l + r)
  have hcard : S.card ≤ 2 * r + 1 := by
    have hsub : S ⊆ Finset.Icc (l - r) (l + r) := by
      intro k hk
      exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hk).2
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    omega
  have hout (k : ℕ) (hk : ¬(l - r ≤ k ∧ k ≤ l + r)) :
      (r : ℝ) ^ 2 ≤ ((k : ℝ) - l) ^ 2 := by
    by_cases hleft : k < l - r
    · have hnat : k + r < l := by omega
      have hreal : (k : ℝ) + r < l := by exact_mod_cast hnat
      nlinarith [sq_nonneg ((l : ℝ) - k - r)]
    · have hnat : l + r < k := by omega
      have hreal : (l : ℝ) + r < k := by exact_mod_cast hnat
      nlinarith [sq_nonneg ((k : ℝ) - l - r)]
  have hpoint (k : ℕ) : (r : ℝ) ^ 2 * f k ≤
      (if l - r ≤ k ∧ k ≤ l + r then (r : ℝ) ^ 2 * M else 0) +
        f k * ((k : ℝ) - l) ^ 2 := by
    split_ifs with hk
    · have := mul_le_mul_of_nonneg_left (hmax k) (sq_nonneg (r : ℝ))
      have := mul_nonneg (hf k) (sq_nonneg ((k : ℝ) - l))
      linarith
    · simpa only [zero_add, mul_comm] using mul_le_mul_of_nonneg_left (hout k hk) (hf k)
  have htotal := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range (n + 1)) => hpoint k)
  rw [← Finset.mul_sum, hsum, mul_one, Finset.sum_add_distrib, hvar,
    ← Finset.sum_filter] at htotal
  change (r : ℝ) ^ 2 ≤ ∑ k ∈ S, (r : ℝ) ^ 2 * M + v at htotal
  rw [Finset.sum_const, nsmul_eq_mul] at htotal
  have hcardR : (S.card : ℝ) ≤ 2 * r + 1 := by exact_mod_cast hcard
  have hbound := mul_le_mul_of_nonneg_right hcardR (mul_nonneg (sq_nonneg (r : ℝ)) hM)
  have htotal' : (r : ℝ) ^ 2 ≤ (2 * r + 1) * ((r : ℝ) ^ 2 * M) + v := by
    linarith
  have hrv : 4 * v ≤ (r : ℝ) ^ 2 := by nlinarith [sq_nonneg ((r : ℝ) - 2 * Real.sqrt v)]
  have hcancel : (3 : ℝ) / 4 ≤ (2 * r + 1) * M := by
    have hrr : (0 : ℝ) < (r : ℝ) ^ 2 := sq_pos_of_pos hrpos
    nlinarith only [htotal', hrv, hrr]
  have hsize : 2 * (r : ℝ) + 1 ≤ 7 * Real.sqrt v := by linarith
  have hfinal := mul_le_mul_of_nonneg_right hsize hM
  apply (div_le_iff₀ (by positivity : 0 < 12 * Real.sqrt v)).mpr
  nlinarith only [hcancel, hfinal]

theorem binomialMass_mean_lower (n l : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (hl : l ≤ n) (hmean : (n : ℝ) * p = l) (hv : 1 ≤ (n : ℝ) * p * (1 - p)) :
    1 / (12 * Real.sqrt ((n : ℝ) * p * (1 - p))) ≤ binomialMass n p l := by
  apply discrete_mode_lower n l (binomialMass n p)
    (binomialMass n p l) ((n : ℝ) * p * (1 - p))
  · intro k; exact binomialMass_nonneg n k ⟨hp.1.le, hp.2.le⟩
  · exact sum_binomialMass n p
  · intro k; exact binomialMass_le_mode n l k hp hl hmean
  · rw [← hmean]; exact binomialMass_variance n p
  · exact hv


theorem binomialMass_mean_inverse_sq (n l : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (hl : l ≤ n) (hmean : (n : ℝ) * p = l) (hv : 1 ≤ (n : ℝ) * p * (1 - p)) :
    (binomialMass n p l)⁻¹ ^ 2 ≤ 144 * ((n : ℝ) * p * (1 - p)) := by
  have hs : 0 < Real.sqrt ((n : ℝ) * p * (1 - p)) :=
    Real.sqrt_pos.mpr (by linarith)
  have hlow := binomialMass_mean_lower n l hp hl hmean hv
  have hpos : 0 < binomialMass n p l := lt_of_lt_of_le (by positivity) hlow
  have hi : (binomialMass n p l)⁻¹ ≤ 12 * Real.sqrt ((n : ℝ) * p * (1 - p)) := by
    rw [← one_div]
    apply (div_le_iff₀ hpos).mpr
    have := (div_le_iff₀ (by positivity)).mp hlow
    nlinarith only [this]
  have his := sq_le_sq₀ (by positivity) (by positivity) |>.mpr hi
  have hs2 := Real.sq_sqrt (show 0 ≤ (n : ℝ) * p * (1 - p) by linarith)
  nlinarith only [his, hs2]

theorem seriesL1_smul (a : ℝ) (f : IntSeries) :
    seriesL1 (a • f) = |a| * seriesL1 f := by
  unfold seriesL1
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul]
  exact tsum_mul_left

theorem mixedFairSeries_difference_L1_bound (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioc 0 1) :
    seriesL1 (firstDifference * mixedFairSeries n p) ≤
      2 * Real.sqrt (2 / (((n : ℝ) + 1) * p)) := by
  rw [mixedFairSeries_expansion, Finset.mul_sum]
  simp_rw [mul_smul_comm]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        seriesL1 (binomialMass n p k • (firstDifference * fairSeries k)) := seriesL1_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), binomialMass n p k * (2 * binomialBound k) := by
      apply Finset.sum_le_sum
      intro k _
      have hw := binomialMass_nonneg n k ⟨hp.1.le, hp.2⟩
      rw [seriesL1_smul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (fairSeries_difference_L1_bound k) hw
    _ = 2 * ∑ k ∈ Finset.range (n + 1), binomialMass n p k * binomialBound k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mixed_binomialBound_le n hp) (by norm_num)

theorem biasedSeries_difference_L1_bound_low (n : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioc 0 (1 / 2)) :
    seriesL1 (firstDifference * biasedSeries n p) ≤
      2 * Real.sqrt (1 / (((n : ℝ) + 1) * p)) := by
  have h := mixedFairSeries_difference_L1_bound n
    (show 2 * p ∈ Set.Ioc 0 1 from ⟨by linarith [hp.1], by linarith [hp.2]⟩)
  rw [mixedFairSeries_eq_biased] at h
  have hp2 : 2 * p / 2 = p := by ring
  have heq : 2 / (((n : ℝ) + 1) * (2 * p)) = 1 / (((n : ℝ) + 1) * p) := by
    have hp0 : p ≠ 0 := ne_of_gt hp.1
    have hn0 : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rwa [hp2, heq] at h

theorem biasedSeries_difference_reflect (n : ℕ) (p : ℝ) (z : ℤ) :
    (firstDifference * biasedSeries n (1 - p)).coeff z =
      -(firstDifference * biasedSeries n p).coeff ((n : ℤ) + 1 - z) := by
  rw [firstDifference_coeff, firstDifference_coeff]
  have h1 := biasedSeries_coeff_reflect n p ((n : ℤ) - z)
  have h2 := biasedSeries_coeff_reflect n p ((n : ℤ) - (z - 1))
  have hz1 : (n : ℤ) - ((n : ℤ) - z) = z := by ring
  have hz2 : (n : ℤ) - ((n : ℤ) - (z - 1)) = z - 1 := by ring
  rw [hz1] at h1
  rw [hz2] at h2
  rw [h1, h2]
  have he1 : (n : ℤ) - (z - 1) = n + 1 - z := by ring
  have he2 : (n : ℤ) + 1 - z - 1 = n - z := by ring
  rw [he1, he2]
  ring

theorem biasedSeries_difference_L1_reflect (n : ℕ) (p : ℝ) :
    seriesL1 (firstDifference * biasedSeries n (1 - p)) =
      seriesL1 (firstDifference * biasedSeries n p) := by
  unfold seriesL1
  simp_rw [biasedSeries_difference_reflect, abs_neg]
  exact (Equiv.subLeft ((n : ℤ) + 1)).tsum_eq
    (fun z : ℤ => |(firstDifference * biasedSeries n p).coeff z|)

theorem biasedSeries_difference_L1_bound (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    seriesL1 (firstDifference * biasedSeries n p) ≤
      2 * Real.sqrt (1 / (((n : ℝ) + 1) * p * (1 - p))) := by
  by_cases hlow : p ≤ 1 / 2
  · apply (biasedSeries_difference_L1_bound_low n ⟨hp.1, hlow⟩).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le
    · exact mul_pos (mul_pos (by positivity) hp.1) (sub_pos.mpr hp.2)
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ n + 1 by positivity) (sq_nonneg p)]
  · have hq : 1 - p ∈ Set.Ioc 0 (1 / 2) := ⟨by linarith [hp.2], by linarith⟩
    rw [← biasedSeries_difference_L1_reflect n p]
    apply (biasedSeries_difference_L1_bound_low n hq).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le
    · exact mul_pos (mul_pos (by positivity) hp.1) (sub_pos.mpr hp.2)
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ n + 1 by positivity)
        (mul_nonneg (sub_nonneg.mpr hp.2.le) (sub_nonneg.mpr hp.2.le))]


def biasedBinomialBound (n : ℕ) (p : ℝ) : ℝ :=
  Real.sqrt (1 / (((n : ℝ) + 1) * p * (1 - p)))

theorem biasedSeries_L1 (n : ℕ) {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    seriesL1 (biasedSeries n p) = 1 := by
  rw [seriesL1_eq_sum_range _ n (biasedSeries_coeff_neg n p)]
  · simp_rw [biasedSeries_coeff_nat, abs_of_nonneg (binomialMass_nonneg _ _ hp)]
    exact sum_binomialMass n p
  · intro k hk
    exact biasedSeries_coeff_high n p k (by exact_mod_cast hk)

theorem biasedSeries_L2Sq_bound (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    seriesL2Sq (biasedSeries n p) ≤ biasedBinomialBound n p := by
  have := seriesL2Sq_le_L1_mul_bound (biasedSeries n p) _ (biasedSeries_coeff_bound n hp)
  simpa only [biasedSeries_L1 n ⟨hp.1.le, hp.2.le⟩, one_mul, biasedBinomialBound] using this

theorem biasedSeries_add (m n : ℕ) (p : ℝ) :
    biasedSeries (m + n) p = biasedSeries m p * biasedSeries n p := by
  exact pow_add _ _ _

theorem biasedSeries_mul_power (n s : ℕ) (p : ℝ) :
    firstDifference ^ s * biasedSeries ((s + 1) * n) p =
      (firstDifference * biasedSeries n p) ^ s * biasedSeries n p := by
  simp only [biasedSeries, add_mul, one_mul, pow_add, pow_mul, mul_pow]
  ring

theorem biased_difference_coeff_bound (n s : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (z : ℤ) :
    |(firstDifference ^ s * biasedSeries ((s + 1) * n) p).coeff z| ≤
      (2 * biasedBinomialBound n p) ^ s * biasedBinomialBound n p := by
  rw [biasedSeries_mul_power]
  apply (series_coeff_mul_bound _ _ _ (biasedSeries_coeff_bound n hp) z).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact (seriesL1_pow_le _ _).trans
    (pow_le_pow_left₀ (seriesL1_nonneg _) (biasedSeries_difference_L1_bound n hp) s)

theorem biased_difference_L2Sq_bound (n s : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    seriesL2Sq (firstDifference ^ s * biasedSeries ((s + 1) * n) p) ≤
      ((2 * biasedBinomialBound n p) ^ s) ^ 2 * biasedBinomialBound n p := by
  rw [biasedSeries_mul_power]
  apply (seriesL2Sq_mul_le _ _).trans
  apply mul_le_mul
  · apply pow_le_pow_left₀ (seriesL1_nonneg _)
    exact (seriesL1_pow_le _ _).trans
      (pow_le_pow_left₀ (seriesL1_nonneg _) (biasedSeries_difference_L1_bound n hp) s)
  · exact biasedSeries_L2Sq_bound n hp
  · exact seriesL2Sq_nonneg _
  · exact sq_nonneg _

theorem biased_difference_coeff_bound_remainder (n s r : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (z : ℤ) :
    |(firstDifference ^ s * biasedSeries ((s + 1) * n + r) p).coeff z| ≤
      (2 * biasedBinomialBound n p) ^ s * biasedBinomialBound n p := by
  rw [biasedSeries_add, ← mul_assoc, mul_comm (firstDifference ^ s * _)]
  simpa only [biasedSeries_L1 r ⟨hp.1.le, hp.2.le⟩, one_mul] using
    series_coeff_mul_bound (biasedSeries r p) (firstDifference ^ s * biasedSeries ((s + 1) * n) p)
      _ (biased_difference_coeff_bound n s hp) z

theorem biased_difference_L2Sq_bound_remainder (n s r : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioo 0 1) :
    seriesL2Sq (firstDifference ^ s * biasedSeries ((s + 1) * n + r) p) ≤
      ((2 * biasedBinomialBound n p) ^ s) ^ 2 * biasedBinomialBound n p := by
  rw [biasedSeries_add, ← mul_assoc, mul_comm (firstDifference ^ s * _)]
  calc
    _ ≤ seriesL1 (biasedSeries r p) ^ 2 *
        seriesL2Sq (firstDifference ^ s * biasedSeries ((s + 1) * n) p) := seriesL2Sq_mul_le _ _
    _ ≤ _ := by simpa only [biasedSeries_L1 r ⟨hp.1.le, hp.2.le⟩, one_pow, one_mul] using
        biased_difference_L2Sq_bound n s hp

/-- All fixed-order nonfair binomial differences, at the exact variance scale.
This is the analytic estimate needed for the initial conditional rank kernels. -/
theorem biased_difference_smoothing (g s : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    (∀ z : ℤ, |(firstDifference ^ s * biasedSeries g p).coeff z| ≤
      (2 * biasedBinomialBound (g / (s + 1)) p) ^ s *
        biasedBinomialBound (g / (s + 1)) p) ∧
    (seriesL2Sq (firstDifference ^ s * biasedSeries g p) ≤
      ((2 * biasedBinomialBound (g / (s + 1)) p) ^ s) ^ 2 *
        biasedBinomialBound (g / (s + 1)) p) := by
  have hg : (s + 1) * (g / (s + 1)) + g % (s + 1) = g := Nat.div_add_mod g (s + 1)
  constructor
  · intro z
    simpa only [hg] using biased_difference_coeff_bound_remainder (g / (s + 1)) s
      (g % (s + 1)) hp z
  · simpa only [hg] using biased_difference_L2Sq_bound_remainder (g / (s + 1)) s
      (g % (s + 1)) hp

theorem biasedBinomialBound_quotient_le (g s : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    biasedBinomialBound (g / (s + 1)) p ≤
      Real.sqrt (((s : ℝ) + 1) / (((g : ℝ) + 1) * p * (1 - p))) := by
  unfold biasedBinomialBound
  apply Real.sqrt_le_sqrt
  have hpq : 0 < p * (1 - p) := mul_pos hp.1 (sub_pos.mpr hp.2)
  have hnat : g + 1 ≤ (s + 1) * (g / (s + 1) + 1) := by
    have hdiv := Nat.div_add_mod g (s + 1)
    have hmod : g % (s + 1) < s + 1 := Nat.mod_lt g (by omega)
    calc
      g + 1 = (s + 1) * (g / (s + 1)) + g % (s + 1) + 1 := by omega
      _ ≤ (s + 1) * (g / (s + 1)) + (s + 1) := by omega
      _ = _ := by ring
  have hreal : (g : ℝ) + 1 ≤ ((s : ℝ) + 1) * ((g / (s + 1) : ℕ) + 1 : ℝ) := by
    exact_mod_cast hnat
  have hp0 := hp.1
  have hq0 := sub_pos.mpr hp.2
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hreal hpq.le]

/-! ## Gaussian overlap by exponential tilting of the exact binomial law -/

theorem binomialMass_tilt (n k : ℕ) {p a : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (ha : 0 < a) :
    binomialMass n p k * a ^ k =
      (1 - p + p * a) ^ n * binomialMass n (p * a / (1 - p + p * a)) k := by
  by_cases hk : k ≤ n
  · have hA : 0 < 1 - p + p * a := by positivity [sub_pos.mpr hp.2, hp.1]
    have hsub : 1 - p * a / (1 - p + p * a) = (1 - p) / (1 - p + p * a) := by
      field_simp; ring
    unfold binomialMass
    rw [hsub, div_pow, div_pow, mul_pow]
    have hpow : (1 - p + p * a) ^ n =
        (1 - p + p * a) ^ k * (1 - p + p * a) ^ (n - k) := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    rw [hpow]
    field_simp
  · simp [binomialMass, Nat.choose_eq_zero_of_lt (by omega : n < k)]

theorem binomialMass_tilt_product (g h k : ℕ) {p a : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (ha : 0 < a) :
    binomialMass g p k * binomialMass h p k =
      ((1 - p + p * a) ^ g * (1 - p + p / a) ^ h) *
        (binomialMass g (p * a / (1 - p + p * a)) k *
          binomialMass h ((p / a) / (1 - p + p / a)) k) := by
  have h1 := binomialMass_tilt g k hp ha
  have h2 := binomialMass_tilt h k hp (inv_pos.mpr ha)
  have hid := congrArg₂ (· * ·) h1 h2
  simp only [inv_pow, ← div_eq_mul_inv] at hid
  have ha0 : a ^ k ≠ 0 := pow_ne_zero _ ha.ne'
  calc
    _ = (binomialMass g p k * a ^ k) * (binomialMass h p k / a ^ k) := by field_simp
    _ = _ := by convert hid using 1; ring

/-- Tilting on opposite sides retains an anti-concentration factor as well
as the Gaussian penalty for different numbers of trials. -/
theorem binomial_overlap_tilt_bound (g h : ℕ) {p a : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (ha : 0 < a) :
    (∑ k ∈ Finset.range (h + 1), binomialMass g p k * binomialMass h p k) ≤
      ((1 - p + p * a) ^ g * (1 - p + p / a) ^ h) *
        biasedBinomialBound g (p * a / (1 - p + p * a)) := by
  have hA : 0 < 1 - p + p * a := by positivity [sub_pos.mpr hp.2, hp.1]
  have hB : 0 < 1 - p + p / a := by positivity [sub_pos.mpr hp.2, hp.1]
  have hpA : p * a / (1 - p + p * a) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · positivity [hp.1]
    · apply (div_lt_one hA).mpr; linarith [hp.2]
  have hpB : (p / a) / (1 - p + p / a) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · positivity [hp.1]
    · apply (div_lt_one hB).mpr; linarith [hp.2]
  simp_rw [binomialMass_tilt_product g h _ hp ha, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ k ∈ Finset.range (h + 1),
        biasedBinomialBound g (p * a / (1 - p + p * a)) *
          binomialMass h ((p / a) / (1 - p + p / a)) k := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_right _ (binomialMass_nonneg _ _ ⟨hpB.1.le, hpB.2.le⟩)
      have hb := biasedSeries_coeff_bound g hpA (k : ℤ)
      rw [biasedSeries_coeff_nat, abs_of_nonneg (binomialMass_nonneg _ _ ⟨hpA.1.le, hpA.2.le⟩)] at hb
      exact hb
    _ = _ := by rw [← Finset.mul_sum, sum_binomialMass, mul_one]


theorem binomial_tilt_variance {p t : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (ht : t ∈ Set.Icc 0 (1 / 4 : ℝ)) :
    p * (1 - p) / 2 ≤
      (p * (1 - t) / (1 - p + p * (1 - t))) *
        (1 - p * (1 - t) / (1 - p + p * (1 - t))) := by
  have hA : 0 < 1 - p + p * (1 - t) := by
    have := hp.1; have := hp.2; have := ht.2
    positivity [sub_pos.mpr hp.2, show (0 : ℝ) < 1 - t by linarith]
  have hA1 : 1 - p + p * (1 - t) ≤ 1 := by nlinarith [mul_nonneg hp.1.le ht.1]
  have hAsq : (1 - p + p * (1 - t)) ^ 2 ≤ 1 := by nlinarith
  have hpq : 0 < p * (1 - p) := mul_pos hp.1 (sub_pos.mpr hp.2)
  have heq : (p * (1 - t) / (1 - p + p * (1 - t))) *
        (1 - p * (1 - t) / (1 - p + p * (1 - t))) =
      p * (1 - p) * (1 - t) / (1 - p + p * (1 - t)) ^ 2 := by
    field_simp; ring
  rw [heq]
  apply (le_div_iff₀ (sq_pos_of_pos hA)).mpr
  have hh := mul_le_mul_of_nonneg_left hAsq hpq.le
  nlinarith [ht.2]

theorem binomial_tilt_normalizer (g h : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ico (1 / 2 : ℝ) 1) (hhg : h ≤ g) (hS : 0 < g + h) :
    let t : ℝ := ((g : ℝ) - h) / (4 * ((g : ℝ) + h))
    ((1 - p + p * (1 - t)) ^ g * (1 - p + p / (1 - t)) ^ h) ≤
      Real.exp (-((g : ℝ) - h) ^ 2 / (16 * ((g : ℝ) + h))) := by
  dsimp only
  set t : ℝ := ((g : ℝ) - h) / (4 * ((g : ℝ) + h)) with htdef
  have hSr : (0 : ℝ) < (g : ℝ) + h := by exact_mod_cast hS
  have hgr : (h : ℝ) ≤ g := by exact_mod_cast hhg
  have hd : (0 : ℝ) ≤ (g : ℝ) - h := sub_nonneg.mpr hgr
  have ht0 : 0 ≤ t := div_nonneg hd (by positivity)
  have ht1 : t ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ((g : ℝ) + h))).mpr
    nlinarith [show (0 : ℝ) ≤ h by positivity]
  have htlt : 0 < 1 - t := by linarith
  have hp0 : 0 < p := by linarith [hp.1]
  have hA : 0 < 1 - p + p * (1 - t) := by positivity [sub_pos.mpr hp.2]
  have hB : 0 < 1 - p + p / (1 - t) := by positivity [sub_pos.mpr hp.2]
  have hlogA : Real.log (1 - p + p * (1 - t)) ≤ -p * t := by
    have := Real.log_le_sub_one_of_pos hA
    nlinarith only [this]
  have hlogB : Real.log (1 - p + p / (1 - t)) ≤ p * t / (1 - t) := by
    have := Real.log_le_sub_one_of_pos hB
    have heq : 1 - p + p / (1 - t) - 1 = p * t / (1 - t) := by field_simp; ring
    rwa [heq] at this
  have hlog : Real.log ((1 - p + p * (1 - t)) ^ g * (1 - p + p / (1 - t)) ^ h) ≤
      -(p * ((g : ℝ) - h) * t) + 2 * p * h * t ^ 2 := by
    rw [Real.log_mul (pow_pos hA _).ne' (pow_pos hB _).ne', Real.log_pow, Real.log_pow]
    have hb : (h : ℝ) * (p * t / (1 - t)) ≤ (h : ℝ) * (p * t + 2 * p * t ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (div_le_iff₀ htlt).mpr
      have hh := mul_nonneg (mul_nonneg hp0.le (sq_nonneg t)) (show 0 ≤ 1 - 2 * t by linarith)
      nlinarith only [hh]
    have ha := mul_le_mul_of_nonneg_left hlogA (show (0 : ℝ) ≤ g by positivity)
    have hb' := mul_le_mul_of_nonneg_left hlogB (show (0 : ℝ) ≤ h by positivity)
    linarith
  have hht : 4 * (h : ℝ) * t ≤ (g : ℝ) - h := by
    rw [htdef, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ((g : ℝ) + h))).mpr
    have hm := mul_nonneg (show (0 : ℝ) ≤ g by positivity) hd
    nlinarith only [hm]
  have hhalf : -(p * ((g : ℝ) - h) * t) + 2 * p * h * t ^ 2 ≤
      -(p * ((g : ℝ) - h) * t) / 2 := by
    have hm := mul_le_mul_of_nonneg_right hht (mul_nonneg hp0.le ht0)
    nlinarith only [hm]
  have hlast : -(p * ((g : ℝ) - h) * t) / 2 ≤
      -((g : ℝ) - h) ^ 2 / (16 * ((g : ℝ) + h)) := by
    rw [htdef]
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity)).mpr
    field_simp
    have hm := mul_nonneg (show 0 ≤ 2 * p - 1 by linarith [hp.1]) (sq_nonneg ((g : ℝ) - h))
    nlinarith only [hm]
  have hexp := Real.exp_le_exp.mpr (hlog.trans (hhalf.trans hlast))
  rwa [Real.exp_log (mul_pos (pow_pos hA _) (pow_pos hB _))] at hexp


/-- The Gaussian cross-overlap estimate used by the conditional rank-kernel
square-sum argument. The constant is absolute, also as p tends to one. -/
theorem binomial_gaussian_overlap (g h : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ico (1 / 2 : ℝ) 1) (hhg : h ≤ g) (hS : 0 < g + h) :
    (∑ k ∈ Finset.range (h + 1), binomialMass g p k * binomialMass h p k) ≤
      Real.sqrt (2 / (((g : ℝ) + 1) * p * (1 - p))) *
        Real.exp (-((g : ℝ) - h) ^ 2 / (16 * ((g : ℝ) + h))) := by
  let t : ℝ := ((g : ℝ) - h) / (4 * ((g : ℝ) + h))
  have hSr : (0 : ℝ) < (g : ℝ) + h := by exact_mod_cast hS
  have hgr : (h : ℝ) ≤ g := by exact_mod_cast hhg
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hgr) (by positivity)
  have ht1 : t ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ((g : ℝ) + h))).mpr
    nlinarith [show (0 : ℝ) ≤ h by positivity]
  have htlt : 0 < 1 - t := by linarith
  have hp0 : 0 < p := by linarith [hp.1]
  have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨hp0, hp.2⟩
  have hA : 0 < 1 - p + p * (1 - t) := by positivity [sub_pos.mpr hp.2]
  have hB : 0 < 1 - p + p / (1 - t) := by positivity [sub_pos.mpr hp.2]
  have hv := binomial_tilt_variance hp' ⟨ht0, ht1⟩
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp.2)
  have hx : 0 < (p * (1 - t) / (1 - p + p * (1 - t))) *
      (1 - p * (1 - t) / (1 - p + p * (1 - t))) := lt_of_lt_of_le (by positivity) hv
  have hb : biasedBinomialBound g (p * (1 - t) / (1 - p + p * (1 - t))) ≤
      Real.sqrt (2 / (((g : ℝ) + 1) * p * (1 - p))) := by
    apply Real.sqrt_le_sqrt
    have hg : (0 : ℝ) < (g : ℝ) + 1 := by positivity
    apply (div_le_div_iff₀ (by nlinarith only [mul_pos hg hx]) (by nlinarith only [mul_pos hg hpq])).mpr
    have hm := mul_le_mul_of_nonneg_left hv hg.le
    nlinarith only [hm]
  have hn := binomial_tilt_normalizer g h hp hhg hS
  change ((1 - p + p * (1 - t)) ^ g * (1 - p + p / (1 - t)) ^ h) ≤ _ at hn
  have he := binomial_overlap_tilt_bound g h hp' htlt
  apply he.trans
  have hbound := mul_le_mul hn hb (Real.sqrt_nonneg _) (Real.exp_nonneg _)
  simpa only [mul_comm] using hbound


theorem sqrt_times_gaussian_le {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x + 1) * Real.exp (-x / 96) ≤ 16 := by
  have he : Real.exp (-x / 96) ^ 2 = 1 / Real.exp (x / 48) := by
    rw [pow_two, ← Real.exp_add]
    rw [show -x / 96 + -x / 96 = -(x / 48) by ring, Real.exp_neg, one_div]
  have hs : (Real.sqrt (x + 1) * Real.exp (-x / 96)) ^ 2 ≤ 256 := by
    rw [mul_pow, Real.sq_sqrt (by linarith), he, mul_one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have hh := Real.add_one_le_exp (x / 48)
    nlinarith only [hh, hx]
  nlinarith only [hs]

theorem sqrt_recip_product_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ 2 * b) :
    Real.sqrt (1 / a) * Real.sqrt (1 / b) ≤ 2 / a := by
  rw [← Real.sqrt_mul (by positivity), Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  field_simp
  nlinarith

theorem binomialMass_le_bound (n k : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    binomialMass n p k ≤ biasedBinomialBound n p := by
  have h := biasedSeries_coeff_bound n hp (k : ℤ)
  rw [biasedSeries_coeff_nat, abs_of_nonneg (binomialMass_nonneg _ _ ⟨hp.1.le, hp.2.le⟩)] at h
  exact h

/-- A uniform product-supremum estimate, including very unequal trial
counts. This justifies eliminating a largest gap in the rank kernel. -/
theorem binomial_product_sup (g h k : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ico (1 / 2 : ℝ) 1) :
    binomialMass g p k * binomialMass h p k ≤
      32 / (((g : ℝ) + 1) * p * (1 - p)) := by
  have hp0 : 0 < p := by linarith [hp.1]
  have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨hp0, hp.2⟩
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp.2)
  have hpq1 : p * (1 - p) ≤ 1 := by nlinarith only [sq_nonneg (p - 1 / 2)]
  have hden : 0 < ((g : ℝ) + 1) * p * (1 - p) := by nlinarith only [mul_pos (show (0 : ℝ) < (g : ℝ) + 1 by positivity) hpq]
  by_cases hnear : g ≤ 2 * h
  · have hdenh : 0 < ((h : ℝ) + 1) * p * (1 - p) := by nlinarith only [mul_pos (show (0 : ℝ) < (h : ℝ) + 1 by positivity) hpq]
    have hgh : ((g : ℝ) + 1) * p * (1 - p) ≤ 2 * (((h : ℝ) + 1) * p * (1 - p)) := by
      have hcast : (g : ℝ) ≤ 2 * h := by exact_mod_cast hnear
      have hm := mul_le_mul_of_nonneg_right (show (g : ℝ) + 1 ≤ 2 * ((h : ℝ) + 1) by linarith) hpq.le
      nlinarith only [hm]
    calc
      _ ≤ biasedBinomialBound g p * biasedBinomialBound h p :=
        mul_le_mul (binomialMass_le_bound g k hp') (binomialMass_le_bound h k hp')
          (binomialMass_nonneg _ _ ⟨hp0.le, hp.2.le⟩) (Real.sqrt_nonneg _)
      _ ≤ 2 / (((g : ℝ) + 1) * p * (1 - p)) := sqrt_recip_product_le hden hdenh hgh
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) hden.le
  · by_cases hk : k ≤ h
    · have hhg : h ≤ g := by omega
      have hS : 0 < g + h := by omega
      have hsum : binomialMass g p k * binomialMass h p k ≤
          ∑ j ∈ Finset.range (h + 1), binomialMass g p j * binomialMass h p j := by
        exact Finset.single_le_sum (s := Finset.range (h + 1)) (a := k) (fun j _ => mul_nonneg
          (binomialMass_nonneg g j ⟨hp0.le, hp.2.le⟩)
          (binomialMass_nonneg h j ⟨hp0.le, hp.2.le⟩)) (Finset.mem_range.mpr (by omega))
      have hgauss := binomial_gaussian_overlap g h hp hhg hS
      have hSr : (0 : ℝ) < (g : ℝ) + h := by exact_mod_cast hS
      have hfar : 2 * (h : ℝ) < g := by exact_mod_cast (show 2 * h < g by omega)
      have hexp : Real.exp (-((g : ℝ) - h) ^ 2 / (16 * ((g : ℝ) + h))) ≤ Real.exp (-(g : ℝ) / 96) := by
        apply Real.exp_le_exp.mpr
        apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * ((g : ℝ) + h)) (by norm_num : (0 : ℝ) < 96)).mpr
        have hn := mul_nonneg (show 0 ≤ (g : ℝ) - 2 * h by linarith) (show 0 ≤ 5 * (g : ℝ) - 3 * h by linarith)
        nlinarith only [hn, sq_nonneg (h : ℝ)]
      have hcoeff : Real.sqrt (2 / (((g : ℝ) + 1) * p * (1 - p))) ≤
          (2 / (((g : ℝ) + 1) * p * (1 - p))) * Real.sqrt ((g : ℝ) + 1) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        rw [mul_pow, Real.sq_sqrt (by positivity), div_pow]
        have hgpos : (0 : ℝ) < (g : ℝ) + 1 := by positivity
        have hqpos : 0 < 1 - p := sub_pos.mpr hp.2
        field_simp
        have hm := mul_le_mul_of_nonneg_left hpq1 (show (0 : ℝ) ≤ (g : ℝ) + 1 by positivity)
        nlinarith only [hm, hpq1]
      calc
        _ ≤ Real.sqrt (2 / (((g : ℝ) + 1) * p * (1 - p))) *
            Real.exp (-((g : ℝ) - h) ^ 2 / (16 * ((g : ℝ) + h))) := hsum.trans hgauss
        _ ≤ ((2 / (((g : ℝ) + 1) * p * (1 - p))) * Real.sqrt ((g : ℝ) + 1)) *
            Real.exp (-(g : ℝ) / 96) := mul_le_mul hcoeff hexp (Real.exp_nonneg _) (by positivity)
        _ ≤ (2 / (((g : ℝ) + 1) * p * (1 - p))) * 16 := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (sqrt_times_gaussian_le (by positivity)) (by positivity)
        _ = _ := by ring
    · simp [binomialMass, Nat.choose_eq_zero_of_lt (by omega : h < k)]
      positivity

end TraceReconstruction

namespace TraceReconstruction

/-- Exact moment generating function, including both endpoint channels. -/
theorem binomialMass_mgf (n : ℕ) (p t : ℝ) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n p k * Real.exp (t * k)) =
      (1 - p + p * Real.exp t) ^ n := by
  rw [add_comm (1 - p), add_pow]
  apply Finset.sum_congr rfl
  intro k _
  rw [show t * (k : ℝ) = (k : ℝ) * t by ring, Real.exp_nat_mul, mul_pow]
  unfold binomialMass
  ring

theorem binomialMass_mgf_le (n : ℕ) {p : ℝ} (hp : p ∈ Set.Icc 0 1) (t : ℝ) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n p k * Real.exp (t * k)) ≤
      Real.exp ((n : ℝ) * p * (Real.exp t - 1)) := by
  rw [binomialMass_mgf]
  have hn : 0 ≤ 1 - p + p * Real.exp t := by positivity [sub_nonneg.mpr hp.2, hp.1]
  have he : 1 - p + p * Real.exp t ≤ Real.exp (p * (Real.exp t - 1)) := by
    nlinarith only [Real.add_one_le_exp (p * (Real.exp t - 1))]
  calc
    _ ≤ Real.exp (p * (Real.exp t - 1)) ^ n := pow_le_pow_left₀ hn he n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- Exponential Markov bound for a finite nonnegative measure. -/
theorem finite_exp_markov {α : Type*} (S : Finset α) (w X : α → ℝ)
    (hw : ∀ a ∈ S, 0 ≤ w a) (a t : ℝ) (ht : 0 ≤ t) :
    (∑ z ∈ S with a ≤ X z, w z) ≤
      Real.exp (-t * a) * ∑ z ∈ S, w z * Real.exp (t * X z) := by
  classical
  calc
    _ = ∑ z ∈ S with a ≤ X z, Real.exp (-t * a) * (w z * Real.exp (t * a)) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [mul_left_comm, ← Real.exp_add]
      simp
    _ ≤ ∑ z ∈ S with a ≤ X z, Real.exp (-t * a) * (w z * Real.exp (t * X z)) := by
      apply Finset.sum_le_sum
      intro z hz
      have h := Finset.mem_filter.mp hz
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h.2 ht)) (hw z h.1))
        (Real.exp_nonneg _)
    _ ≤ ∑ z ∈ S, Real.exp (-t * a) * (w z * Real.exp (t * X z)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro z hz _
      positivity [hw z hz]
    _ = _ := by rw [Finset.mul_sum]

/-- A uniform multiplicative lower tail, sufficient for hidden-flag counts. -/
theorem binomialMass_lower_half (n : ℕ) {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    (∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n * p / 2),
      binomialMass n p k) ≤ Real.exp (-(n : ℝ) * p / 12) := by
  have he : Real.exp (-(1 / 2 : ℝ)) ≤ 2 / 3 := by
    rw [Real.exp_neg]
    apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).mpr
    nlinarith only [Real.add_one_le_exp (1 / 2 : ℝ)]
  have hmark := finite_exp_markov (Finset.range (n + 1)) (binomialMass n p)
    (fun k => -(k : ℝ)) (fun k _ => binomialMass_nonneg n k hp)
    (-(n : ℝ) * p / 2) (1 / 2) (by norm_num)
  have hf : (Finset.range (n + 1)).filter (fun k : ℕ => -(n : ℝ) * p / 2 ≤ -(k : ℝ)) =
      (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n * p / 2) := by
    ext k
    simp only [Finset.mem_filter]
    constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨h, by linarith⟩
  rw [hf] at hmark
  calc
    _ ≤ Real.exp (-(1 / 2 : ℝ) * (-(n : ℝ) * p / 2)) *
        (∑ k ∈ Finset.range (n + 1), binomialMass n p k * Real.exp (-(1 / 2 : ℝ) * k)) := by
      convert hmark using 1
      congr 2
      funext k
      congr 2
      ring
    _ ≤ Real.exp (-(1 / 2 : ℝ) * (-(n : ℝ) * p / 2)) *
        Real.exp ((n : ℝ) * p * (Real.exp (-(1 / 2 : ℝ)) - 1)) := by
      gcongr
      exact binomialMass_mgf_le n hp _
    _ = Real.exp ((n : ℝ) * p * (Real.exp (-(1 / 2 : ℝ)) - 3 / 4)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left he (mul_nonneg (Nat.cast_nonneg n) hp.1)]

end TraceReconstruction

namespace TraceReconstruction
theorem fairBinomial_centered_mgf (n : ℕ) (t : ℝ) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n (1 / 2) k *
      Real.exp (t * ((k : ℝ) - n / 2))) ≤ Real.exp ((n : ℝ) * t ^ 2 / 8) := by
  have he : (1 / 2 : ℝ) + Real.exp t / 2 = Real.exp (t / 2) * Real.cosh (t / 2) := by
    rw [Real.cosh_eq, ← mul_div_assoc, mul_add, ← Real.exp_add, ← Real.exp_add]
    rw [show t / 2 + t / 2 = t by ring, show t / 2 + -(t / 2) = 0 by ring, Real.exp_zero]
    ring
  have hm : (∑ k ∈ Finset.range (n + 1), binomialMass n (1 / 2) k *
      Real.exp (t * ((k : ℝ) - n / 2))) =
      Real.exp (-t * n / 2) * (1 - 1 / 2 + (1 / 2) * Real.exp t) ^ n := by
    rw [← binomialMass_mgf, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  rw [hm, show (1 - 1 / 2 + (1 / 2) * Real.exp t : ℝ) = 1 / 2 + Real.exp t / 2 by ring, he, mul_pow]
  have hb : Real.cosh (t / 2) ^ n ≤ Real.exp (t ^ 2 / 8) ^ n := by
    apply pow_le_pow_left₀ (le_of_lt (Real.cosh_pos _))
    convert Real.cosh_le_exp_half_sq (t / 2) using 1; congr 1; ring
  calc
    _ ≤ Real.exp (-t * n / 2) * (Real.exp (t / 2) ^ n * Real.exp (t ^ 2 / 8) ^ n) := by gcongr
    _ = _ := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem fairBinomial_upper_tail (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 ≤ a) :
    (∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => a ≤ (k : ℝ) - n / 2),
      binomialMass n (1 / 2) k) ≤ Real.exp (-2 * a ^ 2 / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := finite_exp_markov (Finset.range (n + 1)) (binomialMass n (1 / 2))
    (fun k => (k : ℝ) - n / 2) (fun k _ => binomialMass_nonneg n k (by norm_num))
    a (4 * a / n) (by positivity)
  calc
    _ ≤ Real.exp (-(4 * a / n) * a) *
      (∑ k ∈ Finset.range (n + 1), binomialMass n (1 / 2) k *
        Real.exp ((4 * a / n) * ((k : ℝ) - n / 2))) := h
    _ ≤ Real.exp (-(4 * a / n) * a) * Real.exp ((n : ℝ) * (4 * a / n) ^ 2 / 8) := by
      gcongr
      exact fairBinomial_centered_mgf n _
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      field_simp [ne_of_gt hnR]
      ring
end TraceReconstruction

namespace TraceReconstruction
def hypergeomMass (V M m v : ℕ) : ℝ :=
  if v ≤ m then (V.choose v : ℝ) * (M.choose (m-v) : ℝ) / ((V+M).choose m : ℝ) else 0

theorem hypergeomMass_nonneg (V M m v : ℕ) : 0 ≤ hypergeomMass V M m v := by
  unfold hypergeomMass
  split <;> positivity

theorem hypergeomMass_eq_binomial (V M m v : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (hm : m ≤ V+M) (hv : v ≤ m) :
    hypergeomMass V M m v = binomialMass V p v * binomialMass M p (m-v) /
      binomialMass (V+M) p m := by
  unfold hypergeomMass
  rw [ite_eq_left hv]
  by_cases hvV : v ≤ V
  · by_cases hkM : m-v ≤ M
    · unfold binomialMass
      have hc : (0 : ℝ) < (V+M).choose m := by exact_mod_cast Nat.choose_pos hm
      have hp1 := hp.1
      have hq1 := sub_pos.mpr hp.2
      have he : V-v+(M-(m-v)) = V+M-m := by omega
      have he' : v+(m-v) = m := by omega
      apply (div_eq_div_iff (ne_of_gt hc) (by positivity)).mpr
      calc
        _ = ((V.choose v : ℝ) * (M.choose (m-v) : ℝ) * ((V+M).choose m : ℝ)) *
            (p^m * (1-p)^(V+M-m)) := by ring
        _ = _ := by
          rw [show p^m = p^v * p^(m-v) by rw [← pow_add, he'],
            show (1-p)^(V+M-m) = (1-p)^(V-v)*(1-p)^(M-(m-v)) by rw [← pow_add, he]]
          ring
    · rw [Nat.choose_eq_zero_of_lt (by omega : M < m-v)]
      simp [binomialMass, Nat.choose_eq_zero_of_lt (by omega : M < m-v)]
  · rw [Nat.choose_eq_zero_of_lt (by omega : V < v)]
    simp [binomialMass, Nat.choose_eq_zero_of_lt (by omega : V < v)]

theorem binomialMass_sq_upper (n k : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    binomialMass n p k ^ 2 ≤ 1 / (((n : ℝ)+1)*p*(1-p)) := by
  have hp1 := hp.1
  have hq1 := sub_pos.mpr hp.2
  have h := biasedSeries_coeff_bound n hp (k : ℤ)
  rw [biasedSeries_coeff_nat, abs_of_nonneg (binomialMass_nonneg n k ⟨hp.1.le,hp.2.le⟩)] at h
  have hs := sq_le_sq₀ (binomialMass_nonneg n k ⟨hp.1.le,hp.2.le⟩)
    (Real.sqrt_nonneg _) |>.mpr h
  rwa [Real.sq_sqrt (by positivity)] at hs

theorem hypergeomMass_sq_upper (V M m v : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (hm : m ≤ V+M) (hmean : (m : ℝ) = (V+M : ℕ)*p)
    (hvar : 1 ≤ (V+M : ℕ)*p*(1-p)) :
    hypergeomMass V M m v ^ 2 ≤
      144 * (V+M : ℕ) / (((V : ℝ)+1)*((M : ℝ)+1)*p*(1-p)) := by
  have hp1 := hp.1
  have hq1 := sub_pos.mpr hp.2
  by_cases hv : v ≤ m
  · rw [hypergeomMass_eq_binomial V M m v hp hm hv, div_eq_mul_inv, mul_pow, mul_pow]
    have hV := binomialMass_sq_upper V v hp
    have hM := binomialMass_sq_upper M (m-v) hp
    have hN := binomialMass_mean_inverse_sq (V+M) m hp hm hmean.symm hvar
    have hvm := mul_le_mul hV hM (sq_nonneg _) (by positivity)
    have h := mul_le_mul hvm hN (sq_nonneg _) (by positivity)
    apply h.trans
    have hp0 : p ≠ 0 := ne_of_gt hp.1
    have hq0 : 1-p ≠ 0 := ne_of_gt (sub_pos.mpr hp.2)
    have hV0 : (V : ℝ)+1 ≠ 0 := by positivity
    have hM0 : (M : ℝ)+1 ≠ 0 := by positivity
    apply le_of_eq
    field_simp
  · simp only [hypergeomMass, ite_eq_right hv, zero_pow (by decide : 2 ≠ 0)]
    positivity

theorem sum_hypergeomMass (V M m : ℕ) (hm : m ≤ V+M) :
    ∑ v ∈ Finset.range (m+1), hypergeomMass V M m v = 1 := by
  have hc : (0 : ℝ) < (V+M).choose m := by exact_mod_cast Nat.choose_pos hm
  have hv := Nat.add_choose_eq V M m
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  simp only [hypergeomMass]
  have he : (∑ v ∈ Finset.range (m+1),
      if v ≤ m then (V.choose v : ℝ)*(M.choose (m-v) : ℝ)/((V+M).choose m : ℝ) else 0) =
    (∑ v ∈ Finset.range (m+1), (V.choose v : ℝ)*(M.choose (m-v) : ℝ))/((V+M).choose m : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro v hv'
    rw [ite_eq_left (by simp only [Finset.mem_range] at hv'; omega)]
  rw [he]
  have he' : (∑ v ∈ Finset.range (m+1), (V.choose v : ℝ)*(M.choose (m-v) : ℝ)) =
      ((V+M).choose m : ℝ) := by exact_mod_cast hv.symm
  rw [he', div_self (ne_of_gt hc)]

theorem hypergeomMass_high (V M m v : ℕ) (hv : V < v) : hypergeomMass V M m v = 0 := by
  unfold hypergeomMass
  rw [Nat.choose_eq_zero_of_lt hv]
  simp

/-- Adjacent-mass identity for the hidden count. The central regime has full support
on 0,...,M; this is exactly the regime used in adjacent-power lifting. -/
theorem hypergeom_hidden_adjacent (V M m k : ℕ) (hM : M ≤ m) (hV : m ≤ V) (hk : k < M) :
    (((k:ℝ)+1)*((V:ℝ)-m+k+1)) * hypergeomMass M V m (k+1) =
    (((M:ℝ)-k)*((m:ℝ)-k)) * hypergeomMass M V m k := by
  have hkM : k ≤ M := by omega
  have hkm : k ≤ m := by omega
  have hkm' : k+1 ≤ m := by omega
  have hv : m-(k+1) ≤ V := by omega
  have h1 := Nat.choose_succ_right_eq M k
  have h2 := Nat.choose_succ_right_eq V (m-(k+1))
  rw [show m-(k+1)+1=m-k by omega] at h2
  have h1' : (M.choose (k+1):ℝ)*((k:ℝ)+1) = (M.choose k:ℝ)*((M:ℝ)-k) := by
    exact_mod_cast h1
  have h2' : (V.choose (m-k):ℝ)*((m:ℝ)-k) =
      (V.choose (m-(k+1)):ℝ)*((V:ℝ)-m+k+1) := by
    have hvsub : V-(m-(k+1)) = V-m+k+1 := by omega
    rw [hvsub] at h2
    exact_mod_cast h2
  unfold hypergeomMass
  rw [ite_eq_left hkm', ite_eq_left hkm]
  have hmul := congrArg (fun z : ℝ => z*(V.choose (m-(k+1)) : ℝ)*((V:ℝ)-m+k+1)) h1'
  have hmul' := congrArg (fun z : ℝ => z*(M.choose k : ℝ)*((M:ℝ)-k)) h2'
  have he : (((k:ℝ)+1)*((V:ℝ)-m+k+1)) *
        ((M.choose (k+1):ℝ)*(V.choose (m-(k+1)):ℝ)) =
      (((M:ℝ)-k)*((m:ℝ)-k))*((M.choose k:ℝ)*(V.choose (m-k):ℝ)) := by
    nlinarith only [hmul, hmul']
  simpa only [mul_div_assoc] using congrArg (fun z : ℝ => z/((M+V).choose m:ℝ)) he

def hypergeomHiddenMode (V M m : ℕ) : ℕ := (M+1)*(m+1)/(V+M+2)

theorem hypergeomHiddenMode_le (V M m : ℕ) (hV : m ≤ V) :
    hypergeomHiddenMode V M m ≤ M := by
  unfold hypergeomHiddenMode
  have h1 : (M+1)*(m+1) < (M+1)*(V+M+2) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hh : (M+1)*(m+1)/(V+M+2) < M+1 := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    exact h1
  omega

theorem hypergeom_hidden_unimodal_left (V M m k : ℕ) (hM : M ≤ m) (hV : m ≤ V)
    (hk : k < hypergeomHiddenMode V M m) :
    hypergeomMass M V m k ≤ hypergeomMass M V m (k+1) := by
  have hl := hypergeomHiddenMode_le V M m hV
  have hkM : k < M := by omega
  have hrec := hypergeom_hidden_adjacent V M m k hM hV hkM
  have hc : (k+1)*(V+M+2) ≤ (M+1)*(m+1) := by
    have hh : k+1 ≤ (M+1)*(m+1)/(V+M+2) := hk
    exact (Nat.le_div_iff_mul_le (by omega)).mp hh
  have hc' : ((k:ℝ)+1)*((V:ℝ)+M+2) ≤ ((M:ℝ)+1)*((m:ℝ)+1) := by exact_mod_cast hc
  have hh : ((k:ℝ)+1)*((V:ℝ)-m+k+1) ≤ ((M:ℝ)-k)*((m:ℝ)-k) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hh (hypergeomMass_nonneg M V m k)
  have hV' : (m:ℝ) ≤ V := by exact_mod_cast hV
  have ha : 0 < ((k:ℝ)+1)*((V:ℝ)-m+k+1) := by positivity
  exact (mul_le_mul_iff_right₀ ha).mp (by nlinarith only [hm, hrec])

theorem hypergeom_hidden_unimodal_right (V M m k : ℕ) (hM : M ≤ m) (hV : m ≤ V)
    (hk : hypergeomHiddenMode V M m ≤ k) :
    hypergeomMass M V m (k+1) ≤ hypergeomMass M V m k := by
  by_cases hkM : k < M
  · have hrec := hypergeom_hidden_adjacent V M m k hM hV hkM
    have hc : (M+1)*(m+1) < (k+1)*(V+M+2) := by
      apply (Nat.div_lt_iff_lt_mul (by omega)).mp
      exact Nat.lt_succ_of_le hk
    have hc' : ((M:ℝ)+1)*((m:ℝ)+1) < ((k:ℝ)+1)*((V:ℝ)+M+2) := by exact_mod_cast hc
    have hh : ((M:ℝ)-k)*((m:ℝ)-k) ≤ ((k:ℝ)+1)*((V:ℝ)-m+k+1) := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hh (hypergeomMass_nonneg M V m k)
    have hV' : (m:ℝ) ≤ V := by exact_mod_cast hV
    have ha : 0 < ((k:ℝ)+1)*((V:ℝ)-m+k+1) := by positivity
    exact (mul_le_mul_iff_right₀ ha).mp (by nlinarith only [hm, hrec])
  · rw [hypergeomMass_high M V m (k+1) (by omega)]
    exact hypergeomMass_nonneg M V m k

/-- Exact total variation of a zero-extended unimodal sequence. -/
theorem unimodal_variation (f : ℕ → ℝ) (n l : ℕ) (hl : l ≤ n+1)
    (hleft : ∀ k < l, f k ≤ f (k+1))
    (hright : ∀ k, l ≤ k → f (k+1) ≤ f k) (hz : f (n+1)=0) :
    f 0 + ∑ k ∈ Finset.range (n+1), |f (k+1)-f k| = 2*f l := by
  rw [← Finset.sum_range_add_sum_Ico _ hl]
  have h1 : (∑ k ∈ Finset.range l, |f (k+1)-f k|) = f l-f 0 := by
    rw [← Finset.sum_range_sub f l]
    apply Finset.sum_congr rfl
    intro k hk
    exact abs_of_nonneg (sub_nonneg.mpr (hleft k (Finset.mem_range.mp hk)))
  have h2 : (∑ k ∈ Finset.Ico l (n+1), |f (k+1)-f k|) = f l-f (n+1) := by
    calc
      _ = ∑ k ∈ Finset.Ico l (n+1), -(f (k+1)-f k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact abs_of_nonpos (sub_nonpos.mpr (hright k (Finset.mem_Ico.mp hk).1))
      _ = _ := by rw [Finset.sum_neg_distrib, Finset.sum_Ico_sub _ hl]; ring
  rw [h1,h2,hz]
  ring

theorem hypergeom_hidden_variation (V M m : ℕ) (hM : M ≤ m) (hV : m ≤ V) :
    hypergeomMass M V m 0 +
      ∑ k ∈ Finset.range (M+1), |hypergeomMass M V m (k+1)-hypergeomMass M V m k| =
      2*hypergeomMass M V m (hypergeomHiddenMode V M m) := by
  apply unimodal_variation _ M (hypergeomHiddenMode V M m)
    ((hypergeomHiddenMode_le V M m hV).trans (by omega))
    (fun k hk => hypergeom_hidden_unimodal_left V M m k hM hV hk)
    (fun k hk => hypergeom_hidden_unimodal_right V M m k hM hV hk)
  exact hypergeomMass_high M V m (M+1) (by omega)
theorem choose_pred_weight (n r : ℕ) (hn : 0 < n) (hr : r ≤ n) :
    (n:ℝ)*((n-1).choose r : ℝ) = ((n:ℝ)-r)*(n.choose r : ℝ) := by
  have h := Nat.choose_mul_succ_eq (n-1) r
  rw [Nat.sub_add_cancel hn] at h
  have h' : ((n-1).choose r : ℝ)*(n:ℝ) = (n.choose r : ℝ)*((n:ℝ)-r) := by
    exact_mod_cast h
  nlinarith only [h']

theorem choose_pred_weight_succ (n r : ℕ) (hn : 0 < n) :
    (n:ℝ)*((n-1).choose r : ℝ) = ((r:ℝ)+1)*(n.choose (r+1) : ℝ) := by
  have h := Nat.add_one_mul_choose_eq (n-1) r
  rw [Nat.sub_add_cancel hn] at h
  exact_mod_cast h.trans (Nat.mul_comm _ _)

def hypergeomHiddenFlux (V M m k : ℕ) : ℝ :=
  (V:ℝ)/(V+M)*hypergeomMass M (V-1) m k

theorem hypergeomHiddenFlux_formula (V M m k : ℕ) (hM : M ≤ m) (hV : m < V) (hk : k ≤ M) :
    hypergeomHiddenFlux V M m k =
      ((V:ℝ)-m+k)/((V:ℝ)+M-m)*hypergeomMass M V m k := by
  have hN : 0 < V+M := by omega
  have hk' : k ≤ m := by omega
  have hr : m-k ≤ V := by omega
  have hmN : m ≤ V+M := by omega
  have hpred : m ≤ V+M-1 := by omega
  have hVN : (0:ℝ) < V+M := by exact_mod_cast hN
  have hd : (0:ℝ) < (V:ℝ)+M-m := by
    have hr : (m:ℝ) < (V:ℝ)+M := by exact_mod_cast (show m < V+M by omega)
    linarith
  have hCN : (0:ℝ) < (V+M).choose m := by exact_mod_cast Nat.choose_pos hmN
  have hCP : (0:ℝ) < (V+M-1).choose m := by exact_mod_cast Nat.choose_pos hpred
  have hcw := choose_pred_weight (V+M) m hN hmN
  have hcv := choose_pred_weight V (m-k) (by omega) hr
  push_cast [Nat.cast_sub hk'] at hcv
  push_cast at hcw
  unfold hypergeomHiddenFlux hypergeomMass
  rw [ite_eq_left hk', ite_eq_left hk', show M+(V-1)=V+M-1 by omega]
  have hden : ((V:ℝ)+M)*((V+M-1).choose m:ℝ) =
      ((V:ℝ)+M-m)*((V+M).choose m:ℝ) := hcw
  rw [show M+V=V+M by omega]
  calc
    _ = (M.choose k:ℝ)*((V:ℝ)*((V-1).choose (m-k):ℝ)) /
        (((V:ℝ)+M)*((V+M-1).choose m:ℝ)) := by field_simp
    _ = _ := by rw [hden, hcv]; field_simp; ring

theorem hypergeomHiddenFlux_high (V M m k : ℕ) (hk : M < k) :
    hypergeomHiddenFlux V M m k = 0 := by
  simp only [hypergeomHiddenFlux, hypergeomMass_high M (V-1) m k hk, mul_zero]

theorem hypergeomHiddenFlux_boundary (V M m : ℕ) (hM : M ≤ m) (hV : m < V) :
    hypergeomHiddenFlux V M m M = hypergeomMass M V m M := by
  rw [hypergeomHiddenFlux_formula V M m M hM hV le_rfl]
  have hd : (0:ℝ) < (V:ℝ)+M-m := by
    have hr : (m:ℝ) < (V:ℝ)+M := by exact_mod_cast (show m < V+M by omega)
    linarith
  have he : (V:ℝ)-m+M = (V:ℝ)+M-m := by ring
  rw [he, div_self hd.ne', one_mul]

theorem hypergeom_adjacent_hidden_difference (V M m k : ℕ)
    (hM : M ≤ m) (hV : m < V) (hk : k ≤ M) :
    hypergeomMass M V (m+1) (k+1) - hypergeomMass M V m k =
      hypergeomHiddenFlux V M m (k+1) - hypergeomHiddenFlux V M m k := by
  by_cases hkM : k = M
  · subst k
    rw [hypergeomMass_high M V (m+1) (M+1) (by omega),
      hypergeomHiddenFlux_high V M m (M+1) (by omega), hypergeomHiddenFlux_boundary V M m hM hV]
  have hklt : k < M := by omega
  have hkm : k+1 ≤ m := by omega
  have hkm' : k ≤ m := by omega
  have hN : 0 < V+M := by omega
  have hmN : m ≤ V+M := by omega
  have hmN' : m+1 ≤ V+M := by omega
  have hpred : m ≤ V+M-1 := by omega
  have hN0 : (0:ℝ) < (V:ℝ)+M := by exact_mod_cast hN
  have hCN : (0:ℝ) < (V+M).choose m := by exact_mod_cast Nat.choose_pos hmN
  have hCN' : (0:ℝ) < (V+M).choose (m+1) := by exact_mod_cast Nat.choose_pos hmN'
  have hCP : (0:ℝ) < (V+M-1).choose m := by exact_mod_cast Nat.choose_pos hpred
  have hcw := choose_pred_weight (V+M) m hN hmN
  have hcws := choose_pred_weight_succ (V+M) m hN
  have hcv := choose_pred_weight V (m-k) (by omega) (by omega)
  have hcvs := choose_pred_weight_succ V (m-(k+1)) (by omega)
  rw [show m-(k+1)+1=m-k by omega] at hcvs
  have hMrec := Nat.choose_succ_right_eq M k
  have hMrec' : (M.choose (k+1):ℝ)*((k:ℝ)+1) = (M.choose k:ℝ)*((M:ℝ)-k) := by
    exact_mod_cast hMrec
  push_cast at hcw hcws
  push_cast [Nat.cast_sub hkm'] at hcv
  push_cast [Nat.cast_sub hkm] at hcvs
  unfold hypergeomHiddenFlux hypergeomMass
  rw [ite_eq_left (by omega : k+1 ≤ m+1), ite_eq_left hkm', ite_eq_left hkm, ite_eq_left hkm',
    show m+1-(k+1)=m-k by omega, show M+V=V+M by omega,
    show M+(V-1)=V+M-1 by omega]
  have hpold : (M.choose k:ℝ)*(V.choose (m-k):ℝ)/( (V+M).choose m:ℝ) =
      ((V:ℝ)+M-m)*(M.choose k:ℝ)*(V.choose (m-k):ℝ) /
      (((V:ℝ)+M)*((V+M-1).choose m:ℝ)) := by
    apply (div_eq_div_iff hCN.ne' (mul_pos hN0 hCP).ne').mpr
    rw [hcw]; ring
  have hpnew : (M.choose (k+1):ℝ)*(V.choose (m-k):ℝ)/( (V+M).choose (m+1):ℝ) =
      ((m:ℝ)+1)*(M.choose (k+1):ℝ)*(V.choose (m-k):ℝ) /
      (((V:ℝ)+M)*((V+M-1).choose m:ℝ)) := by
    apply (div_eq_div_iff hCN'.ne' (mul_pos hN0 hCP).ne').mpr
    rw [hcws]; ring
  rw [hpold,hpnew]
  have hF (j : ℕ) : (V:ℝ)/((V:ℝ)+M)*((M.choose j:ℝ)*((V-1).choose (m-j):ℝ)/
      ((V+M-1).choose m:ℝ)) = (M.choose j:ℝ)*((V:ℝ)*((V-1).choose (m-j):ℝ)) /
      (((V:ℝ)+M)*((V+M-1).choose m:ℝ)) := by field_simp
  rw [hF, hF, hcv, hcvs]
  rw [← sub_div, ← sub_div]
  congr 1
  have hh := congrArg (fun z : ℝ => z*(V.choose (m-k):ℝ)) hMrec'
  nlinarith only [hh]


theorem hypergeom_next_zero (V M m : ℕ) (hV : m < V) :
    hypergeomMass M V (m+1) 0 = hypergeomHiddenFlux V M m 0 := by
  have hN : 0 < V+M := by omega
  have hN0 : (0:ℝ) < (V:ℝ)+M := by exact_mod_cast hN
  have hCN : (0:ℝ) < (V+M).choose (m+1) := by exact_mod_cast Nat.choose_pos (show m+1 ≤ V+M by omega)
  have hCP : (0:ℝ) < (V+M-1).choose m := by exact_mod_cast Nat.choose_pos (show m ≤ V+M-1 by omega)
  have hcw := choose_pred_weight_succ (V+M) m hN
  have hcv := choose_pred_weight_succ V m (by omega)
  push_cast at hcw hcv
  unfold hypergeomHiddenFlux hypergeomMass
  simp only [Nat.zero_le, ite_true, Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul]
  rw [show M+V=V+M by omega, show M+(V-1)=V+M-1 by omega]
  rw [div_mul_div_comm]
  apply (div_eq_div_iff hCN.ne' (mul_pos hN0 hCP).ne').mpr
  have hh := congrArg (fun z : ℝ => z*(V.choose (m+1):ℝ)) hcw
  have hh' := congrArg (fun z : ℝ => z*((V+M).choose (m+1):ℝ)) hcv
  nlinarith only [hh,hh']

/-- Exact adjacent visible-count TV, expressed with complementary hidden counts.
The shift by one is essential: the two totals are different. -/
def adjacentHypergeomTV (V M m : ℕ) : ℝ :=
  (1/2:ℝ)*(hypergeomMass M V (m+1) 0 +
    ∑ k ∈ Finset.range (M+1), |hypergeomMass M V (m+1) (k+1)-hypergeomMass M V m k|)

theorem adjacentHypergeomTV_eq_flux (V M m : ℕ) (hM : M ≤ m) (hV : m < V) :
    adjacentHypergeomTV V M m =
      hypergeomHiddenFlux V M m (hypergeomHiddenMode (V-1) M m) := by
  unfold adjacentHypergeomTV
  rw [hypergeom_next_zero V M m hV]
  have he : (∑ k ∈ Finset.range (M+1),
      |hypergeomMass M V (m+1) (k+1)-hypergeomMass M V m k|) =
      ∑ k ∈ Finset.range (M+1), |hypergeomHiddenFlux V M m (k+1)-hypergeomHiddenFlux V M m k| := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hypergeom_adjacent_hidden_difference V M m k hM hV (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)]
  rw [he]
  unfold hypergeomHiddenFlux
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (V:ℝ)/(V+M))]
  rw [← Finset.mul_sum, ← mul_add, hypergeom_hidden_variation (V-1) M m hM (by omega)]
  ring

theorem adjacentHypergeomTV_le_mass (V M m : ℕ) (hM : M ≤ m) (hV : m < V) :
    adjacentHypergeomTV V M m ≤ hypergeomMass M V m (hypergeomHiddenMode (V-1) M m) := by
  rw [adjacentHypergeomTV_eq_flux V M m hM hV,
    hypergeomHiddenFlux_formula V M m _ hM hV (hypergeomHiddenMode_le (V-1) M m (by omega))]
  have hk := hypergeomHiddenMode_le (V-1) M m (by omega : m ≤ V-1)
  have hk' : (hypergeomHiddenMode (V-1) M m:ℝ) ≤ M := by exact_mod_cast hk
  have hm' : (m:ℝ) < V := by exact_mod_cast hV
  have hd : (0:ℝ) < (V:ℝ)+M-m := by linarith [Nat.cast_nonneg (α := ℝ) M]
  apply mul_le_of_le_one_left (hypergeomMass_nonneg _ _ _ _)
  apply (div_le_one hd).mpr
  linarith

end TraceReconstruction

namespace TraceReconstruction
def bernoulliRelativeEntropy (θ p : ℝ) : ℝ :=
  θ*Real.log (θ/p)+(1-θ)*Real.log ((1-θ)/(1-p))

theorem bernoulliRelativeEntropy_upper {θ p : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1) (hp : p ∈ Set.Ioo 0 1) :
    bernoulliRelativeEntropy θ p ≤ (θ-p)^2/(p*(1-p)) := by
  have h1 := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hθ.1 hp.1)) hθ.1.le
  have h2 := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos
    (div_pos (sub_pos.mpr hθ.2) (sub_pos.mpr hp.2))) (sub_nonneg.mpr hθ.2.le)
  have he : θ*(θ/p-1)+(1-θ)*((1-θ)/(1-p)-1) = (θ-p)^2/(p*(1-p)) := by
    field_simp [hp.1.ne', (sub_pos.mpr hp.2).ne']; ring
  unfold bernoulliRelativeEntropy
  rw [← he]
  linarith

theorem binomialMass_change_probability (n k : ℕ) {θ p : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1) (hp : p ∈ Set.Ioo 0 1) :
    binomialMass n p k = binomialMass n θ k *
      Real.exp ((k:ℝ)*Real.log (p/θ)+(n-k:ℕ)*Real.log ((1-p)/(1-θ))) := by
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (div_pos hp.1 hθ.1),
    Real.exp_log (div_pos (sub_pos.mpr hp.2) (sub_pos.mpr hθ.2))]
  unfold binomialMass
  simp only [div_pow]
  field_simp [hθ.1.ne', (sub_pos.mpr hθ.2).ne']

theorem binomialMass_mean_change_probability (n k : ℕ) {θ p : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1) (hp : p ∈ Set.Ioo 0 1)
    (hk : k ≤ n) (hmean : (n:ℝ)*θ = k) :
    binomialMass n p k = binomialMass n θ k * Real.exp (-(n:ℝ)*bernoulliRelativeEntropy θ p) := by
  rw [binomialMass_change_probability n k hθ hp]
  congr 2
  rw [Nat.cast_sub hk, ← hmean]
  unfold bernoulliRelativeEntropy
  rw [Real.log_div hp.1.ne' hθ.1.ne', Real.log_div (sub_pos.mpr hp.2).ne' (sub_pos.mpr hθ.2).ne',
    Real.log_div hθ.1.ne' hp.1.ne', Real.log_div (sub_pos.mpr hθ.2).ne' (sub_pos.mpr hp.2).ne']
  ring

/-- Uniform local binomial lower bound without Stirling. It applies at a
count `k` by changing to the channel with mean exactly `k`. -/
theorem binomialMass_local_lower (n k : ℕ) {θ p : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1) (hp : p ∈ Set.Ioo 0 1)
    (hk : k ≤ n) (hmean : (n:ℝ)*θ = k) (hv : 1 ≤ (n:ℝ)*θ*(1-θ)) :
    Real.exp (-(n:ℝ)*(θ-p)^2/(p*(1-p))) /
      (12*Real.sqrt ((n:ℝ)*θ*(1-θ))) ≤ binomialMass n p k := by
  rw [binomialMass_mean_change_probability n k hθ hp hk hmean]
  have hlow := binomialMass_mean_lower n k hθ hk hmean hv
  have hexp : Real.exp (-(n:ℝ)*(θ-p)^2/(p*(1-p))) ≤
      Real.exp (-(n:ℝ)*bernoulliRelativeEntropy θ p) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonpos_left (bernoulliRelativeEntropy_upper hθ hp) (neg_nonpos.mpr (Nat.cast_nonneg n))
    simpa only [mul_div_assoc] using this
  have hh := mul_le_mul hlow hexp (Real.exp_pos _).le
    (binomialMass_nonneg n k ⟨hθ.1.le,hθ.2.le⟩)
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hh

end TraceReconstruction

end

end OAI
