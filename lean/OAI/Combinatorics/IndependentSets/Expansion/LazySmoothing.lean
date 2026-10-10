import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.Bits

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.LazySmoothing

open scoped BigOperators

def bitCount {n : ℕ} (tape : Fin n → Bool) : ℕ :=
  ∑ i, if tape i then 1 else 0

noncomputable def binomialMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  Finset.univ.expect (fun tape : Fin n → Bool => g (bitCount tape))

def splitTape (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Bool × (Fin n → Bool)) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv _ := rfl

theorem bitCount_succ {n : ℕ} (x : Fin (n + 1) → Bool) :
    bitCount x = (if x 0 then 1 else 0) + bitCount (fun i => x i.succ) := by
  exact Fin.sum_univ_succ _

theorem mean_congr {n : ℕ} {f g : ℕ → ℝ} (h : ∀ k, f k = g k) :
    binomialMean n f = binomialMean n g := by
  unfold binomialMean
  exact Finset.expect_congr rfl (fun x _ => h (bitCount x))

@[simp] theorem mean_const (n : ℕ) (c : ℝ) :
    binomialMean n (fun _ => c) = c := Fintype.expect_const c

theorem mean_add (n : ℕ) (f g : ℕ → ℝ) :
    binomialMean n (fun k => f k + g k) = binomialMean n f + binomialMean n g :=
  Finset.expect_add_distrib _ _ _

theorem mean_sub (n : ℕ) (f g : ℕ → ℝ) :
    binomialMean n (fun k => f k - g k) = binomialMean n f - binomialMean n g :=
  Finset.expect_sub_distrib _ _ _

theorem mean_mul (n : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    binomialMean n (fun k => c * f k) = c * binomialMean n f := by
  exact (Finset.mul_expect Finset.univ (fun x : Fin n → Bool => f (bitCount x)) c).symm

@[simp] theorem mean_zero (g : ℕ → ℝ) : binomialMean 0 g = g 0 := by
  simp [binomialMean, bitCount]

theorem expect_bool (f : Bool → ℝ) : Finset.univ.expect f = (f false + f true) / 2 := by
  rw [Finset.expect_eq_sum_div_card]
  simp [Fintype.univ_bool, add_comm]

theorem mean_succ (n : ℕ) (g : ℕ → ℝ) :
    binomialMean (n + 1) g =
      (binomialMean n g + binomialMean n (fun k => g (k + 1))) / 2 := by
  unfold binomialMean
  rw [Fintype.expect_equiv (splitTape n)
    (fun x => g (bitCount x))
    (fun x => g ((if x.1 then 1 else 0) + bitCount x.2))
    (fun x => congrArg g (bitCount_succ x))]
  rw [← Finset.univ_product_univ, Finset.expect_product, expect_bool]
  simp [Nat.add_comm]

def score (n k : ℕ) : ℝ := (n : ℝ) - 2 * (k : ℝ)

noncomputable def scoreMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  binomialMean n (fun k => score n k * g k)

@[simp] theorem scoreMean_zero (g : ℕ → ℝ) : scoreMean 0 g = 0 := by
  simp [scoreMean, score]

theorem scoreMean_succ (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g =
      ((scoreMean n g + binomialMean n g) +
       (scoreMean n (fun k => g (k + 1)) -
        binomialMean n (fun k => g (k + 1)))) / 2 := by
  unfold scoreMean
  rw [mean_succ]
  have h₁ : (fun k => score (n + 1) k * g k) =
      (fun k => score n k * g k + g k) := by
    funext k
    simp only [score, Nat.cast_add, Nat.cast_one]
    ring
  have h₂ : (fun k => score (n + 1) (k + 1) * g (k + 1)) =
      (fun k => score n k * g (k + 1) - g (k + 1)) := by
    funext k
    simp only [score, Nat.cast_add, Nat.cast_one]
    ring
  rw [h₁, h₂, mean_add, mean_sub]

theorem score_identity (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g = ((n : ℝ) + 1) / 2 *
      (binomialMean n g - binomialMean n (fun k => g (k + 1))) := by
  induction n generalizing g with
  | zero => simp [scoreMean_succ]; ring
  | succ n ih =>
    rw [scoreMean_succ, ih g, ih (fun k => g (k + 1))]
    simp only [mean_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem score_mean_zero (n : ℕ) : binomialMean n (score n) = 0 := by
  cases n with
  | zero => simp [score]
  | succ n =>
    have h := score_identity n (fun _ => 1)
    simpa [scoreMean] using h

theorem score_second_moment (n : ℕ) :
    binomialMean n (fun k => score n k ^ 2) = (n : ℝ) := by
  cases n with
  | zero => simp [score]
  | succ n =>
    have h := score_identity n (score (n + 1))
    have hd : binomialMean n (score (n + 1)) -
        binomialMean n (fun k => score (n + 1) (k + 1)) = 2 := by
      rw [← mean_sub]
      calc
        _ = binomialMean n (fun _ => 2) := by
          apply mean_congr
          intro k
          simp only [score, Nat.cast_add, Nat.cast_one]
          ring
        _ = 2 := mean_const _ _
    rw [hd] at h
    simpa [scoreMean, pow_two] using h

theorem score_difference (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g = ((n : ℝ) + 1) *
      (binomialMean n g - binomialMean (n + 1) g) := by
  rw [score_identity, mean_succ]
  ring

theorem adjacent_difference_sq (n : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    4 * ((n : ℝ) + 1) *
      (binomialMean n g - binomialMean (n + 1) g) ^ 2 ≤ 1 := by
  have hc : binomialMean (n + 1)
      (fun k => score (n + 1) k * (g k - 1 / 2)) = scoreMean (n + 1) g := by
    calc
      _ = binomialMean (n + 1) (fun k =>
          score (n + 1) k * g k - (1 / 2) * score (n + 1) k) := by
        apply mean_congr
        intro k
        ring
      _ = scoreMean (n + 1) g := by
        rw [mean_sub, mean_mul, score_mean_zero]
        simp [scoreMean]
  have hv : binomialMean (n + 1) (fun k => (g k - 1 / 2) ^ 2) ≤ 1 / 4 := by
    apply Finset.expect_le Finset.univ_nonempty
    intro tape _
    have h₀ := (hg (bitCount tape)).1
    have h₁ := (hg (bitCount tape)).2
    have hp := mul_nonneg h₀ (sub_nonneg.mpr h₁)
    nlinarith
  have hcs : (binomialMean (n + 1)
        (fun k => score (n + 1) k * (g k - 1 / 2))) ^ 2 ≤
      binomialMean (n + 1) (fun k => score (n + 1) k ^ 2) *
        binomialMean (n + 1) (fun k => (g k - 1 / 2) ^ 2) :=
    Finset.expect_mul_sq_le_sq_mul_sq Finset.univ _ _
  rw [hc, score_difference, score_second_moment] at hcs
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hm := mul_le_mul_of_nonneg_left hv (le_of_lt hn)
  simp only [Nat.cast_add, Nat.cast_one] at hcs
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith

theorem adjacent_difference_le (n : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrn : r ^ 2 ≤ 4 * ((n : ℝ) + 1)) :
    |binomialMean n g - binomialMean (n + 1) g| ≤ 1 / r := by
  have hs := adjacent_difference_sq n g hg
  have hd := sq_nonneg (binomialMean n g - binomialMean (n + 1) g)
  have hh := mul_le_mul_of_nonneg_right hrn hd
  rw [le_div_iff₀ hr]
  have ha := sq_abs (binomialMean n g - binomialMean (n + 1) g)
  have hp : 0 ≤ |binomialMean n g - binomialMean (n + 1) g| * r :=
    mul_nonneg (abs_nonneg _) (le_of_lt hr)
  nlinarith [sq_nonneg (|binomialMean n g - binomialMean (n + 1) g| * r - 1)]

theorem mean_shift_le (n d : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrn : r ^ 2 ≤ 4 * ((n : ℝ) + 1)) :
    |binomialMean (n + d) g - binomialMean n g| ≤ (d : ℝ) / r := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hrnd : r ^ 2 ≤ 4 * ((n + d : ℕ) + 1 : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      linarith
    have ha := adjacent_difference_le (n + d) g hg r hr hrnd
    rw [abs_sub_comm] at ha
    calc
      _ ≤ |binomialMean (n + d + 1) g - binomialMean (n + d) g| +
          |binomialMean (n + d) g - binomialMean n g| := abs_sub_le _ _ _
      _ ≤ 1 / r + (d : ℝ) / r := add_le_add ha ih
      _ = ((d + 1 : ℕ) : ℝ) / r := by push_cast; ring

theorem mean_ordered_difference_le (m n : ℕ) (hmn : m ≤ n) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrm : r ^ 2 ≤ 4 * ((m : ℝ) + 1)) :
    |binomialMean n g - binomialMean m g| ≤ ((n - m : ℕ) : ℝ) / r := by
  simpa [Nat.add_sub_of_le hmn] using mean_shift_le m (n - m) g hg r hr hrm

theorem mean_window_le (N M m : ℕ) (hlo : N - M ≤ m) (hhi : m ≤ N + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1)
    (r : ℝ) (hr : 0 < r) (hbase : r ^ 2 ≤ 4 * (((N - M : ℕ) : ℝ) + 1)) :
    |binomialMean m g - binomialMean N g| ≤ (M : ℝ) / r := by
  by_cases hmN : m ≤ N
  · have hrm : r ^ 2 ≤ 4 * ((m : ℝ) + 1) := by
      have : ((N - M : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlo
      linarith
    have h := mean_ordered_difference_le m N hmN g hg r hr hrm
    rw [abs_sub_comm] at h
    refine h.trans (div_le_div_of_nonneg_right ?_ (le_of_lt hr))
    have : N - m ≤ M := by omega
    exact_mod_cast this
  · have hNm : N ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmN)
    have hrN : r ^ 2 ≤ 4 * ((N : ℝ) + 1) := by
      have : ((N - M : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N M
      linarith
    have h := mean_ordered_difference_le N m hNm g hg r hr hrN
    refine h.trans (div_le_div_of_nonneg_right ?_ (le_of_lt hr))
    have : m - N ≤ M := by omega
    exact_mod_cast this

theorem square_window_le (q M m : ℕ) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    |binomialMean m g - binomialMean ((4 * q * M) ^ 2) g| ≤ 1 / (4 * (q : ℝ)) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hR : (4 : ℝ) * M ≤ ((4 * q * M : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hRM : (M : ℝ) ≤ (((4 * q * M : ℕ) : ℝ)) ^ 2 := by nlinarith
  have hMN : M ≤ (4 * q * M) ^ 2 := by exact_mod_cast hRM
  have hr : (0 : ℝ) < ((4 * q * M : ℕ) : ℝ) := by linarith
  have hb : (((4 * q * M : ℕ) : ℝ)) ^ 2 ≤
      4 * (((((4 * q * M) ^ 2 - M : ℕ)) : ℝ) + 1) := by
    rw [Nat.cast_sub hMN, Nat.cast_pow]
    nlinarith
  have h := mean_window_le ((4 * q * M) ^ 2) M m hlo hhi g hg
    ((4 * q * M : ℕ) : ℝ) hr hb
  have he : (M : ℝ) / ((4 * q * M : ℕ) : ℝ) = 1 / (4 * (q : ℝ)) := by
    push_cast
    have hq0 : (q : ℝ) ≠ 0 := by linarith
    have hM0 : (M : ℝ) ≠ 0 := by linarith
    field_simp
  rw [he] at h
  exact h

theorem modal_transfer (q M m : ℕ) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1)
    (hmodal : 1 / (q : ℝ) ≤ binomialMean ((4 * q * M) ^ 2) g) :
    1 / (2 * (q : ℝ)) ≤ binomialMean m g := by
  have h := square_window_le q M m hq hM hlo hhi g hg
  have hqR : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hrec : 0 < 1 / (q : ℝ) := one_div_pos.mpr hqR
  have he₁ : 1 / (4 * (q : ℝ)) = (1 / (q : ℝ)) / 4 := by ring
  have he₂ : 1 / (2 * (q : ℝ)) = (1 / (q : ℝ)) / 2 := by ring
  rw [he₁] at h
  rw [he₂]
  have hl := (abs_le.mp h).1
  linarith

end IndependentSetsGames.Foundations.PCP.LazySmoothing

end OAI
