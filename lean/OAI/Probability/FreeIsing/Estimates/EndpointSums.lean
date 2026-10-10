import OAI.Probability.FreeIsing.Trees.PathCutoff

namespace OAI

noncomputable section

open Filter

namespace Problem367

theorem tsum_le_prefix_add_majorant {f g : ℕ → ℝ} (R : ℕ)
    (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n) (hg : Summable g)
    (htail : ∀ n, R ≤ n → f n ≤ g n) :
    (∑' n, f n) ≤ (∑ n ∈ Finset.range R, f n) + ∑' n, g n := by
  have hf : Summable f := hg.of_norm_bounded_eventually_nat <|
    eventually_atTop.mpr ⟨R, fun n hn => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 n)]
      exact htail n hn⟩
  have hft : Summable (fun n => f (n + R)) := (summable_nat_add_iff R).mpr hf
  have hgt : Summable (fun n => g (n + R)) := (summable_nat_add_iff R).mpr hg
  calc
    (∑' n, f n) = (∑ n ∈ Finset.range R, f n) + ∑' n, f (n + R) :=
      (hf.sum_add_tsum_nat_add R).symm
    _ ≤ (∑ n ∈ Finset.range R, f n) + ∑' n, g (n + R) := by
      exact add_le_add le_rfl (hft.tsum_le_tsum
        (fun n => htail (n + R) (Nat.le_add_left R n)) hgt)
    _ ≤ (∑ n ∈ Finset.range R, f n) + ∑' n, g n := by
      apply add_le_add le_rfl
      exact tsum_comp_le_tsum_of_inj (i := fun n : ℕ => n + R) hg hg0
        (fun m n h => Nat.add_right_cancel h)

theorem sum_range_nat_pow_le (R k : ℕ) :
    (∑ n ∈ Finset.range R, (n : ℝ) ^ k) ≤ (R : ℝ) ^ (k + 1) := by
  calc
    _ ≤ ∑ _n ∈ Finset.range R, (R : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro n hn
      have h : (n : ℝ) ≤ R := by exact_mod_cast (Finset.mem_range.mp hn).le
      exact pow_le_pow_left₀ (Nat.cast_nonneg n) h k
    _ = (R : ℝ) ^ (k + 1) := by simp [pow_succ, mul_comm]

theorem sum_range_sqrt_le (R : ℕ) :
    (∑ n ∈ Finset.range R, Real.sqrt n) ≤ (R : ℝ) * Real.sqrt R := by
  calc
    _ ≤ ∑ _n ∈ Finset.range R, Real.sqrt R := by
      apply Finset.sum_le_sum
      intro n hn
      apply Real.sqrt_le_sqrt
      exact_mod_cast (Finset.mem_range.mp hn).le
    _ = (R : ℝ) * Real.sqrt R := by simp

theorem tsum_integer_path_endpoint_le {f : ℕ → ℝ} (R k m : ℕ)
    {A B E c a q : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (hc1 : c ≤ 1) (ha : 0 < a) (hq : 1 < q)
    (hshort : ∀ n, n < R → f n ≤ A * (n : ℝ) ^ k)
    (htail : ∀ n, R ≤ n → f n ≤
      B * ((n : ℝ) ^ k * Real.exp (-c * n)) +
      E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :
    (∑' n, f n) ≤ A * (R : ℝ) ^ (k + 1) +
      B * ((k.factorial : ℝ) * (2 / c) ^ (k + 1)) +
      E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-a * q ^ n)) := by
  have hpoly := summable_path_attenuation k hc
  have hexception := summable_superexponential_path m ha hq
  have hg := (hpoly.mul_left B).add (hexception.mul_left E)
  have hprefix : (∑ n ∈ Finset.range R, f n) ≤ A * (R : ℝ) ^ (k + 1) := by
    calc
      _ ≤ ∑ n ∈ Finset.range R, A * (n : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro n hn
        exact hshort n (Finset.mem_range.mp hn)
      _ = A * (∑ n ∈ Finset.range R, (n : ℝ) ^ k) := by rw [Finset.mul_sum]
      _ ≤ A * (R : ℝ) ^ (k + 1) :=
        mul_le_mul_of_nonneg_left (sum_range_nat_pow_le R k) hA
  calc
    _ ≤ (∑ n ∈ Finset.range R, f n) +
        ∑' n : ℕ, (B * ((n : ℝ) ^ k * Real.exp (-c * n)) +
          E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :=
      tsum_le_prefix_add_majorant R hf0 (fun n => by positivity) hg htail
    _ = (∑ n ∈ Finset.range R, f n) +
        (B * (∑' n : ℕ, (n : ℝ) ^ k * Real.exp (-c * n)) +
          E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-a * q ^ n))) := by
      rw [(hpoly.mul_left B).tsum_add (hexception.mul_left E), tsum_mul_left, tsum_mul_left]
    _ ≤ A * (R : ℝ) ^ (k + 1) +
        (B * ((k.factorial : ℝ) * (2 / c) ^ (k + 1)) +
          E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-a * q ^ n))) := by
      exact add_le_add hprefix (add_le_add
        (mul_le_mul_of_nonneg_left (tsum_path_attenuation_small_le k hc hc1) hB) le_rfl)
    _ = _ := by ring

theorem tsum_sqrt_path_endpoint_le {f : ℕ → ℝ} (R m : ℕ)
    {A B E c a q : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (hc1 : c ≤ 1) (ha : 0 < a) (hq : 1 < q)
    (hshort : ∀ n, n < R → f n ≤ A * Real.sqrt n)
    (htail : ∀ n, R ≤ n → f n ≤
      B * (Real.sqrt n * Real.exp (-c * n)) +
      E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :
    (∑' n, f n) ≤ A * ((R : ℝ) * Real.sqrt R) +
      B * (3 / (c * Real.sqrt c)) +
      E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-a * q ^ n)) := by
  have hpoly := summable_sqrt_path_attenuation hc
  have hexception := summable_superexponential_path m ha hq
  have hg := (hpoly.mul_left B).add (hexception.mul_left E)
  have hprefix : (∑ n ∈ Finset.range R, f n) ≤ A * ((R : ℝ) * Real.sqrt R) := by
    calc
      _ ≤ ∑ n ∈ Finset.range R, A * Real.sqrt n := by
        apply Finset.sum_le_sum
        intro n hn
        exact hshort n (Finset.mem_range.mp hn)
      _ = A * (∑ n ∈ Finset.range R, Real.sqrt n) := by rw [Finset.mul_sum]
      _ ≤ A * ((R : ℝ) * Real.sqrt R) :=
        mul_le_mul_of_nonneg_left (sum_range_sqrt_le R) hA
  calc
    _ ≤ (∑ n ∈ Finset.range R, f n) +
        ∑' n : ℕ, (B * (Real.sqrt n * Real.exp (-c * n)) +
          E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :=
      tsum_le_prefix_add_majorant R hf0 (fun n => by positivity) hg htail
    _ = (∑ n ∈ Finset.range R, f n) +
        (B * (∑' n : ℕ, Real.sqrt n * Real.exp (-c * n)) +
          E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-a * q ^ n))) := by
      rw [(hpoly.mul_left B).tsum_add (hexception.mul_left E), tsum_mul_left, tsum_mul_left]
    _ ≤ A * ((R : ℝ) * Real.sqrt R) +
        (B * (3 / (c * Real.sqrt c)) +
          E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-a * q ^ n))) := by
      exact add_le_add hprefix (add_le_add
        (mul_le_mul_of_nonneg_left (tsum_sqrt_path_attenuation_le hc hc1) hB) le_rfl)
    _ = _ := by ring

end Problem367

end

end OAI
