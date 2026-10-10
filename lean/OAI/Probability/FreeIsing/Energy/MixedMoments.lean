import OAI.Probability.FreeIsing.Energy.IndependentMoments
import OAI.Probability.FreeIsing.Energy.MomentInduction

namespace OAI

namespace Problem367

theorem exists_two_positive_of_mixed
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℕ} {p : ℕ}
    (hsum : ∑ i, r i = p) (hp : 0 < p) (hmixed : ¬ ∃ i, r i = p) :
    ∃ i j, i ≠ j ∧ 0 < r i ∧ 0 < r j := by
  classical
  have hpos : 0 < ∑ i, r i := by simpa only [hsum] using hp
  obtain ⟨i, hi, hri⟩ := Finset.sum_pos_iff.mp hpos
  have hrest : 0 < ∑ j ∈ Finset.univ.erase i, r j := by
    have hh := Finset.sum_erase_add Finset.univ r hi
    rw [hsum] at hh
    have hine : r i ≠ p := fun heq => hmixed ⟨i, heq⟩
    omega
  obtain ⟨j, hj, hrj⟩ := Finset.sum_pos_iff.mp hrest
  exact ⟨i, j, Ne.symm (Finset.mem_erase.mp hj).1, hri, hrj⟩

theorem mixed_sum_sq_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℕ} {p : ℕ}
    (hsum : ∑ i, r i = p) (hp : 0 < p) (hmixed : ¬ ∃ i, r i = p) :
    ∑ i, (r i : ℝ)^2 ≤ (p : ℝ)^2 - 2 * ((p : ℝ) - 1) := by
  obtain ⟨i, j, hij, hri, hrj⟩ := exists_two_positive_of_mixed hsum hp hmixed
  have hs := sum_sq_le_of_two_positive Finset.univ r
    (Finset.mem_univ i) (Finset.mem_univ j) hij hri hrj
  rw [hsum] at hs
  have hs' : ∑ i, (r i : ℝ)^2 ≤ ((p - 1 : ℕ) : ℝ)^2 + 1 := by exact_mod_cast hs
  rw [Nat.cast_sub hp, Nat.cast_one] at hs'
  nlinarith

theorem mixed_moment_product_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℕ} {p : ℕ}
    (hsum : ∑ i, r i = p) (hp : 0 < p) (hmixed : ¬ ∃ i, r i = p)
    {K t : ℝ} (hK : 0 ≤ K) (ht : 0 < t)
    (M : ι → ℕ → ℝ) (hM : ∀ i k, 0 ≤ M i k)
    (hbound : ∀ i k, k < p → M i k ≤
      Real.exp (K * (k : ℝ)^2) * t ^ ((k : ℝ) / 4)) :
    ∏ i, M i (r i) ≤
      Real.exp (K * ((p : ℝ)^2 - 2 * ((p : ℝ) - 1))) * t ^ ((p : ℝ) / 4) := by
  have hri : ∀ i, r i < p := by
    intro i
    have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => Nat.zero_le (r j))
      (Finset.mem_univ i)
    rw [hsum] at hh
    have hn : r i ≠ p := fun heq => hmixed ⟨i, heq⟩
    omega
  have hsum' : ∑ i, (r i : ℝ) = p := by exact_mod_cast hsum
  calc
    ∏ i, M i (r i) ≤
        ∏ i, (Real.exp (K * (r i : ℝ)^2) * t ^ ((r i : ℝ) / 4)) :=
      Finset.prod_le_prod₀ (fun i _ => hM i (r i)) (fun i _ => hbound i (r i) (hri i))
    _ = Real.exp (K * ∑ i, (r i : ℝ)^2) * t ^ ((p : ℝ) / 4) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Real.rpow_sum_of_pos ht,
        ← Finset.mul_sum, ← Finset.sum_div, hsum']
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (mixed_sum_sq_le hsum hp hmixed) hK))
      (Real.rpow_nonneg ht.le _)

theorem mixed_multinomial_sum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} (hp : 0 < p)
    {K t : ℝ} (hK : 0 ≤ K) (ht : 0 < t)
    (M : ι → ℕ → ℝ) (hM : ∀ i k, 0 ≤ M i k)
    (hbound : ∀ i k, k < p → M i k ≤
      Real.exp (K * (k : ℝ)^2) * t ^ ((k : ℝ) / 4)) :
    (∑ r ∈ (Finset.piAntidiag (Finset.univ : Finset ι) p).filter
      (fun r => ¬ ∃ i, r i = p),
      (Nat.multinomial Finset.univ r : ℝ) * ∏ i, M i (r i)) ≤
        (Fintype.card ι : ℝ)^p *
          (Real.exp (K * ((p : ℝ)^2 - 2 * ((p : ℝ) - 1))) * t ^ ((p : ℝ) / 4)) := by
  classical
  let A := Finset.piAntidiag (Finset.univ : Finset ι) p
  let C := Real.exp (K * ((p : ℝ)^2 - 2 * ((p : ℝ) - 1))) * t ^ ((p : ℝ) / 4)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum : (∑ r ∈ A, (Nat.multinomial Finset.univ r : ℝ)) = (Fintype.card ι : ℝ)^p := by
    have hh := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset ι) (fun _ => (1 : ℝ)) p
    simpa [A] using hh.symm
  calc
    _ ≤ ∑ r ∈ A.filter (fun r => ¬ ∃ i, r i = p),
        (Nat.multinomial Finset.univ r : ℝ) * C := by
      apply Finset.sum_le_sum
      intro r hr
      obtain ⟨hrA, hrMix⟩ := Finset.mem_filter.mp hr
      have hrSum := (Finset.mem_piAntidiag.mp hrA).1
      exact mul_le_mul_of_nonneg_left
        (mixed_moment_product_le hrSum hp hrMix hK ht M hM hbound) (Nat.cast_nonneg _)
    _ = (∑ r ∈ A.filter (fun r => ¬ ∃ i, r i = p),
        (Nat.multinomial Finset.univ r : ℝ)) * C := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ r ∈ A, (Nat.multinomial Finset.univ r : ℝ)) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun r _ _ => Nat.cast_nonneg _)
    _ = _ := by rw [hsum]

open MeasureTheory ProbabilityTheory in

theorem independent_abs_moment_le_pure_add_remainder
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : iIndepFun X μ) (hmX : ∀ i, Measurable (X i))
    {p : ℕ} (hp : 0 < p)
    (hMom : ∀ i k, k ≤ p → Integrable (fun ω => |X i ω| ^ k) μ)
    {K t : ℝ} (hK : 0 ≤ K) (ht : 0 < t)
    (hbound : ∀ i k, k < p → (∫ ω, |X i ω| ^ k ∂μ) ≤
      Real.exp (K * (k : ℝ)^2) * t ^ ((k : ℝ) / 4)) :
    (∫ ω, |∑ i, X i ω| ^ p ∂μ) ≤ (∑ i, ∫ ω, |X i ω| ^ p ∂μ) +
      (Fintype.card ι : ℝ)^p *
        (Real.exp (K * ((p : ℝ)^2 - 2 * ((p : ℝ) - 1))) * t ^ ((p : ℝ) / 4)) := by
  classical
  let M : ι → ℕ → ℝ := fun i k => ∫ ω, |X i ω| ^ k ∂μ
  have hzero : ∀ i, M i 0 = 1 := by intro i; simp [M]
  have hM : ∀ i k, 0 ≤ M i k := by
    intro i k
    exact integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) _)
  calc
    _ ≤ ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) p,
        (Nat.multinomial Finset.univ r : ℝ) * ∏ i, M i (r i) :=
      integral_abs_sum_pow_le_of_iIndepFun hX hmX p hMom
    _ = (∑ i, M i p) +
        ∑ r ∈ (Finset.piAntidiag (Finset.univ : Finset ι) p).filter
          (fun r => ¬ ∃ i, r i = p),
          (Nat.multinomial Finset.univ r : ℝ) * ∏ i, M i (r i) :=
      multinomial_sum_eq_pure_add_mixed M hzero hp
    _ ≤ _ := add_le_add (le_refl _) (mixed_multinomial_sum_le hp hK ht M hM hbound)

end Problem367

end OAI
