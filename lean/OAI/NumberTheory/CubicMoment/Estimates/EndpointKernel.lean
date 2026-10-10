import OAI.NumberTheory.CubicMoment.Estimates.PowerSavings

namespace OAI

/-!
# Summing the sharp-cutoff endpoint kernel

The Fourier truncation argument sums rapidly decaying endpoint errors over
integer norms. These bounds supply the quantitative lattice step in
`eq:perron-error`, uniformly in the location of the endpoint.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

def endpointKernel (h d : ℝ) : ℝ := h ^ 2 / (h + |d|) ^ 2

lemma endpointKernel_nonneg (h d : ℝ) : 0 ≤ endpointKernel h d := by
  exact div_nonneg (sq_nonneg h) (sq_nonneg _)

lemma endpointKernel_nat_step {h : ℝ} (hh : 0 < h) (k : ℕ) :
    h ^ 2 / (h + (k : ℝ) + 1) ^ 2 ≤
      h ^ 2 / (h + (k : ℝ)) - h ^ 2 / (h + (k : ℝ) + 1) := by
  have hk : 0 < h + (k : ℝ) := by positivity
  have hk' : 0 < h + (k : ℝ) + 1 := by positivity
  have he : h ^ 2 / (h + (k : ℝ)) - h ^ 2 / (h + (k : ℝ) + 1) =
      h ^ 2 / ((h + (k : ℝ)) * (h + (k : ℝ) + 1)) := by
    field_simp
    ring
  rw [he]
  exact div_le_div_of_nonneg_left (sq_nonneg h) (by positivity) (by nlinarith)

lemma endpointKernel_tail_sum {h : ℝ} (hh : 0 < h) (n : ℕ) :
    (∑ k ∈ Finset.range n, h ^ 2 / (h + (k : ℝ) + 1) ^ 2) ≤
      h - h ^ 2 / (h + (n : ℝ)) := by
  induction n with
  | zero => simp [hh.ne', pow_two]
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.cast_add_one]
    have hn := endpointKernel_nat_step hh n
    simp only [add_assoc] at *
    linarith

lemma endpointKernel_range_sum {h : ℝ} (hh : 0 < h) (n : ℕ) :
    (∑ k ∈ Finset.range n, h ^ 2 / (h + (k : ℝ)) ^ 2) ≤ 1 + h := by
  cases n with
  | zero => simp; positivity
  | succ n =>
    rw [Finset.sum_range_succ']
    have he : (∑ k ∈ Finset.range n, h ^ 2 / (h + ((k + 1 : ℕ) : ℝ)) ^ 2) =
        ∑ k ∈ Finset.range n, h ^ 2 / (h + (k : ℝ) + 1) ^ 2 := by
      simp only [Nat.cast_add_one, add_assoc]
    rw [he]
    have h0 : h ^ 2 / (h + (0 : ℕ)) ^ 2 = 1 := by simp [hh.ne']
    rw [h0]
    have hn := endpointKernel_tail_sum hh n
    have hpos : 0 ≤ h ^ 2 / (h + (n : ℝ)) := by positivity
    linarith

lemma endpointKernel_finite_nat_sum {h : ℝ} (hh : 0 < h) (s : Finset ℕ) :
    (∑ k ∈ s, h ^ 2 / (h + (k : ℝ)) ^ 2) ≤ 1 + h := by
  have hs : s ⊆ Finset.range (s.sup id + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun _ _ _ => div_nonneg (sq_nonneg h) (sq_nonneg _))).trans
      (endpointKernel_range_sum hh _)

lemma endpointKernel_mono {h d e : ℝ} (hh : 0 < h)
    (hd : 0 ≤ d) (hde : d ≤ |e|) :
    endpointKernel h e ≤ h ^ 2 / (h + d) ^ 2 := by
  unfold endpointKernel
  apply div_le_div_of_nonneg_left (sq_nonneg h) (by positivity)
  nlinarith [abs_nonneg e]

/-- All integer norms to the left of an endpoint can be indexed by their
distinct nonnegative integer distances from a fixed integer below it. -/
lemma endpointKernel_integer_left {h x : ℝ} (hh : 0 < h) (z : ℤ)
    (hz : (z : ℝ) ≤ x) (s : Finset ℤ) (hs : ∀ n ∈ s, n ≤ z) :
    (∑ n ∈ s, endpointKernel h ((n : ℝ) - x)) ≤ 1 + h := by
  let g : ℤ → ℕ := fun n => (z - n).toNat
  have hgc n (hn : n ∈ s) : (g n : ℝ) = (z : ℝ) - (n : ℝ) := by
    dsimp [g]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr (hs n hn)), Int.cast_sub]
  have hinj : Set.InjOn g s := by
    intro a ha b hb he
    have h := congrArg (fun n : ℕ => (n : ℝ)) he
    rw [hgc a ha, hgc b hb] at h
    have hab : (a : ℝ) = (b : ℝ) := by linarith
    exact_mod_cast hab
  calc
    _ ≤ ∑ n ∈ s, h ^ 2 / (h + (g n : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply endpointKernel_mono hh (Nat.cast_nonneg _)
      rw [hgc n hn]
      have hnz : (n : ℝ) ≤ z := by exact_mod_cast hs n hn
      rw [abs_of_nonpos (by linarith : (n : ℝ) - x ≤ 0)]
      linarith
    _ = ∑ k ∈ s.image g, h ^ 2 / (h + (k : ℝ)) ^ 2 := (Finset.sum_image (f := fun k : ℕ => h ^ 2 / (h + (k : ℝ)) ^ 2) hinj).symm
    _ ≤ _ := endpointKernel_finite_nat_sum hh _

lemma endpointKernel_integer_right {h x : ℝ} (hh : 0 < h) (z : ℤ)
    (hz : x ≤ (z : ℝ)) (s : Finset ℤ) (hs : ∀ n ∈ s, z ≤ n) :
    (∑ n ∈ s, endpointKernel h ((n : ℝ) - x)) ≤ 1 + h := by
  let g : ℤ → ℕ := fun n => (n - z).toNat
  have hgc n (hn : n ∈ s) : (g n : ℝ) = (n : ℝ) - (z : ℝ) := by
    dsimp [g]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr (hs n hn)), Int.cast_sub]
  have hinj : Set.InjOn g s := by
    intro a ha b hb he
    have h := congrArg (fun n : ℕ => (n : ℝ)) he
    rw [hgc a ha, hgc b hb] at h
    have hab : (a : ℝ) = (b : ℝ) := by linarith
    exact_mod_cast hab
  calc
    _ ≤ ∑ n ∈ s, h ^ 2 / (h + (g n : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply endpointKernel_mono hh (Nat.cast_nonneg _)
      rw [hgc n hn]
      have hzn : (z : ℝ) ≤ n := by exact_mod_cast hs n hn
      rw [abs_of_nonneg (by linarith : 0 ≤ (n : ℝ) - x)]
      linarith
    _ = ∑ k ∈ s.image g, h ^ 2 / (h + (k : ℝ)) ^ 2 := (Finset.sum_image (f := fun k : ℕ => h ^ 2 / (h + (k : ℝ)) ^ 2) hinj).symm
    _ ≤ _ := endpointKernel_finite_nat_sum hh _

/-- Uniform in the real endpoint, including exact equality with an integer.
This supplies the `O(1+X/T)` integer-norm sum in Fourier truncation. -/
theorem endpointKernel_integer_sum {h : ℝ} (hh : 0 < h) (x : ℝ) (s : Finset ℤ) :
    (∑ n ∈ s, endpointKernel h ((n : ℝ) - x)) ≤ 2 * (1 + h) := by
  have hleft := endpointKernel_integer_left (x := x) hh ⌊x⌋ (Int.floor_le x)
    (s.filter (fun n => n ≤ ⌊x⌋)) (fun n hn => (Finset.mem_filter.mp hn).2)
  have hright := endpointKernel_integer_right (x := x) hh (⌊x⌋ + 1)
    (by have h := Int.lt_floor_add_one x; push_cast; linarith)
    (s.filter (fun n => ¬n ≤ ⌊x⌋)) (fun n hn => by
      have h := (Finset.mem_filter.mp hn).2
      omega)
  have he := Finset.sum_filter_add_sum_filter_not s (fun n => n ≤ ⌊x⌋)
    (fun n => endpointKernel h ((n : ℝ) - x))
  linarith

/-- Summing errors localized near the two endpoints, including endpoints
that are integer norms. The coefficient bound is imposed after collecting
equal norms, as required by the manuscript. -/
theorem weighted_endpoint_error {h C M : ℝ} (hh : 0 < h) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (s : Finset ℤ) (x y : ℝ) (c error : ℤ → ℂ)
    (hc : ∀ n ∈ s, ‖c n‖ ≤ M)
    (he : ∀ n ∈ s, ‖error n‖ ≤ C *
      (endpointKernel h ((n : ℝ) - x) + endpointKernel h ((n : ℝ) - y))) :
    ‖∑ n ∈ s, c n * error n‖ ≤ 4 * C * M * (1 + h) := by
  calc
    _ ≤ ∑ n ∈ s, ‖c n * error n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s, M * (C *
        (endpointKernel h ((n : ℝ) - x) + endpointKernel h ((n : ℝ) - y))) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul (hc n hn) (he n hn) (_root_.norm_nonneg _) hM
    _ = M * C * ((∑ n ∈ s, endpointKernel h ((n : ℝ) - x)) +
        ∑ n ∈ s, endpointKernel h ((n : ℝ) - y)) := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib]
      ring
    _ ≤ M * C * (2 * (1 + h) + 2 * (1 + h)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (endpointKernel_integer_sum hh x s) (endpointKernel_integer_sum hh y s))
        (mul_nonneg hM hC)
    _ = _ := by ring

/-- The summed Fourier boundary error is negligible at the first-moment
scale when the coefficient loss is smaller than the excess truncation
height. This turns a pointwise kernel estimate into the sharp-cutoff
summation error, rather than assuming that error as an input. -/
theorem endpoint_error_isLittleO {ε ρ C : ℝ} (hερ : ε < ρ) (hρ : ρ ≤ 5 / 6)
    (hC : 0 ≤ C) (s : ℝ → Finset ℤ) (c error : ℝ → ℤ → ℂ)
    (hc : ∀ X : ℝ, 1 ≤ X → ∀ n ∈ s X, ‖c X n‖ ≤ X ^ ε)
    (he : ∀ X : ℝ, 1 ≤ X → ∀ n ∈ s X, ‖error X n‖ ≤ C *
      (endpointKernel (X / X ^ (1 / 6 + ρ : ℝ)) ((n : ℝ) - X) +
        endpointKernel (X / X ^ (1 / 6 + ρ : ℝ)) ((n : ℝ) - 2 * X))) :
    (fun X : ℝ => ∑ n ∈ s X, c X n * error X n)
      =o[Filter.atTop] firstMomentScale := by
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => X ^ ε * (1 + X / X ^ (1 / 6 + ρ : ℝ)))
    _ (truncationError_isLittleO hερ hρ)
  apply Asymptotics.IsBigO.of_bound (4 * C)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with X hX
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hh : 0 < X / X ^ (1 / 6 + ρ : ℝ) := by positivity
  have hb := weighted_endpoint_error hh hC (Real.rpow_nonneg hX0.le ε)
    (s X) X (2 * X) (c X) (error X) (hc X hX) (he X hX)
  rw [Real.norm_of_nonneg (by positivity)]
  nlinarith only [hb]

end CubicFirstMoment

end

end OAI
