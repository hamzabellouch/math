import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.VaughanBilinear

/-- The exact correlation expansion of a weighted finite bilinear energy.
No distinctness or unit-modulus assumption on the phase is needed. -/
theorem energy_identity {α β : Type*} (s : Finset α) (t : Finset β)
    (b : β → ℂ) (z : α → β → ℂ) :
    ((∑ m ∈ s, ‖∑ n ∈ t, b n * z m n‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ t, ∑ k ∈ t, b n * (starRingEnd ℂ) (b k) *
        ∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k) := by
  classical
  have hpoint (m : α) :
      (‖∑ n ∈ t, b n * z m n‖ ^ 2 : ℂ) =
        ∑ n ∈ t, ∑ k ∈ t,
          b n * (starRingEnd ℂ) (b k) *
            (z m n * (starRingEnd ℂ) (z m k)) := by
    rw [← Complex.mul_conj']
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro k hk
    ring
  push_cast
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]

/-- Bounding a bilinear energy by absolute correlations retains the
arithmetic cancellation in the first variable. -/
theorem energy_le_correlations {α β : Type*} (s : Finset α) (t : Finset β)
    (b : β → ℂ) (z : α → β → ℂ) :
    (∑ m ∈ s, ‖∑ n ∈ t, b n * z m n‖ ^ 2) ≤
      ∑ n ∈ t, ∑ k ∈ t, ‖b n‖ * ‖b k‖ *
        ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ := by
  have h := congrArg Complex.re (energy_identity s t b z)
  simp only [Complex.ofReal_re, Complex.re_sum] at h
  rw [h]
  apply Finset.sum_le_sum
  intro n hn
  apply Finset.sum_le_sum
  intro k hk
  calc
    _ ≤ ‖b n * (starRingEnd ℂ) (b k) *
        ∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ := Complex.re_le_norm _
    _ = _ := by simp only [norm_mul, Complex.norm_conj]

/-- Finite Type-II Cauchy--Schwarz, with the full correlation sum explicit.
This is an unconditional algebraic bound, not a minor-arc hypothesis. -/
theorem norm_bilinear_sq_le {α β : Type*} (s : Finset α) (t : Finset β)
    (a : α → ℂ) (b : β → ℂ) (z : α → β → ℂ) :
    ‖∑ m ∈ s, a m * ∑ n ∈ t, b n * z m n‖ ^ 2 ≤
      (∑ m ∈ s, ‖a m‖ ^ 2) *
        (∑ n ∈ t, ∑ k ∈ t, ‖b n‖ * ‖b k‖ *
          ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) := by
  calc
    _ ≤ (∑ m ∈ s, ‖a m‖ * ‖∑ n ∈ t, b n * z m n‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [norm_mul] using
        norm_sum_le s (fun m => a m * ∑ n ∈ t, b n * z m n)
    _ ≤ (∑ m ∈ s, ‖a m‖ ^ 2) *
        ∑ m ∈ s, ‖∑ n ∈ t, b n * z m n‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (energy_le_correlations s t b z)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- For unit phases the diagonal correlation is exactly the number of rows. -/
theorem diagonal_correlation {α β : Type*} (s : Finset α)
    (z : α → β → ℂ) (n : β) (hz : ∀ m ∈ s, ‖z m n‖ = 1) :
    ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m n)‖ = (s.card : ℝ) := by
  have h : (∑ m ∈ s, z m n * (starRingEnd ℂ) (z m n)) = (s.card : ℂ) := by
    calc
      _ = ∑ m ∈ s, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Complex.mul_conj', hz m hm]
        norm_num
      _ = _ := by simp
  rw [h, Complex.norm_natCast]

/-- Exact diagonal/off-diagonal separation; erased indices do not count a
diagonal pair twice, including when either indexing set is empty. -/
theorem correlation_sum_split {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (z : α → β → ℂ)
    (hz : ∀ m ∈ s, ∀ n ∈ t, ‖z m n‖ = 1) :
    (∑ n ∈ t, ∑ k ∈ t, ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) =
      (s.card : ℝ) * t.card +
        ∑ n ∈ t, ∑ k ∈ t.erase n,
          ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ := by
  have hpoint (n : β) (hn : n ∈ t) :
      (∑ k ∈ t, ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) =
        (s.card : ℝ) + ∑ k ∈ t.erase n,
          ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ := by
    rw [← Finset.sum_erase_add (s := t)
      (fun k => ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) hn,
      diagonal_correlation s z n (fun m hm => hz m hm n hn)]
    ring
  calc
    _ = ∑ n ∈ t, ((s.card : ℝ) + ∑ k ∈ t.erase n,
          ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) :=
      Finset.sum_congr rfl hpoint
    _ = _ := by rw [Finset.sum_add_distrib]; simp [mul_comm]

/-- Bounded coefficient version of Type-II Cauchy--Schwarz. The diagonal
is evaluated exactly; only genuine off-diagonal correlations remain. -/
theorem norm_bilinear_sq_le_offDiagonal {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (a : α → ℂ) (b : β → ℂ)
    (z : α → β → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ n ∈ t, ‖b n‖ ≤ B)
    (hz : ∀ m ∈ s, ∀ n ∈ t, ‖z m n‖ = 1) :
    ‖∑ m ∈ s, a m * ∑ n ∈ t, b n * z m n‖ ^ 2 ≤
      (∑ m ∈ s, ‖a m‖ ^ 2) * B ^ 2 *
        ((s.card : ℝ) * t.card + ∑ n ∈ t, ∑ k ∈ t.erase n,
          ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) := by
  have hbound :
      (∑ n ∈ t, ∑ k ∈ t, ‖b n‖ * ‖b k‖ *
        ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) ≤
      B ^ 2 * ∑ n ∈ t, ∑ k ∈ t,
        ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro k hk
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [pow_two] using mul_le_mul (hb n hn) (hb k hk) (norm_nonneg _) hB
  calc
    _ ≤ _ := norm_bilinear_sq_le s t a b z
    _ ≤ (∑ m ∈ s, ‖a m‖ ^ 2) *
        (B ^ 2 * ∑ n ∈ t, ∑ k ∈ t,
          ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) :=
      mul_le_mul_of_nonneg_left hbound (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by rw [correlation_sum_split s t z hz]; ring

/-- The standard real additive phase, with the `2π` convention. -/
def phase (x : ℝ) : ℂ := Real.fourierChar x

@[simp] theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Circle.norm_coe _

theorem phase_mul_conj (x y : ℝ) :
    phase x * (starRingEnd ℂ) (phase y) = phase (x - y) := by
  unfold phase
  rw [Circle.starRingEnd_addChar, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 2

theorem phase_nat_mul (x : ℝ) (n : ℕ) : phase (x * n) = phase x ^ n := by
  unfold phase
  rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, Circle.coe_pow]

/-- An exact geometric cancellation bound in a form valid even at resonance. -/
theorem phase_sum_mul_bound (x : ℝ) (M : ℕ) :
    ‖∑ m ∈ Finset.range M, phase (x * m)‖ * ‖1 - phase x‖ ≤ 2 := by
  simp_rw [phase_nat_mul]
  rw [← norm_mul, geom_sum_mul_neg]
  calc
    ‖1 - phase x ^ M‖ ≤ ‖(1 : ℂ)‖ + ‖phase x ^ M‖ := norm_sub_le _ _
    _ = 2 := by simp; norm_num

/-- The usual geometric sum bound away from resonance. -/
theorem phase_sum_le_min (x : ℝ) (M : ℕ) (hx : phase x ≠ 1) :
    ‖∑ m ∈ Finset.range M, phase (x * m)‖ ≤
      min (M : ℝ) (2 / ‖1 - phase x‖) := by
  apply le_min
  · calc
      _ ≤ ∑ m ∈ Finset.range M, ‖phase (x * m)‖ := norm_sum_le _ _
      _ = M := by simp
  · have hpos : 0 < ‖1 - phase x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx.symm)
    exact (le_div_iff₀ hpos).mpr (phase_sum_mul_bound x M)

/-- A total geometric majorant. Resonant frequencies use the trivial bound;
the definition never interprets division by zero as cancellation. -/
def geometricBound (M : ℕ) (x : ℝ) : ℝ :=
  if phase x = 1 then M else min (M : ℝ) (2 / ‖1 - phase x‖)

theorem phase_sum_le_geometricBound (x : ℝ) (M : ℕ) :
    ‖∑ m ∈ Finset.range M, phase (x * m)‖ ≤ geometricBound M x := by
  unfold geometricBound
  split_ifs with hx
  · simp_rw [phase_nat_mul, hx]
    simp
  · exact phase_sum_le_min x M hx

/-- The finite Type-II estimate specialized to a real bilinear phase. All
remaining terms are explicit one-dimensional geometric sums, bounded without
any Diophantine approximation assumption. -/
theorem real_phase_bilinear_sq_le (M : ℕ) (t : Finset ℕ)
    (a b : ℕ → ℂ) (θ B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ n ∈ t, ‖b n‖ ≤ B) :
    ‖∑ m ∈ Finset.range M, a m * ∑ n ∈ t, b n * phase (θ * m * n)‖ ^ 2 ≤
      (∑ m ∈ Finset.range M, ‖a m‖ ^ 2) * B ^ 2 *
        ((M : ℝ) * t.card + ∑ n ∈ t, ∑ k ∈ t.erase n,
          geometricBound M (θ * ((n : ℝ) - k))) := by
  have hbase := norm_bilinear_sq_le_offDiagonal (Finset.range M) t a b
    (fun m n => phase (θ * m * n)) B hB hb
    (fun m hm n hn => norm_phase _)
  simp only [Finset.card_range] at hbase
  refine hbase.trans ?_
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg B))
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro n hn
  apply Finset.sum_le_sum
  intro k hk
  have hcorr : (∑ m ∈ Finset.range M,
      phase (θ * m * n) * (starRingEnd ℂ) (phase (θ * m * k))) =
      ∑ m ∈ Finset.range M, phase ((θ * ((n : ℝ) - k)) * m) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [phase_mul_conj]
    congr 1
    ring
  rw [hcorr]
  exact phase_sum_le_geometricBound _ M

/-- A finite real Schur bound, proved by symmetrizing `2xy ≤ x²+y²`.
The coefficients need not be nonnegative. -/
theorem symmetric_weighted_sum_le {β : Type*} (t : Finset β)
    (f : β → ℝ) (K : β → β → ℝ)
    (hK : ∀ n ∈ t, ∀ k ∈ t, 0 ≤ K n k)
    (hsym : ∀ n ∈ t, ∀ k ∈ t, K n k = K k n) :
    (∑ n ∈ t, ∑ k ∈ t, f n * f k * K n k) ≤
      ∑ n ∈ t, f n ^ 2 * ∑ k ∈ t, K n k := by
  have hfirst : (∑ n ∈ t, ∑ k ∈ t, f n ^ 2 * K n k) =
      ∑ n ∈ t, f n ^ 2 * ∑ k ∈ t, K n k := by
    simp only [Finset.mul_sum]
  have hsecond : (∑ n ∈ t, ∑ k ∈ t, f k ^ 2 * K n k) =
      ∑ n ∈ t, f n ^ 2 * ∑ k ∈ t, K n k := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsym k hk n hn]
  calc
    _ ≤ ∑ n ∈ t, ∑ k ∈ t,
        (f n ^ 2 * K n k + f k ^ 2 * K n k) / 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro k hk
      nlinarith [mul_nonneg (sq_nonneg (f n - f k)) (hK n hn k hk)]
    _ = ((∑ n ∈ t, ∑ k ∈ t, f n ^ 2 * K n k) +
        (∑ n ∈ t, ∑ k ∈ t, f k ^ 2 * K n k)) / 2 := by
      simp only [add_div, Finset.sum_div, Finset.sum_add_distrib]
    _ = _ := by rw [hfirst, hsecond]; ring

/-- Reversing a correlation conjugates it, hence preserves its norm. -/
theorem correlation_norm_symm {α β : Type*} (s : Finset α)
    (z : α → β → ℂ) (n k : β) :
    ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ =
      ‖∑ m ∈ s, z m k * (starRingEnd ℂ) (z m n)‖ := by
  have hc : (∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)) =
      (starRingEnd ℂ) (∑ m ∈ s, z m k * (starRingEnd ℂ) (z m n)) := by
    simp only [map_sum, map_mul, starRingEnd_self_apply]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [hc, Complex.norm_conj]

/-- Type-II energy bound using an absolute correlation row bound. Unlike the
bounded-coefficient version, this retains both coefficient squared sums and
therefore applies directly to divisor-coefficient second-moment estimates. -/
theorem norm_bilinear_sq_le_energy {α β : Type*} (s : Finset α) (t : Finset β)
    (a : α → ℂ) (b : β → ℂ) (z : α → β → ℂ) (C : ℝ)
    (hrow : ∀ n ∈ t,
      (∑ k ∈ t, ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) ≤ C) :
    ‖∑ m ∈ s, a m * ∑ n ∈ t, b n * z m n‖ ^ 2 ≤
      (∑ m ∈ s, ‖a m‖ ^ 2) * C * (∑ n ∈ t, ‖b n‖ ^ 2) := by
  have hweight := symmetric_weighted_sum_le t (fun n => ‖b n‖)
    (fun n k => ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖)
    (fun _ _ _ _ => norm_nonneg _)
    (fun n _ k _ => correlation_norm_symm s z n k)
  have hbound :
      (∑ n ∈ t, ∑ k ∈ t, ‖b n‖ * ‖b k‖ *
        ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) ≤
      C * ∑ n ∈ t, ‖b n‖ ^ 2 := by
    refine hweight.trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow n hn) (sq_nonneg ‖b n‖)
  calc
    _ ≤ _ := norm_bilinear_sq_le s t a b z
    _ ≤ (∑ m ∈ s, ‖a m‖ ^ 2) * (C * ∑ n ∈ t, ‖b n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hbound (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by ring

end Problem337.VaughanBilinear

end

end OAI
