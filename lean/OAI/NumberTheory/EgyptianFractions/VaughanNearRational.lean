import OAI.NumberTheory.EgyptianFractions.VaughanBilinear
import OAI.NumberTheory.EgyptianFractions.GeometricCharacterBound
import OAI.NumberTheory.EgyptianFractions.RationalPhaseSpacing

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.VaughanBilinear

theorem phase_int (n : ℤ) : phase n = 1 := by
  rw [phase, Real.fourierChar_apply]
  have he : (↑(2 * Real.pi * (n : ℝ)) : ℂ) * Complex.I =
      (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_int_mul_two_pi_mul_I]

theorem phase_fract (x : ℝ) : phase (Int.fract x) = phase x := by
  rw [Int.fract, ← phase_mul_conj, phase_int]
  simp

theorem phase_eq_geometric_phase (x : ℝ) :
    phase x = Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) := by
  rw [phase, Real.fourierChar_apply]
  congr 1
  ring

/-- The usual truncated reciprocal-distance majorant for a real geometric
sum. Integer phases use the length cap, never a spurious zero reciprocal. -/
theorem phase_sum_le_truncatedInv (x : ℝ) (M : ℕ) :
    ‖∑ m ∈ Finset.range M, phase (x * m)‖ ≤
      RationalPhaseSpacing.truncatedInv M (RationalPhaseSpacing.intDistance x) := by
  have hcap : ‖∑ m ∈ Finset.range M, phase (x * m)‖ ≤ (M : ℝ) := by
    calc
      _ ≤ ∑ m ∈ Finset.range M, ‖phase (x * m)‖ := norm_sum_le _ _
      _ = _ := by simp
  by_cases hx : RationalPhaseSpacing.intDistance x = 0
  · simpa only [RationalPhaseSpacing.truncatedInv, ite_eq_left hx] using hcap
  have hpos : 0 < RationalPhaseSpacing.intDistance x :=
    lt_of_le_of_ne (RationalPhaseSpacing.intDistance_nonneg x) (Ne.symm hx)
  rw [RationalPhaseSpacing.truncatedInv, ite_eq_right hx]
  refine le_min hcap ?_
  have hlow : RationalPhaseSpacing.intDistance x ≤ Int.fract x := min_le_left _ _
  have hhigh : Int.fract x ≤ 1 - RationalPhaseSpacing.intDistance x := by
    have h := min_le_right (Int.fract x) (1 - Int.fract x)
    change RationalPhaseSpacing.intDistance x ≤ 1 - Int.fract x at h
    linarith
  have hgeom := norm_geometric_phase_sum_le_middle hpos hlow hhigh M
  have heq : (∑ m ∈ Finset.range M, phase (x * m)) =
      ∑ m ∈ Finset.range M,
        Complex.exp (Complex.I * (2 * Real.pi * Int.fract x : ℝ)) ^ m := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [phase_nat_mul, ← phase_fract x, phase_eq_geometric_phase]
  rw [heq]
  exact hgeom.trans (one_div_le_one_div_of_le hpos (by linarith))

/-- Rational approximation provides an actual Type-II correlation row bound
on every short block of integer columns, uniformly in the chosen row. -/
theorem near_rational_correlation_row_le
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (M : ℕ) (t : Finset ℤ)
    (hspan : ∀ n ∈ t, ∀ k ∈ t, 2 * |n - k| ≤ (q : ℤ)) (n : ℤ) :
    (∑ k ∈ t, ‖∑ m ∈ Finset.range M,
      phase (θ * m * n) * (starRingEnd ℂ) (phase (θ * m * k))‖) ≤
      2 * (M : ℝ) + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))) := by
  classical
  let A := t.image (fun k => n - k)
  have hA : ∀ j ∈ A, ∀ l ∈ A, 2 * |j - l| ≤ (q : ℤ) := by
    intro j hj l hl
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
    have heq : (n - k) - (n - i) = i - k := by omega
    rw [heq]
    exact hspan i hi k hk
  have hsum := RationalPhaseSpacing.sum_truncatedInv_intDistance_le
    θ a q hq hcop happrox A hA (M : ℝ) (Nat.cast_nonneg M)
  have hcorr (k : ℤ) : (∑ m ∈ Finset.range M,
      phase (θ * m * n) * (starRingEnd ℂ) (phase (θ * m * k))) =
      ∑ m ∈ Finset.range M, phase ((θ * ((n - k : ℤ) : ℝ)) * m) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [phase_mul_conj]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ∑ k ∈ t, RationalPhaseSpacing.truncatedInv M
        (RationalPhaseSpacing.intDistance (θ * ((n - k : ℤ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [hcorr]
      exact phase_sum_le_truncatedInv _ M
    _ = ∑ j ∈ A, RationalPhaseSpacing.truncatedInv M
        (RationalPhaseSpacing.intDistance (θ * j)) := by
      rw [Finset.sum_image]
      intro k hk i hi heq
      dsimp at heq
      omega
    _ ≤ _ := hsum

/-- A proved near-rational Type-II estimate with both coefficient energies.
The only number-theoretic hypothesis is the stated reduced approximation;
all correlation/spacing/cancellation estimates are discharged. -/
theorem near_rational_bilinear_sq_le
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (M : ℕ) (t : Finset ℤ)
    (hspan : ∀ n ∈ t, ∀ k ∈ t, 2 * |n - k| ≤ (q : ℤ))
    (c : ℕ → ℂ) (b : ℤ → ℂ) :
    ‖∑ m ∈ Finset.range M, c m * ∑ n ∈ t, b n * phase (θ * m * n)‖ ^ 2 ≤
      (∑ m ∈ Finset.range M, ‖c m‖ ^ 2) *
        (2 * (M : ℝ) + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))) *
          (∑ n ∈ t, ‖b n‖ ^ 2) := by
  apply norm_bilinear_sq_le_energy
  intro n hn
  exact near_rational_correlation_row_le θ a q hq hcop happrox M t hspan n

/-- Actual near-rational row cancellation on an arbitrary integer interval,
also valid for any subset of that interval. -/
theorem near_rational_interval_correlation_row_le
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (M : ℕ) (t : Finset ℤ) (L : ℤ) (N : ℕ)
    (ht : t ⊆ Finset.Ico L (L + N)) (n : ℤ) :
    (∑ k ∈ t, ‖∑ m ∈ Finset.range M,
      phase (θ * m * n) * (starRingEnd ℂ) (phase (θ * m * k))‖) ≤
      (2 * (N : ℝ) / q + 1) *
        (2 * (M : ℝ) + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))) := by
  classical
  let A := t.image (fun k => n - k)
  let L' : ℤ := n - L - N + 1
  have hA : A ⊆ Finset.Ico L' (L' + N) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    have hk' := Finset.mem_Ico.mp (ht hk)
    apply Finset.mem_Ico.mpr
    dsimp [L']
    omega
  calc
    _ ≤ ∑ k ∈ t, RationalPhaseSpacing.truncatedInv M
        (RationalPhaseSpacing.intDistance (θ * ((n - k : ℤ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      have heq : (∑ m ∈ Finset.range M,
          phase (θ * m * n) * (starRingEnd ℂ) (phase (θ * m * k))) =
          ∑ m ∈ Finset.range M, phase ((θ * ((n - k : ℤ) : ℝ)) * m) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [phase_mul_conj]
        congr 1
        push_cast
        ring
      rw [heq]
      exact phase_sum_le_truncatedInv _ M
    _ = ∑ j ∈ A, RationalPhaseSpacing.truncatedInv M
        (RationalPhaseSpacing.intDistance (θ * j)) := by
      rw [Finset.sum_image]
      intro k hk i hi heq
      dsimp at heq
      omega
    _ ≤ ∑ j ∈ Finset.Ico L' (L' + N), RationalPhaseSpacing.truncatedInv M
        (RationalPhaseSpacing.intDistance (θ * j)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hA (fun _ _ _ =>
        RationalPhaseSpacing.truncatedInv_nonneg (Nat.cast_nonneg M)
          (RationalPhaseSpacing.intDistance_nonneg _))
    _ ≤ _ := RationalPhaseSpacing.sum_truncatedInv_intDistance_interval_le
      θ a q hq hcop happrox L' N M (Nat.cast_nonneg M)

/-- Full rectangular Type-II estimate from a reduced rational approximation.
No spacing, correlation, or equidistribution estimate remains as a premise. -/
theorem near_rational_interval_bilinear_sq_le
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (M : ℕ) (t : Finset ℤ) (L : ℤ) (N : ℕ)
    (ht : t ⊆ Finset.Ico L (L + N)) (c : ℕ → ℂ) (b : ℤ → ℂ) :
    ‖∑ m ∈ Finset.range M, c m * ∑ n ∈ t, b n * phase (θ * m * n)‖ ^ 2 ≤
      (∑ m ∈ Finset.range M, ‖c m‖ ^ 2) *
        ((2 * (N : ℝ) / q + 1) *
          (2 * (M : ℝ) + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))))) *
            (∑ n ∈ t, ‖b n‖ ^ 2) := by
  apply norm_bilinear_sq_le_energy
  intro n hn
  exact near_rational_interval_correlation_row_le θ a q hq hcop happrox M t L N ht n

/-- The explicit geometric majorant itself is bounded by the truncated
reciprocal distance. This also allows variable inner interval lengths. -/
theorem geometricBound_le_truncatedInv (M : ℕ) (x : ℝ) :
    geometricBound M x ≤
      RationalPhaseSpacing.truncatedInv M (RationalPhaseSpacing.intDistance x) := by
  by_cases hd : RationalPhaseSpacing.intDistance x = 0
  · rw [RationalPhaseSpacing.truncatedInv, ite_eq_left hd]
    unfold geometricBound
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hdpos : 0 < RationalPhaseSpacing.intDistance x :=
    lt_of_le_of_ne (RationalPhaseSpacing.intDistance_nonneg x) (Ne.symm hd)
  have hlow : RationalPhaseSpacing.intDistance x ≤ Int.fract x := min_le_left _ _
  have hhigh : Int.fract x ≤ 1 - RationalPhaseSpacing.intDistance x := by
    have h := min_le_right (Int.fract x) (1 - Int.fract x)
    change RationalPhaseSpacing.intDistance x ≤ 1 - Int.fract x at h
    linarith
  have hs := sin_pi_mul_lower_on_middle hdpos hlow hhigh
  have hchord : 2 * RationalPhaseSpacing.intDistance x ≤ ‖1 - phase x‖ := by
    rw [norm_sub_rev, ← phase_fract x, phase_eq_geometric_phase, norm_exp_phase_sub_one]
    have habs := le_abs_self (Real.sin (Real.pi * Int.fract x))
    nlinarith
  have hnorm : 0 < ‖1 - phase x‖ := by linarith
  have hx : phase x ≠ 1 := by
    intro hx
    simp [hx] at hnorm
  rw [geometricBound, ite_eq_right hx, RationalPhaseSpacing.truncatedInv, ite_eq_right hd]
  apply min_le_min_left
  apply (div_le_div_iff₀ hnorm hdpos).mpr
  simpa using hchord

/-- A uniform harmonic row bound for indexed integer frequencies. The map
into the interval must be injective, but need not exhaust the interval. -/
theorem sum_geometricBound_difference_le {β : Type*}
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (M : ℕ) (t : Finset β) (f : β → ℤ) (L : ℤ) (N : ℕ)
    (hf : ∀ k ∈ t, f k ∈ Finset.Ico L (L + N))
    (hinj : Set.InjOn f t) (n : ℤ) :
    (∑ k ∈ t, geometricBound M (θ * ((n - f k : ℤ) : ℝ))) ≤
      (2 * (N : ℝ) / q + 1) *
        (2 * (M : ℝ) + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))) := by
  classical
  let A := t.image (fun k => n - f k)
  let L' : ℤ := n - L - N + 1
  have hA : A ⊆ Finset.Ico L' (L' + N) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    have hk' := Finset.mem_Ico.mp (hf k hk)
    apply Finset.mem_Ico.mpr
    dsimp [L']
    omega
  calc
    _ ≤ ∑ k ∈ t, RationalPhaseSpacing.truncatedInv M
        (RationalPhaseSpacing.intDistance (θ * ((n - f k : ℤ) : ℝ))) :=
      Finset.sum_le_sum (fun k _ => geometricBound_le_truncatedInv M _)
    _ = ∑ j ∈ A, RationalPhaseSpacing.truncatedInv M
        (RationalPhaseSpacing.intDistance (θ * j)) := by
      rw [Finset.sum_image]
      intro k hk i hi heq
      apply hinj hk hi
      dsimp at heq
      omega
    _ ≤ ∑ j ∈ Finset.Ico L' (L' + N), RationalPhaseSpacing.truncatedInv M
        (RationalPhaseSpacing.intDistance (θ * j)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hA (fun _ _ _ =>
        RationalPhaseSpacing.truncatedInv_nonneg (Nat.cast_nonneg M)
          (RationalPhaseSpacing.intDistance_nonneg _))
    _ ≤ _ := RationalPhaseSpacing.sum_truncatedInv_intDistance_interval_le
      θ a q hq hcop happrox L' N M (Nat.cast_nonneg M)

end Problem337.VaughanBilinear

end

end OAI
