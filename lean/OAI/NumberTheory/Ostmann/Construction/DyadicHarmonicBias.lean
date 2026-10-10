import OAI.NumberTheory.Ostmann.QuadraticCenter.ClosedQuadraticBand

namespace OAI

/-! # Transferring quadratic smallness to harmonic prime intervals -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

noncomputable def harmonicQuadraticBias (A : Set ℕ) (N p : ℕ) : ℝ :=
  maximalQuadraticBias (tailSupport A N p) p / p

noncomputable def iteratedLogPrimeBand (α β L : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊Real.exp (Real.exp (β * L))⌋₊).filter
    (fun p => Real.exp (α * L) ≤ Real.log (p : ℝ))

noncomputable def harmonicQuadraticBandMass (A : Set ℕ) (N : ℕ) (α β L : ℝ) : ℝ :=
  ∑ p ∈ iteratedLogPrimeBand α β L, harmonicQuadraticBias A N p

theorem harmonicQuadraticBias_nonneg (A : Set ℕ) (N p : ℕ) :
    0 ≤ harmonicQuadraticBias A N p := div_nonneg (maximalQuadraticBias_nonneg _ _) (Nat.cast_nonneg _)

theorem harmonicQuadratic_closedBand_le (A : Set ℕ) (N : ℕ) (T ε : ℝ)
    (hT : 0 < T) (hbound : closedQuadraticBandMass A N T ≤ ε * T) :
    (∑ p ∈ closedLogPrimeBand T, harmonicQuadraticBias A N p) ≤ ε := by
  have hterm (p : ℕ) (hp : p ∈ closedLogPrimeBand T) :
      harmonicQuadraticBias A N p ≤
        ((Real.log (p : ℝ) / p) * maximalQuadraticBias (tailSupport A N p) p) / T := by
    apply (le_div_iff₀ hT).mpr
    have hh := (mem_closedLogPrimeBand_iff T p).mp hp
    have hb := mul_le_mul_of_nonneg_right hh.2.1
      (harmonicQuadraticBias_nonneg A N p)
    dsimp [harmonicQuadraticBias] at *
    convert hb using 1 <;> ring
  calc
    _ ≤ ∑ p ∈ closedLogPrimeBand T,
        ((Real.log (p : ℝ) / p) * maximalQuadraticBias (tailSupport A N p) p) / T :=
      Finset.sum_le_sum hterm
    _ = closedQuadraticBandMass A N T / T := by rw [← Finset.sum_div]; rfl
    _ ≤ (ε * T) / T := div_le_div_of_nonneg_right hbound hT.le
    _ = ε := mul_div_cancel_right₀ ε hT.ne'

/-- Closed dyadic intervals cover the specified finite logarithmic range. -/
theorem exists_dyadic_cover (X u : ℝ) (n : ℕ) (hX : 0 < X) (hlo : X ≤ u)
    (hhi : u ≤ (2 : ℝ) ^ n * X) :
    ∃ j ≤ n, (2 : ℝ) ^ j * X ≤ u ∧ u ≤ 2 * ((2 : ℝ) ^ j * X) := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, by simpa using hlo, ?_⟩
    simp only [pow_zero, one_mul] at hhi ⊢
    linarith
  | succ n ih =>
    by_cases hh : u ≤ (2 : ℝ) ^ n * X
    · obtain ⟨j, hj, hju, huj⟩ := ih hh
      exact ⟨j, Nat.le_succ_of_le hj, hju, huj⟩
    · refine ⟨n, Nat.le_succ n, (not_le.mp hh).le, ?_⟩
      simpa only [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hhi

theorem harmonicQuadraticBandMass_dyadic_bound (A : Set ℕ) (N n : ℕ)
    (α β L ε : ℝ) (hcover : Real.exp (β * L) ≤ (2 : ℝ) ^ n * Real.exp (α * L))
    (hlocal : ∀ j ≤ n,
      closedQuadraticBandMass A N ((2 : ℝ) ^ j * Real.exp (α * L)) ≤
        ε * ((2 : ℝ) ^ j * Real.exp (α * L))) :
    harmonicQuadraticBandMass A N α β L ≤ ((n : ℝ) + 1) * ε := by
  let H := iteratedLogPrimeBand α β L
  let P := fun j : ℕ => closedLogPrimeBand ((2 : ℝ) ^ j * Real.exp (α * L))
  have hsub (p : ℕ) (hp : p ∈ H) : ∃ j ∈ Finset.range (n + 1), p ∈ P j := by
    obtain ⟨hpprime, hplo⟩ := Finset.mem_filter.mp hp
    have hprime := Nat.prime_of_mem_primesLE hpprime
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpu : Real.log (p : ℝ) ≤ Real.exp (β * L) :=
      (Real.log_le_iff_le_exp hp0).mpr
        ((by exact_mod_cast Nat.le_of_mem_primesLE hpprime :
          (p : ℝ) ≤ ⌊Real.exp (Real.exp (β * L))⌋₊).trans (Nat.floor_le (Real.exp_nonneg _)))
    obtain ⟨j, hj, hjlo, hjhi⟩ := exists_dyadic_cover (Real.exp (α * L)) (Real.log (p : ℝ)) n
      (Real.exp_pos _) hplo (hpu.trans hcover)
    exact ⟨j, Finset.mem_range.mpr (by omega),
      (mem_closedLogPrimeBand_iff _ p).mpr ⟨hprime, hjlo, hjhi⟩⟩
  have hterm (p : ℕ) (hp : p ∈ H) : harmonicQuadraticBias A N p ≤
      ∑ j ∈ Finset.range (n + 1), if p ∈ P j then harmonicQuadraticBias A N p else 0 := by
    obtain ⟨j, hj, hpj⟩ := hsub p hp
    have hh := Finset.single_le_sum (s := Finset.range (n + 1))
      (f := fun j => if p ∈ P j then harmonicQuadraticBias A N p else 0)
      (fun i _ => by split <;> simp [harmonicQuadraticBias_nonneg]) hj
    simpa only [ite_eq_left hpj] using hh
  calc
    _ ≤ ∑ p ∈ H, ∑ j ∈ Finset.range (n + 1),
        if p ∈ P j then harmonicQuadraticBias A N p else 0 := Finset.sum_le_sum hterm
    _ = ∑ j ∈ Finset.range (n + 1), ∑ p ∈ H,
        if p ∈ P j then harmonicQuadraticBias A N p else 0 := Finset.sum_comm
    _ ≤ ∑ _j ∈ Finset.range (n + 1), ε := by
      apply Finset.sum_le_sum
      intro j hj
      have hsplit : (∑ p ∈ H, if p ∈ P j then harmonicQuadraticBias A N p else 0) =
          ∑ p ∈ H.filter (fun p => p ∈ P j), harmonicQuadraticBias A N p := by rw [Finset.sum_filter]
      rw [hsplit]
      apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (fun p hp => (Finset.mem_filter.mp hp).2)
        (fun p _ _ => harmonicQuadraticBias_nonneg A N p))
      exact harmonicQuadratic_closedBand_le A N _ ε (by positivity) (hlocal j (by simpa using hj))
    _ = _ := by simp

end Ostmann

end OAI
