import Mathlib

namespace OAI

/-!
# Short-period detection for the finite-tree obstruction

Complete-period averaging gives the short-period detection estimate in
`prop:finite-lower`.
-/

open scoped BigOperators

namespace TreeEdit.BinaryLower.FinitePeriod

lemma sum_range_period_mul {f : ℕ → ℝ} {q : ℕ}
    (hperiod : Function.Periodic f q) (n : ℕ) :
    ∑ s ∈ Finset.range (n * q), f s =
      (n : ℝ) * ∑ s ∈ Finset.range q, f s := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have hshift : (∑ s ∈ Finset.range q, f (n * q + s)) =
          ∑ s ∈ Finset.range q, f s := by
        apply Finset.sum_congr rfl
        intro s hs
        simpa [Nat.add_comm] using hperiod.nat_mul n s
      rw [hshift]
      push_cast
      ring

/-- Full periods occupy at least half of any interval of length at least twice
its positive period. No divisibility of `J` by `q` is required. -/
lemma periodic_sum_lower {f : ℕ → ℝ} {q J : ℕ}
    (hq : 0 < q) (hJ : 2 * q ≤ J)
    (hperiod : Function.Periodic f q) (hnonneg : ∀ s, 0 ≤ f s)
    (hcycle : ∑ s ∈ Finset.range q, f s = 2 * (q : ℝ)) :
    (J : ℝ) ≤ ∑ s ∈ Finset.range J, f s := by
  have hqJ : q ≤ J := by omega
  have hdiv : 1 ≤ J / q := Nat.div_pos hqJ hq
  have hfull : q ≤ J / q * q := by
    simpa using Nat.mul_le_mul_right q hdiv
  have hrem : J % q < q := Nat.mod_lt J hq
  have hdecomp := Nat.mod_add_div J q
  rw [Nat.mul_comm q (J / q)] at hdecomp
  have hhalf : J ≤ 2 * (J / q * q) := by omega
  have hsub : J / q * q ≤ J := Nat.div_mul_le_self J q
  calc
    (J : ℝ) ≤ 2 * ((J / q : ℕ) : ℝ) * (q : ℝ) := by
      exact_mod_cast (show J ≤ 2 * (J / q) * q by simpa [Nat.mul_assoc] using hhalf)
    _ = ∑ s ∈ Finset.range (J / q * q), f s := by
      rw [sum_range_period_mul hperiod, hcycle]
      ring
    _ ≤ ∑ s ∈ Finset.range J, f s :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hsub)
        (fun s _ _ => hnonneg s)

lemma norm_one_sub_sq {z : ℂ} (hz : ‖z‖ = 1) :
    ‖1 - z‖ ^ 2 = 2 - 2 * z.re := by
  rw [Complex.sq_norm, Complex.normSq_sub]
  simp [Complex.normSq_eq_norm_sq, hz]
  ring

/-- Complete nontrivial root-of-unity periods have mean squared displacement
exactly two. Primitivity is unnecessary: any positive period works. -/
lemma root_cycle_sum {z : ℂ} {q : ℕ} (hz : ‖z‖ = 1)
    (hne : z ≠ 1) (hroot : z ^ q = 1) :
    ∑ s ∈ Finset.range q, ‖1 - z ^ (s + 1)‖ ^ 2 = 2 * (q : ℝ) := by
  have hgeom : (∑ s ∈ Finset.range q, z ^ s) = 0 := by
    rw [geom_sum_eq hne, hroot]
    simp
  have hgeom' : (∑ s ∈ Finset.range q, z ^ (s + 1)) = 0 := by
    simp_rw [pow_succ]
    rw [← Finset.sum_mul, hgeom, zero_mul]
  have hre : (∑ s ∈ Finset.range q, (z ^ (s + 1)).re) = 0 := by
    simpa using congrArg Complex.re hgeom'
  simp_rw [norm_one_sub_sq (by simp [norm_pow, hz] : ‖z ^ (_ + 1)‖ = 1)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hre]
  simp
  ring

/-- Short-period detection used at every sparse active internal node. -/
theorem root_short_average {z : ℂ} {q J : ℕ}
    (hq : 0 < q) (hJ : 2 * q ≤ J) (hz : ‖z‖ = 1)
    (hne : z ≠ 1) (hroot : z ^ q = 1) :
    1 ≤ (∑ s ∈ Finset.range J, ‖1 - z ^ (s + 1)‖ ^ 2) / (J : ℝ) := by
  have hperiod : Function.Periodic (fun s : ℕ => ‖1 - z ^ (s + 1)‖ ^ 2) q := by
    intro s
    have he : s + q + 1 = (s + 1) + q := by omega
    dsimp
    rw [he, pow_add, hroot, mul_one]
  have hsum := periodic_sum_lower hq hJ hperiod
    (fun s => sq_nonneg _) (root_cycle_sum hz hne hroot)
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  exact (le_div_iff₀ hJpos).2 (by simpa using hsum)

/-- A character specialization in exactly the source's cheap-shift notation.
Only a period of the character value is required; it need not be a period of
`u` itself. Activity after multiplying by `R` guarantees nontriviality. -/
theorem character_short_average {A : Type*} [AddCommGroup A] [Finite A]
    (χ : AddChar A ℂ) (u : A) {q J R : ℕ}
    (hq : 0 < q) (hJ : 2 * q ≤ J)
    (hactive : χ (R • u) ≠ 1) (hperiod : χ (q • u) = 1) :
    1 ≤ (∑ s ∈ Finset.range J, ‖1 - χ ((s + 1) • u)‖ ^ 2) / (J : ℝ) := by
  have hne : χ u ≠ 1 := by
    intro h
    apply hactive
    simp [χ.map_nsmul_eq_pow, h]
  have hroot : χ u ^ q = 1 := by
    simpa only [χ.map_nsmul_eq_pow] using hperiod
  simpa only [χ.map_nsmul_eq_pow] using
    root_short_average hq hJ (χ.norm_apply u) hne hroot

end TreeEdit.BinaryLower.FinitePeriod

end OAI
