import OAI.NumberTheory.EgyptianFractions.ReciprocalPhasePreparation
import OAI.NumberTheory.EgyptianFractions.ReciprocalPhaseRegularity
import OAI.NumberTheory.EgyptianFractions.SecondDerivativeTest
import OAI.NumberTheory.EgyptianFractions.CorrelationPhase

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Absorb the square-root expression in the second derivative test. -/
theorem reciprocal_terminal_sqrt_budget {U a lam T : ℝ} (hU : 1 ≤ U)
    (ha : 0 < a) (hT : T ≤ 3 * U)
    (hlower : a * U ^ (-(3 : ℝ) / 2) ≤ lam)
    (hupper : lam ≤ a * U ^ (-(2 : ℝ) / 5)) :
    T * Real.sqrt lam + 1 / Real.sqrt lam ≤
      3 * (a ^ ((1 : ℝ) / 2) + a ^ (-(1 : ℝ) / 2) + 1) * U ^ ((4 : ℝ) / 5) := by
  have hlam : 0 < lam := (mul_pos ha (Real.rpow_pos_of_pos (by linarith) _)).trans_le hlower
  have h := reciprocal_terminal_error_bound hU ha ha.le hlower hupper
  have hinv : lam ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt lam := by
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg hlam.le, ← Real.sqrt_eq_rpow, one_div]
  rw [← Real.sqrt_eq_rpow, hinv] at h
  have hs := mul_le_mul_of_nonneg_right hT (Real.sqrt_nonneg lam)
  have hi : 0 ≤ 1 / Real.sqrt lam := by positivity
  nlinarith

/-- Once a fixed reciprocal derivative order has been chosen, every short
forward difference satisfies a uniform terminal cancellation estimate. -/
theorem reciprocal_terminal_range_bound (k : ℕ) (hk : 4 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U Z x : ℝ) (N : ℕ) (hs : List ℝ),
      2 ≤ U → hs.length + 2 = k →
      (∀ h ∈ hs, 1 ≤ h ∧ h ≤ U ^ (1 / (10 * (k : ℝ)))) →
      U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) →
      |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2) →
      U ≤ x → x + N + hs.sum ≤ 3 * U → (N : ℝ) ≤ 3 * U →
      ‖∑ j ∈ Finset.range N,
        ExponentialSum.phase (forwardDifference hs (fun y => Z / y) ((j : ℝ) + x))‖ ≤
        C * U ^ ((4 : ℝ) / 5) := by
  let a : ℝ := (k.factorial : ℝ) / (3 : ℝ) ^ (k + 1)
  let A : ℝ := (3 : ℝ) ^ (k + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨(6 * A + 15) * (3 * (a ^ ((1 : ℝ) / 2) + a ^ (-(1 : ℝ) / 2) + 1)),
    by positivity, ?_⟩
  intro U Z x N hs hU hlen hhs hlo hhi hx hend hN
  have hU0 : 0 < U := by linarith
  have hhs0 : ∀ h ∈ hs, 0 ≤ h := fun h hh => by linarith [(hhs h hh).1]
  have hhspos : ∀ h ∈ hs, 0 < h := fun h hh => by linarith [(hhs h hh).1]
  let Λ := |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod
  obtain ⟨hΛlo, hΛhi⟩ := reciprocal_phase_shift_scale (by linarith : 1 < U)
    (show 1 ≤ k by omega) hlo hhi hs (by omega) hhs
  have hΛpos : 0 < Λ := (Real.rpow_pos_of_pos hU0 _).trans_le hΛlo
  let lam := a * Λ
  have hlam : 0 < lam := mul_pos ha hΛpos
  have hbounds (y : ℝ) (hy : y ∈ Set.Icc x (x + N)) :
      lam ≤ |iteratedDeriv 2 (forwardDifference hs (fun z => Z / z)) y| ∧
      |iteratedDeriv 2 (forwardDifference hs (fun z => Z / z)) y| ≤ A * lam := by
    have hb := reciprocal_second_derivative_comparison_general hs hhspos Z 3 hU0
      (hx.trans hy.1) (show y + hs.sum ≤ 3 * U by linarith [hy.2])
    dsimp only at hb
    rw [hlen] at hb
    change a * Λ ≤ _ ∧ _ ≤ (k.factorial : ℝ) * Λ at hb
    have heq : A * lam = (k.factorial : ℝ) * Λ := by
      dsimp [A, lam, a]
      field_simp
    rwa [heq]
  have hh := ExponentialSum.second_derivative_test
    (forwardDifference hs (fun y => Z / y))
    (iteratedDeriv 1 (forwardDifference hs (fun y => Z / y)))
    (iteratedDeriv 2 (forwardDifference hs (fun y => Z / y)))
    x N lam A hlam hA.le
    (fun y hy => (reciprocal_forwardDifference_second_derivative_data hs hhs0 Z
      (hU0.trans_le (hx.trans hy.1))).1)
    (fun y hy => (reciprocal_forwardDifference_second_derivative_data hs hhs0 Z
      (hU0.trans_le (hx.trans hy.1))).2)
    hbounds
  have hb := reciprocal_terminal_sqrt_budget (by linarith : 1 ≤ U) ha hN
    (mul_le_mul_of_nonneg_left hΛlo ha.le)
    (mul_le_mul_of_nonneg_left hΛhi ha.le)
  exact hh.trans (by
    calc
      (6 * A + 15) * ((N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam) ≤
          (6 * A + 15) * (3 * (a ^ ((1 : ℝ) / 2) + a ^ (-(1 : ℝ) / 2) + 1) * U ^ ((4 : ℝ) / 5)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring)

/-- Integer interval terminal estimate, in the exact form used by iterated
correlations. The endpoint extension is absorbed by the enlarged interval. -/
theorem reciprocal_terminal_interval_bound (k : ℕ) (hk : 4 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U Z : ℝ) (L R : ℤ) (hs : List ℤ),
      2 ≤ U → hs.length = k - 2 →
      (∀ h ∈ hs, 0 < h ∧ h < (Nat.floor (U ^ (1 / (10 * (k : ℝ)))) : ℤ)) →
      U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) →
      |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2) →
      U ≤ (L : ℝ) → (R : ℝ) ≤ 2 * U →
      ‖∑ n ∈ Finset.Icc L (R - hs.sum),
        differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
          (fun y => Z / y) n)‖ ≤ C * U ^ ((4 : ℝ) / 5) := by
  obtain ⟨C, hC, hbound⟩ := reciprocal_terminal_range_bound k hk
  refine ⟨C, hC, ?_⟩
  intro U Z L R hs hU hlen hhs hlo hhi hL hR
  have hU0 : 0 < U := by linarith
  have hsum : 0 ≤ hs.sum := List.sum_nonneg (fun h hh => (hhs h hh).1.le)
  by_cases hempty : R - hs.sum < L
  · rw [Finset.Icc_eq_empty (not_le_of_gt hempty), Finset.sum_empty, norm_zero]
    positivity
  have hne : L ≤ R - hs.sum := by omega
  let N := (R - hs.sum + 1 - L).toNat
  have hNi : (N : ℤ) = R - hs.sum + 1 - L := Int.toNat_of_nonneg (by omega)
  have hNr := congrArg (fun n : ℤ => (n : ℝ)) hNi
  push_cast at hNr
  have hsumR : ((hs.map (fun h : ℤ => (h : ℝ))).sum) = (hs.sum : ℝ) := by
    simp
  have hspos : (0 : ℝ) ≤ (hs.sum : ℝ) := by exact_mod_cast hsum
  have hh := hbound U Z L N (hs.map (fun h : ℤ => (h : ℝ))) hU
    (by simp only [List.length_map, hlen]; omega)
    (by
      intro h hh
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hh
      constructor
      · exact_mod_cast (show (1 : ℤ) ≤ j by have := (hhs j hj).1; omega)
      · have hh : (j : ℝ) < (Nat.floor (U ^ (1 / (10 * (k : ℝ)))) : ℝ) := by
          exact_mod_cast (hhs j hj).2
        exact hh.le.trans (Nat.floor_le (Real.rpow_nonneg hU0.le _)))
    hlo hhi hL
    (by rw [hsumR]; linarith)
    (by linarith)
  have heq : (∑ n ∈ Finset.Icc L (R - hs.sum),
        differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
          (fun y => Z / y) n)) =
      ∑ j ∈ Finset.range N,
        ExponentialSum.phase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
          (fun y => Z / y) ((j : ℝ) + L)) := by
    rw [Int.Icc_eq_finset_map, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply, Int.cast_add, Int.cast_natCast]
    rw [add_comm]
    rfl
  rwa [heq]

/-- Eventual interface for finite-order uniformization of reciprocal phases. -/
theorem reciprocal_terminal_bound_eventually (k : ℕ) (hk : 4 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ U : ℝ in Filter.atTop, ∀ Z : ℝ,
      U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) →
      |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2) →
      ∀ L R : ℤ, U ≤ (L : ℝ) → (R : ℝ) ≤ 2 * U →
      ∀ hs : List ℤ, hs.length = k - 2 →
      (∀ h ∈ hs, 0 < h ∧ h < (Nat.floor (U ^ (1 / (10 * (k : ℝ)))) : ℤ)) →
      ‖∑ n ∈ Finset.Icc L (R - hs.sum),
        differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
          (fun y => Z / y) n)‖ ≤ C * U ^ ((4 : ℝ) / 5) := by
  obtain ⟨C, hC, hbound⟩ := reciprocal_terminal_interval_bound k hk
  refine ⟨C, hC, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with U hU
  intro Z hlo hhi L R hL hR hs hlen hhs
  exact hbound U Z L R hs hU hlen hhs hlo hhi hL hR

end Problem337

end

end OAI
