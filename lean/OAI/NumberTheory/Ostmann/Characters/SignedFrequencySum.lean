import Mathlib.Data.Int.Order.Lemmas
import OAI.NumberTheory.Ostmann.Arithmetic.ReducedFrequencySum

namespace OAI

/-! # Both signs in the internal-frequency sum -/

namespace Ostmann

open scoped BigOperators Classical

theorem natAbs_fiber_card_le_two (S : Finset ℤ) (a : ℕ) :
    (S.filter fun s => s.natAbs = a).card ≤ 2 := by
  have hsub : (S.filter fun s => s.natAbs = a) ⊆ {(a : ℤ), -(a : ℤ)} := by
    intro s hs
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (Int.natAbs_eq_iff.mp (Finset.mem_filter.mp hs).2)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_insert_le _ _).trans_eq (by simp))

theorem sum_signed_magnitudes_le (S : Finset ℤ) (N : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (F : ℕ → ℝ) (hF : ∀ a ∈ Finset.Icc 1 N, 0 ≤ F a) :
    (∑ s ∈ S, F s.natAbs) ≤ 2 * ∑ a ∈ Finset.Icc 1 N, F a := by
  have hmem (s : ℤ) (hs : s ∈ S) : s.natAbs ∈ Finset.Icc 1 N :=
    Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
      (Int.natAbs_ne_zero.mpr (hS s hs).1), (hS s hs).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmem (fun s => F s.natAbs)]
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 N, 2 * F a := by
      apply Finset.sum_le_sum
      intro a ha
      have heq : (∑ s ∈ S.filter (fun s => s.natAbs = a), F s.natAbs) =
          ((S.filter (fun s => s.natAbs = a)).card : ℝ) * F a := by
        calc
          _ = ∑ _s ∈ S.filter (fun s => s.natAbs = a), F a :=
            Finset.sum_congr rfl fun _ hs => congrArg F (Finset.mem_filter.mp hs).2
          _ = _ := by simp
      rw [heq]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast natAbs_fiber_card_le_two S a) (hF a ha)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The factor four is exactly the two possible signs in each history. -/
theorem signed_reducedFrequency_lcm_sum_le (S T : Finset ℤ) (N g h : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hT : ∀ t ∈ T, t ≠ 0 ∧ t.natAbs ≤ N) (hg : g ≠ 0) (hh : h ≠ 0) :
    (∑ s ∈ S, ∑ t ∈ T,
      (((reducedFrequency g s.natAbs).lcm (reducedFrequency h t.natAbs) : ℕ) : ℝ)⁻¹) ≤
      4 * (g.divisors.card : ℝ) * h.divisors.card * (1 + Real.log N) ^ 3 := by
  calc
    _ ≤ 2 * ∑ a ∈ Finset.Icc 1 N, ∑ t ∈ T,
        (((reducedFrequency g a).lcm (reducedFrequency h t.natAbs) : ℕ) : ℝ)⁻¹ :=
      sum_signed_magnitudes_le S N hS _ (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
    _ ≤ 2 * ∑ a ∈ Finset.Icc 1 N, 2 * ∑ b ∈ Finset.Icc 1 N,
        (((reducedFrequency g a).lcm (reducedFrequency h b) : ℕ) : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro a _
      exact sum_signed_magnitudes_le T N hT
        (fun b => (((reducedFrequency g a).lcm (reducedFrequency h b) : ℕ) : ℝ)⁻¹)
        (fun _ _ => by positivity)
    _ = 4 * (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        (((reducedFrequency g a).lcm (reducedFrequency h b) : ℕ) : ℝ)⁻¹) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := by
      have hbound := mul_le_mul_of_nonneg_left (reducedFrequency_lcm_sum_le N g h hg hh)
        (show (0 : ℝ) ≤ 4 by norm_num)
      convert hbound using 1
      ring

end Ostmann

end OAI
