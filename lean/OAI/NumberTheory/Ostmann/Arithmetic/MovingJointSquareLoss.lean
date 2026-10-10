import OAI.NumberTheory.Ostmann.Arithmetic.MovingRepresentativeSquares
import OAI.NumberTheory.Ostmann.Arithmetic.JointSquareLiftExclusions

namespace OAI

/-! # Joint square-exclusion estimate for the actual moving-tree rows -/

namespace Ostmann
open scoped BigOperators Classical

theorem moving_joint_square_loss {σ I : Type*} [Fintype I] [DecidableEq I]
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (T : MovingSlotData σ n) (hlevels : T.Levels tier) (rep : I → σ)
    (hf : ∀ i, T.Frequencies (fun s => (s : ZMod (value (rep i))) ≠ 0))
    (x₀ y₀ : ∀ i, ZMod (value (rep i))) (hy : ∀ i, y₀ i ≠ 0)
    (hbase : ∀ i (j : MovingRepresentativeOccurrences T (rep i)),
      let o := T.occurrences.get j.val
      let φ := MovingSlotReversal.naturalReduction (value (rep i)) value
      φ (movingSlotLine o.path o.current).a * x₀ i +
        φ (movingSlotLine o.path o.current).b * y₀ i = 0)
    (F : (∀ i, SquareLiftPairs (value (rep i)) (x₀ i) (y₀ i)) → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B) :
    let _ : ∀ i, Fact (value (rep i)).Prime := fun i => ⟨hprime (rep i)⟩
    let φ := fun i => MovingSlotReversal.naturalReduction (value (rep i) ^ 2) value
    (Fintype.card (∀ i, SquareLiftPairs (value (rep i)) (x₀ i) (y₀ i)) : ℝ)⁻¹ *
      ‖(∑ x, if ∀ i (j : MovingRepresentativeOccurrences T (rep i)),
        let o := T.occurrences.get j.val
        φ i (movingSlotLine o.path o.current).a * (x i).1.1 +
          φ i (movingSlotLine o.path o.current).b * (x i).2.1 ≠ 0 then F x else 0) -
        ∑ x, F x‖ ≤
      2 * B * (2 ^ n - 1 : ℕ) * ∑ i, (value (rep i) : ℝ)⁻¹ := by
  let : ∀ i, Fact (value (rep i)).Prime := fun i => ⟨hprime (rep i)⟩
  let J := fun i => MovingRepresentativeOccurrences T (rep i)
  let line := fun i (j : J i) =>
    let o := T.occurrences.get j.val
    movingSlotLine o.path o.current
  let φ := fun i => MovingSlotReversal.naturalReduction (value (rep i) ^ 2) value
  have hu (i : I) (j : J i) :=
    T.occurrence_units_of_prime_types tier value hprime hdisjoint hlevels
      (T.occurrences.get j.val) (List.get_mem _ _) (rep i)
      (T.occurrence_compensation_level tier hlevels _ (List.get_mem _ _) (rep i) j.property) (hf i)
  have hrow (i : I) (j : J i) :
      squareReduction (value (rep i)) (φ i (line i j).a) ≠ 0 ∨
        squareReduction (value (rep i)) (φ i (line i j).b) ≠ 0 := by
    simp only [φ, naturalReduction_square]
    apply movingHistoryLine_nonzero
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      exact (hu i j).1 t ht
    · exact (hu i j).2.1
    · exact (hu i j).2.2
  have hb := joint_square_lift_removed_mass_le (fun i => value (rep i)) J
    (fun i j => φ i (line i j).a) (fun i j => φ i (line i j).b) x₀ y₀ hy hrow
    (by simpa only [φ, naturalReduction_square] using hbase) F B hB hF
  refine hb.trans ?_
  calc
    2 * B * ∑ i, (Fintype.card (J i) : ℝ) / value (rep i) ≤
        2 * B * ∑ i, (2 ^ n - 1 : ℕ) / (value (rep i) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast movingRepresentativeOccurrences_card T (rep i)
    _ = _ := by simp only [div_eq_mul_inv, ← Finset.mul_sum]; ring

end Ostmann

end OAI
