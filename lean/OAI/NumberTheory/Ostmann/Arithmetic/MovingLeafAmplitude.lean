import OAI.NumberTheory.Ostmann.Arithmetic.MovingScalarWindows
import OAI.NumberTheory.Ostmann.Tree.PairedFrequencyProjection
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticFrequencyTree

namespace OAI

/-! # The scalar leaf weights retain the actual frequency cutoff -/

namespace Ostmann
open scoped Classical

theorem movingDataWeight_unit_leaf_bound {σ : Type*}
    (F : {k : ℕ} → MovingSlotData σ k → ℤ → ℂ) (V : ℕ)
    (hF : ∀ s regular, ‖F (.leaf s regular) s‖ ≤ if s.natAbs ≤ V then 1 else 0)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) :
    ‖movingDataWeight F (fun _ _ _ _ => 1)
      (buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a)‖ ≤
      frequencyLeafWeight (singleFrequencyLeaf S V) n t := by
  induction a with
  | leaf => exact hF _ _
  | @node n u l r ihL ihR =>
    simp only [buildMovingSlotData, frequencyTreeMap, movingDataWeight,
      Complex.ofReal_one, one_mul, norm_mul, norm_star, frequencyLeafWeight]
    exact mul_le_mul (ihL _ _ _) (ihR _ _ _) (norm_nonneg _)
      (frequencyLeafWeight_nonneg _ (fun _ => by unfold singleFrequencyLeaf; split_ifs <;> norm_num) _ _)

/-- Removing the explicit compensation multipliers leaves a scalar amplitude
of norm at most one whenever the actual leaf coefficients have that bound. -/
theorem movingDataWeight_unit_norm_le_one {σ : Type*}
    (F : {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (hF : ∀ s regular, ‖F (.leaf s regular) s‖ ≤ 1)
    {n : ℕ} (T : MovingSlotData σ n) :
    ‖movingDataWeight F (fun _ _ _ _ => 1) T‖ ≤ 1 := by
  induction T with
  | leaf s regular => exact hF s regular
  | node s CL CR U l r ihL ihR =>
    simp only [movingDataWeight, Complex.ofReal_one, one_mul, norm_mul, norm_star]
    exact (mul_le_mul ihL ihR (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

theorem frequencyLeafWeight_pair_projection (S : Finset ℤ) (V n : ℕ)
    (t : FrequencyTree (S × S) n) :
    frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n false t) *
      frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n true t) =
      frequencyLeafWeight (pairedFrequencyLeaf S V) n t := by
  induction n with
  | zero =>
    change (if (t.1 : ℤ).natAbs ≤ V then (1 : ℝ) else 0) *
      (if (t.2 : ℤ).natAbs ≤ V then 1 else 0) = _
    unfold frequencyLeafWeight pairedFrequencyLeaf
    split_ifs <;> simp_all
  | succ n ih =>
    change
      (frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n false t.2.1) *
        frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n false t.2.2)) *
      (frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n true t.2.1) *
        frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n true t.2.2)) = _ * _
    rw [show ∀ a b c d : ℝ, (a * b) * (c * d) = (a * c) * (b * d) by intros; ring]
    rw [ih t.2.1, ih t.2.2]

theorem movingDataWeight_pair_unit_leaf_bound {σ : Type*}
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ) (V : ℕ)
    (hF : ∀ b s regular, ‖F b (.leaf s regular) s‖ ≤ if s.natAbs ≤ V then 1 else 0)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree (S × S) n)
    (small : Bool → TreeLeafTuple (List σ) n) (bulk : TreeLeafTuple (List σ) n)
    (a : Bool → MovingSampleSlots σ n) :
    let T := fun b => buildMovingSlotData n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)) (small b) bulk (a b)
    ‖movingDataWeight (F false) (fun _ _ _ _ => 1) (T false)‖ *
      ‖movingDataWeight (F true) (fun _ _ _ _ => 1) (T true)‖ ≤
      frequencyLeafWeight (pairedFrequencyLeaf S V) n t := by
  intro T
  rw [← frequencyLeafWeight_pair_projection]
  exact mul_le_mul (movingDataWeight_unit_leaf_bound (F false) V (hF false) S n _ _ bulk _)
    (movingDataWeight_unit_leaf_bound (F true) V (hF true) S n _ _ bulk _) (norm_nonneg _)
    (frequencyLeafWeight_nonneg _ (fun _ => by unfold singleFrequencyLeaf; split_ifs <;> norm_num) _ _)

end Ostmann

end OAI
