import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeExpansion
import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeGeometry
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstRowCollection

namespace OAI

/-! Exact collection of Gauss height-tail rows above any fixed scale threshold.
This retains the independent smooth norm partitions and product envelope. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def tailHighScaleRows (i : ℕ) (ℓ : ℤ) (ξ H U X V : ℝ) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if V ≤ distinguishedScaleLength d then scaleFirstTailScaleRow i ℓ ξ H U X d else 0

theorem tailHighScaleRows_arity {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ m : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (i : ℕ) (ℓ : ℤ) (H U V : ℝ),
      tailHighScaleRows i ℓ ξ H U X V =
        ∑ j ∈ Finset.range m,
          ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
            if V ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
              tailPrimeTuplePiece i j ℓ ξ H U X d else 0 := by
  obtain ⟨m,hm⟩ := tailScaleRow_remainder_arity hξ
  refine ⟨m,?_⟩
  filter_upwards [hm,eventually_ge_atTop (1:ℝ)] with X hm hX
  intro i ℓ H U V
  have hF : 1 ≤ Real.exp primeProductWeights.radius*X :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp primeProductWeights.radius_nonneg) hX
  unfold tailHighScaleRows
  calc
    _ = ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        ∑ j ∈ Finset.range m,
          if V ≤ distinguishedScaleLength k then
            ∑ l : Fin j → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
              tailPrimeTuplePiece i j ℓ ξ H U X (Sum.elim k l) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hm i ℓ H U k]
      simp_rw [tailScaleDoubleRow_partition i _ ℓ ξ H U hF (zero_lt_one.trans_le hX) k]
      split_ifs <;> simp only [Finset.sum_const_zero]
    _ = ∑ j ∈ Finset.range m,
        ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
          ∑ l : Fin j → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
            if V ≤ distinguishedScaleLength k then
              tailPrimeTuplePiece i j ℓ ξ H U X (Sum.elim k l) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp only [Finset.sum_const_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [distinguishedScaleLength_sum_type] using
        sum_partition_sum_type (fun d : (Fin i ⊕ Fin j) →
          Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)) =>
          if V ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
            tailPrimeTuplePiece i j ℓ ξ H U X d else 0)

lemma tailHighScaleRows_window_split (i : ℕ) (ℓ : ℤ) (ξ H U X V : ℝ) :
    (∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      scaleFirstTailScaleRow i ℓ ξ H U X d) =
      (∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        if distinguishedScaleLength d < V then scaleFirstTailScaleRow i ℓ ξ H U X d else 0)+
      tailHighScaleRows i ℓ ξ H U X V := by
  unfold tailHighScaleRows
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : distinguishedScaleLength d < V
  · simp only [hd,not_le.mpr hd,ite_true,ite_false,add_zero]
  · simp only [hd,not_lt.mp hd,ite_true,ite_false,zero_add]

end CubicFirstMoment

end

end OAI
