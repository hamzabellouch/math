import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstArity
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstHighSum

namespace OAI

/-! Exact collection of the independently partitioned high-scale rows.
This connects the scale-first identity to the proved high-box estimates. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma sum_partition_sum_type {i j N : ℕ}
    (F : ((Fin i ⊕ Fin j) → Fin N) → ℂ) :
    (∑ k : Fin i → Fin N, ∑ l : Fin j → Fin N, F (Sum.elim k l)) =
      ∑ d : (Fin i ⊕ Fin j) → Fin N, F d := by
  rw [←Fintype.sum_prod_type']
  apply Finset.sum_equiv (Equiv.sumArrowEquivProdArrow (Fin i) (Fin j) (Fin N)).symm
  · intro _
    simp only [Finset.mem_univ]
  · intro _ _
    rfl

lemma distinguishedScaleLength_sum_type {i j N : ℕ}
    (k : Fin i → Fin N) (l : Fin j → Fin N) :
    largeTupleDistinguishedScale (fun a => (Sum.elim k l a).val) =
      distinguishedScaleLength k := by
  rfl

theorem distinguishedHighScaleRows_arity {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ m : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (i : ℕ) (ℓ : ℤ) (Ct : ℕ) (H : ℝ),
      distinguishedHighScaleRows i ℓ ξ Ct H X =
        ∑ j ∈ Finset.range m,
          ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
            if X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
              scaleFirstPrimeTuplePiece i j ℓ ξ Ct H X d else 0 := by
  obtain ⟨m,hm⟩ := distinguishedScaleRow_remainder_arity hξ
  refine ⟨m,?_⟩
  filter_upwards [hm,eventually_ge_atTop (1:ℝ)] with X hm hX
  intro i ℓ Ct H
  have hF : 1 ≤ Real.exp primeProductWeights.radius*X :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp primeProductWeights.radius_nonneg) hX
  unfold distinguishedHighScaleRows
  calc
    _ = ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        ∑ j ∈ Finset.range m,
          if X^(69/200:ℝ) ≤ distinguishedScaleLength k then
            ∑ l : Fin j → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
              scaleFirstPrimeTuplePiece i j ℓ ξ Ct H X (Sum.elim k l) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hm i ℓ Ct H k]
      simp_rw [distinguishedScaleDoubleRow_partition i _ ℓ ξ Ct H hF (zero_lt_one.trans_le hX) k]
      split_ifs <;> simp only [Finset.sum_const_zero]
    _ = ∑ j ∈ Finset.range m,
        ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
          ∑ l : Fin j → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
            if X^(69/200:ℝ) ≤ distinguishedScaleLength k then
              scaleFirstPrimeTuplePiece i j ℓ ξ Ct H X (Sum.elim k l) else 0 := by
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
          if X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
            scaleFirstPrimeTuplePiece i j ℓ ξ Ct H X d else 0)

end CubicFirstMoment

end

end OAI
