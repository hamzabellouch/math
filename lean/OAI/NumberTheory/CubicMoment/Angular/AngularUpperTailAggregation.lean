import OAI.NumberTheory.CubicMoment.Estimates.UpperTailAggregation
import OAI.NumberTheory.CubicMoment.Angular.AngularUpperTailEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedAggregation
import OAI.NumberTheory.CubicMoment.Estimates.PrimeModelLogTail

namespace OAI

/-! Aggregate the literal upper-height stopped terms over their original
labels, side dyads and distinguished-prime scales. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

def angular_upperStoppedEnvelopeTail (i : ℕ) (κ ρ ξ H T X : ℝ) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength d < X^(1/3-2*κ) then
      ∑ s ∈ Finset.range (heightWindowCount H T),
        upperTailStoppedRow i ℓ κ ρ ξ H (T*(3/2:ℝ)^s) X d
    else 0

lemma angular_upperTailStoppedRow_height_dyads (i : ℕ) (κ ρ ξ H T X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    (∑ s ∈ Finset.range (heightWindowCount H T),
      upperTailStoppedRow i ℓ κ ρ ξ H (T*(3/2:ℝ)^s) X d) =
      ∑ q ∈ stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          ∑ j ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
            ∑ k ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
              ∑ s ∈ Finset.range (heightWindowCount H T),
                upperTailStoppedDyad i ℓ κ ρ ξ H (T*(3/2:ℝ)^s) X d q j k := by
  simp_rw [upperTailStoppedRow_dyads]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [←Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

theorem angular_upperStoppedEnvelopeTail_aggregate (i : ℕ) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (κ ξ H T X : ℝ), 1 ≤ X → ∀ (M : ℝ), 0 ≤ M →
      (∀ (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
        (q : ℕ × ℕ × ℕ),
        q ∈ stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X) →
        ∀ j k : ℕ, ‖∑ s ∈ Finset.range (heightWindowCount H T),
          upperTailStoppedDyad i ℓ κ ρ ξ H (T*(3/2:ℝ)^s) X d q j k‖ ≤ M) →
      ‖angular_upperStoppedEnvelopeTail ℓ i κ ρ ξ H T X‖ ≤
        K*(1+Real.log X)^(i+5)*M := by
  obtain ⟨D,hD,hcount⟩ := stoppedFactorSupport_log_count
  obtain ⟨C,hC,hlabels⟩ := stopping_label_weighted_sum_dilated hρ
    (Real.one_le_exp primeProductWeights.radius_nonneg)
  obtain ⟨E,hE,hparts⟩ := stopped_norm_partition_subset_count i
  refine ⟨E*(C*D^2),by positivity,?_⟩
  intro κ ξ H T X hX M hM hpiece
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  let I := stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)
  let J := (distinguishedStoppedSide X).image stoppedNormDyadIndex
  let S := (Finset.univ : Finset (Fin i → Fin (normPartitionCount
    (Real.exp primeProductWeights.radius*X))))
  have hI : I ⊆ stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X) := Finset.Subset.refl _
  have hJ : (J.card:ℝ) ≤ D*(1+Real.log X) := hcount X hX _
  have hrow (d) : ‖∑ s ∈ Finset.range (heightWindowCount H T),
      upperTailStoppedRow i ℓ κ ρ ξ H (T*(3/2:ℝ)^s) X d‖ ≤
      (C*D^2)*(1+Real.log X)^5*M := by
    rw [angular_upperTailStoppedRow_height_dyads ℓ]
    have hinner (q) (hq : q ∈ I) :
        ‖∑ j ∈ J, ∑ k ∈ J, ∑ s ∈ Finset.range (heightWindowCount H T),
          upperTailStoppedDyad i ℓ κ ρ ξ H (T*(3/2:ℝ)^s) X d q j k‖ ≤
        D^2*(1+Real.log X)^2*M := by
      apply (norm_double_sum_le_card_sq J J _ (fun j _ k _ => hpiece d q hq j k)).trans
      have hs := mul_le_mul hJ hJ (Nat.cast_nonneg J.card)
        (by positivity : 0 ≤ D*(1+Real.log X))
      calc
        _ ≤ (D*(1+Real.log X))*(D*(1+Real.log X))*M := mul_le_mul_of_nonneg_right hs hM
        _ = _ := by ring
    exact ((hlabels X hX I hI).2 _ (D^2*(1+Real.log X)^2*M)
      (by positivity) hinner).trans_eq (by ring)
  have hb (d) : ‖(if distinguishedScaleLength d < X^(1/3-2*κ) then
      ∑ s ∈ Finset.range (heightWindowCount H T),
        upperTailStoppedRow i ℓ κ ρ ξ H (T*(3/2:ℝ)^s) X d else 0)‖ ≤
      (C*D^2)*(1+Real.log X)^5*M := by
    split_ifs
    · exact hrow d
    · rw [norm_zero]; positivity
  calc
    _ ≤ ∑ d ∈ S, (C*D^2)*(1+Real.log X)^5*M := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun d _ => hb d)
    _ = (S.card:ℝ)*((C*D^2)*(1+Real.log X)^5*M) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (E*(1+Real.log X)^i)*((C*D^2)*(1+Real.log X)^5*M) :=
      mul_le_mul_of_nonneg_right (hparts X hX S) (by positivity)
    _ = _ := by rw [pow_add]; ring

end CubicFirstMoment

end

end OAI
