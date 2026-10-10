import Mathlib
import OAI.Probability.LogConcave.Sampling.TensorGrad

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

lemma productEnergyBudget_scaled (C B : ℕ → ℝ) (α κ ρ : ℝ) (j : ℕ) :
    productEnergyBudget (fun k => C k*α*ρ^k) (fun k => κ*ρ^(2*k)*B k) j =
      κ*α^2*ρ^(2*(j+1))*productEnergyBudget C B j := by
  unfold productEnergyBudget
  calc
    _ = 2^j*(κ*α^2*ρ^(2*(j+1))*∑s∈(Finset.univ : Finset (Fin j)).powerset,
        (C s.card)^2*B (j-s.card+1)) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      have hc : s.card ≤ j := (Finset.card_le_univ s).trans_eq (Fintype.card_fin j)
      have hp : (ρ^s.card)^2*ρ^(2*(j-s.card+1))=ρ^(2*(j+1)) := by
        rw [← pow_mul,← pow_add]
        congr 1
        omega
      calc
        (C s.card*α*ρ^s.card)^2*(κ*ρ^(2*(j-s.card+1))*B (j-s.card+1)) =
          κ*α^2*((ρ^s.card)^2*ρ^(2*(j-s.card+1)))*((C s.card)^2*B (j-s.card+1)) := by ring
        _ = _ := by rw [hp]
    _ = _ := by ring

lemma adjointEnergyBudget_nonneg {K : ℝ} (hK : 0 ≤ K) (C : ℕ → ℝ)
    {B : ℕ → ℝ} (hB : ∀j,0 ≤ B j) (j : ℕ) : 0 ≤ adjointEnergyBudget K C B j := by
  unfold adjointEnergyBudget
  apply mul_nonneg (by norm_num)
  apply add_nonneg (add_nonneg (hB _) (mul_nonneg hK (hB _)))
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun s _ => mul_nonneg (sq_nonneg _) (hB _)))

lemma adjointEnergyBudget_scaled {K κ ρ : ℝ} (hK : 0 ≤ K) (hκ : 0 ≤ κ) (hρ : 1 ≤ ρ)
    (D B : ℕ → ℝ) (hB : ∀j,0 ≤ B j) (q j : ℕ) :
    adjointEnergyBudget K (fun k => D k*ρ^k) (fun k => κ*ρ^(2*(k+q))*B k) j ≤
      κ*ρ^(2*(j+q+1))*adjointEnergyBudget K D B j := by
  have hr : 0 ≤ ρ := zero_le_one.trans hρ
  have hp : ρ^(2*(j+q)) ≤ ρ^(2*(j+q+1)) := pow_le_pow_right₀ hρ (by omega)
  have hlead : κ*ρ^(2*(j+1+q))*B (j+1)=κ*ρ^(2*(j+q+1))*B (j+1) := by rw [show j+1+q=j+q+1 by omega]
  have hs : (∑s∈(Finset.univ : Finset (Fin j)).powerset.erase ∅,
      (D s.card*ρ^s.card)^2*(κ*ρ^(2*(j-s.card+q))*B (j-s.card))) ≤
      κ*ρ^(2*(j+q+1))*∑s∈(Finset.univ : Finset (Fin j)).powerset.erase ∅,
        (D s.card)^2*B (j-s.card) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hc : s.card ≤ j := (Finset.card_le_univ s).trans_eq (Fintype.card_fin j)
    have he : (ρ^s.card)^2*ρ^(2*(j-s.card+q))=ρ^(2*(j+q)) := by
      rw [← pow_mul,← pow_add]
      congr 1
      omega
    calc
      (D s.card*ρ^s.card)^2*(κ*ρ^(2*(j-s.card+q))*B (j-s.card)) =
        κ*((ρ^s.card)^2*ρ^(2*(j-s.card+q)))*((D s.card)^2*B (j-s.card)) := by ring
      _ = κ*ρ^(2*(j+q))*((D s.card)^2*B (j-s.card)) := by rw [he]
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hκ)
        (mul_nonneg (sq_nonneg _) (hB _))
  unfold adjointEnergyBudget
  calc
    _ ≤ 2*(κ*ρ^(2*(j+q+1))*B (j+1)+K*(κ*ρ^(2*(j+q+1))*B j)+
        2^j*(κ*ρ^(2*(j+q+1))*∑s∈(Finset.univ : Finset (Fin j)).powerset.erase ∅,
          (D s.card)^2*B (j-s.card))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add
      · exact add_le_add hlead.le (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hκ) (hB _)) hK)
      · exact mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end LogConcaveSampling

end

end

end

end OAI
