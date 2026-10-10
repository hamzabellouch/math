import OAI.NumberTheory.JointDickman.Amplification.ArithmeticSquareHits
import OAI.NumberTheory.JointDickman.Amplification.FiniteEventUnion
import OAI.NumberTheory.JointDickman.Counting.BlockSiteErrorScale

namespace OAI

/-! # Removing all site squares in a block, after taking digit averages -/

namespace JointDickman
open Finset PublishedInputs Classical

def BlockSquareHit (B M u : ℕ) : Prop :=
  ∃ i : Fin M, ∃ p ∈ auxiliaryPrimes B, p^2 ∣ u+(i.val+1)

theorem residue_block_squareHit_bound (B M : ℕ) :
    (∑ u : ZMod (auxiliarySquarePeriod B),
      if BlockSquareHit B M u.val then (1 : ℝ) else 0)/
        (auxiliarySquarePeriod B : ℝ) ≤
      (M : ℝ)*∑ p ∈ auxiliaryPrimes B, 1/(p : ℝ)^2 := by
  let w := fun _ : ZMod (auxiliarySquarePeriod B) => 1/(auxiliarySquarePeriod B : ℝ)
  have hw : ∀ u, 0 ≤ w u := by intro u; dsimp [w]; positivity
  have hunif (E : ZMod (auxiliarySquarePeriod B) → Prop) :
      finiteProbability w E = (∑ u, if E u then (1 : ℝ) else 0)/(auxiliarySquarePeriod B : ℝ) := by
    simp only [finiteProbability,w,ite_div,one_div,zero_div,sum_div]
  have hp (i : Fin M) (p : ℕ) (hp : p ∈ auxiliaryPrimes B) :
      finiteProbability w (fun u => p^2 ∣ u.val+(i.val+1)) = 1/(p : ℝ)^2 := by
    rw [hunif]
    convert residue_square_divisor_mean hp (i.val+1) using 1
    congr 1
    apply sum_congr rfl
    intro u _
    by_cases h : p^2 ∣ u.val+(i.val+1) <;> simp [h]
  rw [← hunif]
  change finiteProbability w (fun u => ∃ i : Fin M, ∃ p ∈ auxiliaryPrimes B,
    p^2 ∣ u.val+(i.val+1)) ≤ _
  calc
    _ ≤ ∑ i : Fin M, finiteProbability w
        (fun u => ∃ p ∈ auxiliaryPrimes B, p^2 ∣ u.val+(i.val+1)) :=
      finiteProbability_union_le w hw _
    _ ≤ ∑ i : Fin M, ∑ p ∈ auxiliaryPrimes B,
        finiteProbability w (fun u => p^2 ∣ u.val+(i.val+1)) :=
      sum_le_sum (fun i _ => finiteProbability_exists_mem w hw _ _)
    _ = _ := by simp_rw [sum_congr rfl (fun p h => hp _ p h)]; simp

/-- Polynomially bounded graph tests pay a vanishing total cost when all
site squares are removed. -/
theorem block_squareHit_polynomial_bound {B M : ℕ} (hB : 1 < B) (hM : M ≤ B^2) :
    (B : ℝ)^10 * ((∑ u : ZMod (auxiliarySquarePeriod B),
      if BlockSquareHit B M u.val then (1 : ℝ) else 0)/(auxiliarySquarePeriod B : ℝ)) ≤
        1/(B : ℝ) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have ht := sum_reciprocal_square_tail (auxiliaryPrimes B)
    (show auxiliaryCutoff B ≠ 0 from pow_ne_zero _ (by omega)) (by
      intro p hp
      exact_mod_cast (mem_filter.mp hp).2)
  have hpow : (B : ℝ)^13 ≤ (auxiliaryCutoff B : ℝ) := by
    simp only [auxiliaryCutoff,Nat.cast_pow]
    exact pow_le_pow_right₀ hB1 (by norm_num : 13 ≤ 1000)
  have ht' := ht.trans (one_div_le_one_div_of_le (pow_pos hB0 13) hpow)
  have hMr : (M : ℝ) ≤ (B : ℝ)^2 := by exact_mod_cast hM
  calc
    _ ≤ (B : ℝ)^10*((M : ℝ)*∑ p ∈ auxiliaryPrimes B, 1/(p : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (residue_block_squareHit_bound B M) (by positivity)
    _ ≤ (B : ℝ)^10*((B : ℝ)^2*(1/(B : ℝ)^13)) := by gcongr
    _ = _ := by field_simp

end JointDickman

end OAI
