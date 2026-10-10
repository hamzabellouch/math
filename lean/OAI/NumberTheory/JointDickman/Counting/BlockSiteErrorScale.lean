import OAI.NumberTheory.JointDickman.Counting.BlockSiteComparison
import OAI.NumberTheory.JointDickman.Amplification.AmplificationMultiplier
import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryScale
import OAI.NumberTheory.JointDickman.Amplification.ReciprocalTail

namespace OAI

/-! # The block-site comparison error at the manuscript's cutoff scale -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem amplification_block_size_le_square (A : ℕ) :
    ∀ᶠ B : ℕ in atTop, A*amplificationMultiplier B ≤ B^2 := by
  filter_upwards [amplificationMultiplier_comparable,eventually_ge_atTop A,
    eventually_ge_atTop 1] with B hT hA hB
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hpow : (B : ℝ)^(8/25 : ℝ) ≤ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hBreal (show (8/25 : ℝ) ≤ 1 by norm_num)
  have hTB : amplificationMultiplier B ≤ B := by exact_mod_cast hT.2.2.trans hpow
  calc
    _ ≤ B*B := Nat.mul_le_mul hA hTB
    _ = _ := by ring

theorem block_site_polynomial_error_bound {B M : ℕ} (hB : 1 < B) (hM : M ≤ B^2)
    {C : ℝ} (hC : 0 ≤ C) :
    2*(C*(B : ℝ)^10)*(M : ℝ)^2*(∑ p ∈ auxiliaryPrimes B, 1/(p : ℝ)^2) ≤
      2*C/(B : ℝ) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have ht := sum_reciprocal_square_tail (auxiliaryPrimes B)
    (show auxiliaryCutoff B ≠ 0 from pow_ne_zero _ (by omega)) (by
      intro p hp
      exact_mod_cast (mem_filter.mp hp).2)
  have hpow : (B : ℝ)^15 ≤ (auxiliaryCutoff B : ℝ) := by
    simp only [auxiliaryCutoff,Nat.cast_pow]
    exact pow_le_pow_right₀ hB1 (by norm_num : 15 ≤ 1000)
  have ht' := ht.trans (one_div_le_one_div_of_le (pow_pos hB0 15) hpow)
  have hMreal : (M : ℝ) ≤ (B : ℝ)^2 := by exact_mod_cast hM
  calc
    _ ≤ 2*(C*(B : ℝ)^10)*((B : ℝ)^2)^2*(1/(B : ℝ)^15) := by gcongr
    _ = _ := by field_simp

theorem block_sites_auxiliary_comparison {B M : ℕ} (hB : 1 < B) (hM : M ≤ B^2)
    (F : (auxiliaryPrimes B → (univ : Finset (Fin M)).powerset) → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ x, |F x| ≤ C*(B : ℝ)^10) :
    |(∑ n ∈ range (∏ p ∈ auxiliaryPrimes B, p), F (blockSiteResidues M (auxiliaryPrimes B) n))/
        (∏ p ∈ auxiliaryPrimes B, (p : ℝ)) -
      ∑ x, bernoulliProductMass univ
        (fun p : auxiliaryPrimes B => fun _ : Fin M => 1/(p.val : ℝ)) x * F x| ≤
      2*C/(B : ℝ) := by
  have hP : ∀ p ∈ auxiliaryPrimes B, p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have hlarge : ∀ p ∈ auxiliaryPrimes B, M < p := by
    intro p hp
    have hp' : (auxiliaryCutoff B : ℝ) < p := (mem_filter.mp hp).2
    have hcut : B^2 ≤ auxiliaryCutoff B := by
      change B^2 ≤ B^1000
      exact pow_le_pow_right₀ (Nat.le_of_lt hB) (by decide : 2 ≤ 1000)
    have hpi : auxiliaryCutoff B < p := by exact_mod_cast hp'
    exact (hM.trans hcut).trans_lt hpi
  exact (block_sites_independent_error M (auxiliaryPrimes B) hP hlarge F
    (by positivity) hF).trans (block_site_polynomial_error_bound hB hM hC)

end JointDickman

end OAI
