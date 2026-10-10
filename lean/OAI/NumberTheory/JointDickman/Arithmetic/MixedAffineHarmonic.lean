import OAI.NumberTheory.JointDickman.Arithmetic.MixedAffineSieve

namespace OAI

/-! # Harmonic normalization for the numeric addition -/

namespace JointDickman
open Finset Classical

theorem mixed_affine_harmonic_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Finset ℕ) (a b c d : ℤ) (q W : ℝ) (u v Z : ℕ),
      0 ≤ q → q ≤ 1 → 0 < W → u ≤ v → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 4 ≤ p) →
      (∀ p ∈ P, (b : ZMod p) ≠ 0 ∧ (d : ZMod p) ≠ 0 ∧
        (a : ZMod p)*d-c*b ≠ 0) →
      (∀ n ∈ Ico u v, W ≤ (a : ℝ)+(b : ℝ)*n) →
      (∑ n ∈ Ico u v, (∏ p ∈ P,
        residueWeight q 0 ((a : ZMod p)+b*n)*residueWeight (1/2) 0 ((c : ZMod p)+d*n))/
          ((a : ℝ)+(b : ℝ)*n)) ≤
        (K*((v : ℝ)-u)*(∏ p ∈ P, (1-(3/2-q)/(p : ℝ)))+2*(Z+1 : ℝ)*(Z : ℝ)^2)/W := by
  obtain ⟨K,hK,hbound⟩ := mixed_affine_interval_sieve hFord hM
  refine ⟨K,hK,?_⟩
  intro P a b c d q W u v Z hq hq1 hW huv hZ hP hdet hden
  have hh := hbound P a b c d q u v Z hq hq1 huv hZ hP hdet
  calc
    _ ≤ (∑ n ∈ Ico u v, ∏ p ∈ P,
        residueWeight q 0 ((a : ZMod p)+b*n)*residueWeight (1/2) 0 ((c : ZMod p)+d*n))/W := by
      rw [sum_div]
      apply sum_le_sum
      intro n hn
      exact div_le_div_of_nonneg_left (prod_nonneg (fun p _ => mul_nonneg
        (residueWeight_nonneg _ _ hq) (residueWeight_nonneg _ _ (by norm_num)))) hW (hden n hn)
    _ ≤ _ := div_le_div_of_nonneg_right hh hW.le

end JointDickman

end OAI
