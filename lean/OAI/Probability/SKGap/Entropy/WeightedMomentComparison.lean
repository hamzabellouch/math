import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

lemma sum_abs_le_sqrt_card_l2 (d : ι → ℝ) :
    (∑ i, |d i|) ≤ √(Fintype.card ι:ℝ)*√(∑ i,d i^2) := by
  simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : ι => (1:ℝ)) (fun i => |d i|)

theorem weighted_moment_comparison (a v y f : ι → ℝ) {H C D R : ℝ}
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 1 ≤ R)
    (ha : ∀ i, |a i-v i| ≤ D)
    (hsmall : ∀ i, |y i| ≤ R → |f i| ≤ H)
    (hlarge : ∀ i, |f i| ≤ C*(1+y i^2)) :
    |∑ i,(a i-v i)*f i| ≤ H*√(Fintype.card ι:ℝ)*√(∑ i,(a i-v i)^2)+
      2*C*D*∑ i,if R < |y i| then y i^2 else 0 := by
  have hpoint (i : ι) : |(a i-v i)*f i| ≤ H*|a i-v i|+
      2*C*D*(if R < |y i| then y i^2 else 0) := by
    rw [abs_mul]
    by_cases hi : R < |y i|
    · rw [ite_eq_left hi]
      have hy : 1 ≤ y i^2 := by nlinarith [sq_abs (y i)]
      have hf : |f i| ≤ 2*C*y i^2 := (hlarge i).trans (by nlinarith)
      have hh := mul_le_mul (ha i) hf (abs_nonneg _) hD
      nlinarith [mul_nonneg hH (abs_nonneg (a i-v i))]
    · rw [ite_eq_right hi,mul_zero,add_zero]
      simpa only [mul_comm H] using mul_le_mul_of_nonneg_left (hsmall i (le_of_not_gt hi)) (abs_nonneg (a i-v i))
  calc
    _ ≤ ∑ i, |(a i-v i)*f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,(H*|a i-v i|+2*C*D*(if R < |y i| then y i^2 else 0)) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = H*(∑ i,|a i-v i|)+2*C*D*∑ i,if R < |y i| then y i^2 else 0 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    _ ≤ _ := by
      rw [mul_assoc H]
      exact add_le_add (mul_le_mul_of_nonneg_left (sum_abs_le_sqrt_card_l2 _) hH) le_rfl

theorem normalized_weighted_moment_comparison {n : ℕ} (hn : 0 < n)
    (a v y f : Fin n → ℝ) {H C D R ε ν : ℝ}
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 1 ≤ R)
    (hε : 0 ≤ ε) (ha : ∀ i, |a i-v i| ≤ D)
    (hsmall : ∀ i, |y i| ≤ R → |f i| ≤ H)
    (hlarge : ∀ i, |f i| ≤ C*(1+y i^2))
    (hclose : ∑ i,(a i-v i)^2 ≤ ε^2*(n:ℝ))
    (htail : (∑ i,if R < |y i| then y i^2 else 0) ≤ ν*(n:ℝ)) :
    |(∑ i,(a i-v i)*f i)/(n:ℝ)| ≤ H*ε+2*C*D*ν := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnorm : √(∑ i,(a i-v i)^2) ≤ ε*√(n:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hnR.le]
  have h := weighted_moment_comparison a v y f hH hC hD hR ha hsmall hlarge
  simp only [Fintype.card_fin] at h
  have h' : |∑ i,(a i-v i)*f i| ≤ (H*ε+2*C*D*ν)*(n:ℝ) := by
    calc
      _ ≤ _ := h
      _ ≤ H*√(n:ℝ)*(ε*√(n:ℝ))+2*C*D*(ν*(n:ℝ)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hnorm (by positivity))
          (mul_le_mul_of_nonneg_left htail (by positivity))
      _ = H*ε*(√(n:ℝ))^2+2*C*D*ν*(n:ℝ) := by ring
      _ = _ := by rw [Real.sq_sqrt hnR.le]; ring
  rw [abs_div,abs_of_pos hnR]
  exact (div_le_iff₀ hnR).mpr h'
end SKGap
end
end

end OAI
