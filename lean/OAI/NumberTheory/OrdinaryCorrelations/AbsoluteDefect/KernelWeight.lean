import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CompleteInverseOne

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set

namespace OrdinaryCorrelations.Completion
open Finset ArithmeticFunction

def kernelWeight (f : ℕ → ℂ) (σ : ℝ) (n : ℕ) : ℝ :=
  ‖kernel f n‖ * (n:ℝ)^(-σ)

lemma kernelWeight_nonneg (f : ℕ → ℂ) (σ : ℝ) (n : ℕ) : 0 ≤ kernelWeight f σ n :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

@[simp] lemma kernelWeight_zero (f : ℕ → ℂ) (σ : ℝ) : kernelWeight f σ 0 = 0 := by
  simp [kernelWeight]

@[simp] lemma kernelWeight_one {f : ℕ → ℂ} (h1 : f 1 = 1) (σ : ℝ) :
    kernelWeight f σ 1 = 1 := by simp [kernelWeight,kernel_one_norm h1]

lemma kernelWeight_mul {f : ℕ → ℂ} (hf : Multiplicative f) (h1 : f 1 = 1)
    (σ : ℝ) {m n : ℕ} (hmn : m.Coprime n) :
    kernelWeight f σ (m*n) = kernelWeight f σ m * kernelWeight f σ n := by
  simp only [kernelWeight,(kernel_multiplicative hf h1).map_mul_of_coprime hmn,
    norm_mul,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

lemma kernelWeight_prime {f : ℕ → ℂ} (h1 : f 1 = 1) (σ : ℝ) {p : ℕ} (hp : Nat.Prime p) :
    kernelWeight f σ p = 0 := by simp [kernelWeight,kernel_prime h1 hp]

lemma geometric_rpow (p k : ℕ) (σ : ℝ) : ((p^k:ℕ):ℝ)^(-σ) = ((p:ℝ)^(-σ))^k := by
  rw [Nat.cast_pow,←Real.rpow_natCast_mul (Nat.cast_nonneg p),mul_comm,
    Real.rpow_mul_natCast (Nat.cast_nonneg p)]

lemma kernelWeight_prime_pow_le {f : ℕ → ℂ} (hf : OneBounded f) (σ : ℝ)
    {p : ℕ} (hp : Nat.Prime p) (k : ℕ) :
    kernelWeight f σ (p^(k+1)) ≤ 2*((p:ℝ)^(-σ))^(k+1) := by
  rw [kernelWeight,geometric_rpow]
  exact mul_le_mul_of_nonneg_right (kernel_prime_pow_norm hf hp k)
    (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _)

lemma prime_ratio_lt_one {σ : ℝ} (hσ : 0 < σ) {p : ℕ} (hp : Nat.Prime p) :
    (p:ℝ)^(-σ) < 1 := by
  rw [Real.rpow_neg (Nat.cast_nonneg p)]
  exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by exact_mod_cast hp.one_lt) hσ)

lemma kernelWeight_prime_summable {f : ℕ → ℂ} (hf : OneBounded f) (h1 : f 1 = 1)
    {σ : ℝ} (hσ : 0 < σ) {p : ℕ} (hp : Nat.Prime p) :
    Summable (fun k : ℕ => kernelWeight f σ (p^k)) := by
  have hs := (summable_geometric_of_lt_one
    (Real.rpow_nonneg (Nat.cast_nonneg p) (-σ)) (prime_ratio_lt_one hσ hp)).mul_left 2
  apply Summable.of_nonneg_of_le (fun k => kernelWeight_nonneg _ _ _) _ hs
  intro k
  cases k with
  | zero => simp [h1]
  | succ k => exact kernelWeight_prime_pow_le hf σ hp k

lemma kernelWeight_prime_tsum_le {f : ℕ → ℂ} (hf : OneBounded f) (h1 : f 1 = 1)
    {σ : ℝ} (hσ : 0 < σ) {p : ℕ} (hp : Nat.Prime p) :
    (∑' k : ℕ, kernelWeight f σ (p^k)) ≤
      1 + 2*((p:ℝ)^(-σ))^2 / (1-(p:ℝ)^(-σ)) := by
  let r := (p:ℝ)^(-σ)
  have hr : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hr1 : r < 1 := prime_ratio_lt_one hσ hp
  have hs := kernelWeight_prime_summable hf h1 hσ hp
  have hg : Summable (fun k : ℕ => 2*r^2*r^k) :=
    (summable_geometric_of_lt_one hr hr1).mul_left (2*r^2)
  have ht : (∑' k : ℕ, kernelWeight f σ (p^(k+2))) ≤ 2*r^2/(1-r) := by
    calc
      (∑' k : ℕ, kernelWeight f σ (p^(k+2))) ≤ ∑' k : ℕ, 2*r^2*r^k := by
        apply Summable.tsum_le_tsum _ ((summable_nat_add_iff 2).mpr hs) hg
        intro k
        have hb := kernelWeight_prime_pow_le hf σ hp (k+1)
        calc
          kernelWeight f σ (p^(k+2)) ≤ 2*r^(k+2) := by
            simpa only [show k+1+1=k+2 by omega] using hb
          _ = 2*r^2*r^k := by rw [pow_add]; ring
      _ = 2*r^2/(1-r) := by
        rw [tsum_mul_left,tsum_geometric_of_lt_one hr hr1]
        rfl
  have he := hs.sum_add_tsum_nat_add 2
  norm_num [Finset.sum_range_succ,kernelWeight_one h1,kernelWeight_prime h1 σ hp] at he
  rw [←he]
  dsimp [r] at ht ⊢
  linarith

end OrdinaryCorrelations.Completion

end

end OAI
