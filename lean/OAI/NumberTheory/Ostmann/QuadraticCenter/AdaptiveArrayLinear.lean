import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveArrayDivisor

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem adaptive_jacobi_norm_le (n q : ℕ) : ‖(jacobiSym (n:ℤ) q:ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy (n:ℤ) q with h | h | h <;> simp [h]

theorem adaptive_sqrt_inv_norm_le {s : ℕ} (hs : 0 < s) :
    ‖(Real.sqrt (s:ℝ):ℂ)⁻¹‖ ≤ 1 := by
  have hs1 : (1:ℝ) ≤ Real.sqrt (s:ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1:ℝ) ≤ s by exact_mod_cast hs)
  rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_le_one_of_one_le₀ hs1

def adaptiveArrayLinear (L q : ℕ) (lam : ℝ) (s : ℕ) (G : ℕ → ℕ → ℂ) : ℂ :=
  (Real.sqrt (s:ℝ):ℂ)⁻¹ * ∑ v ∈ L.divisors,
    (jacobiSym (v:ℤ) q:ℂ)/(Real.sqrt (v:ℝ):ℂ) * ∑ d ∈ L.divisors,
      (lam:ℂ)^d.primeFactors.card*(jacobiSym (d:ℤ) q:ℂ)*G d v

theorem adaptiveArrayLinear_sub (L q : ℕ) (lam : ℝ) (s : ℕ)
    (G H : ℕ → ℕ → ℂ) :
    adaptiveArrayLinear L q lam s G-adaptiveArrayLinear L q lam s H =
      adaptiveArrayLinear L q lam s (fun d v => G d v-H d v) := by
  simp only [adaptiveArrayLinear,Finset.sum_sub_distrib,mul_sub]

theorem adaptiveArrayLinear_norm_le (L q : ℕ) {lam : ℝ} (hlam : |lam| ≤ 1)
    {s : ℕ} (hs : 0 < s) (G : ℕ → ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ d ∈ L.divisors, ∀ v ∈ L.divisors, ‖G d v‖ ≤ B) :
    ‖adaptiveArrayLinear L q lam s G‖ ≤ (L.divisors.card:ℝ)^2*B := by
  have hcoeff (d : ℕ) : ‖(lam:ℂ)^d.primeFactors.card*(jacobiSym (d:ℤ) q:ℂ)‖ ≤ 1 := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul (pow_le_one₀ (abs_nonneg lam) hlam) (adaptive_jacobi_norm_le d q)
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hinner (v : ℕ) (hv : v ∈ L.divisors) :
      ‖∑ d ∈ L.divisors,(lam:ℂ)^d.primeFactors.card*(jacobiSym (d:ℤ) q:ℂ)*G d v‖ ≤
        L.divisors.card*B := by
    calc
      _ ≤ ∑ d ∈ L.divisors,‖(lam:ℂ)^d.primeFactors.card*(jacobiSym (d:ℤ) q:ℂ)*G d v‖ := norm_sum_le _ _
      _ ≤ ∑ _d ∈ L.divisors,B := by
        apply Finset.sum_le_sum
        intro d hd
        rw [norm_mul]
        exact ((mul_le_mul_of_nonneg_left (hG d hd v hv) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_right (hcoeff d) hB)).trans_eq (one_mul B)
      _ = _ := by simp
  have houter : ‖∑ v ∈ L.divisors,(jacobiSym (v:ℤ) q:ℂ)/(Real.sqrt (v:ℝ):ℂ)*
      ∑ d ∈ L.divisors,(lam:ℂ)^d.primeFactors.card*(jacobiSym (d:ℤ) q:ℂ)*G d v‖ ≤
      (L.divisors.card:ℝ)^2*B := by
    calc
      _ ≤ ∑ v ∈ L.divisors,‖(jacobiSym (v:ℤ) q:ℂ)/(Real.sqrt (v:ℝ):ℂ)*
          ∑ d ∈ L.divisors,(lam:ℂ)^d.primeFactors.card*(jacobiSym (d:ℤ) q:ℂ)*G d v‖ := norm_sum_le _ _
      _ ≤ ∑ _v ∈ L.divisors,(L.divisors.card:ℝ)*B := by
        apply Finset.sum_le_sum
        intro v hv
        have hv0 := Nat.pos_of_mem_divisors hv
        have hvnorm : ‖(jacobiSym (v:ℤ) q:ℂ)/(Real.sqrt (v:ℝ):ℂ)‖ ≤ 1 := by
          rw [div_eq_mul_inv,norm_mul]
          exact (mul_le_mul (adaptive_jacobi_norm_le v q) (adaptive_sqrt_inv_norm_le hv0)
            (norm_nonneg _) (by norm_num)).trans_eq (by ring)
        rw [norm_mul]
        exact (mul_le_mul hvnorm (hinner v hv) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      _ = _ := by simp; ring
  unfold adaptiveArrayLinear
  rw [norm_mul]
  exact (mul_le_mul (adaptive_sqrt_inv_norm_le hs) houter (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem positiveDivisorArray_eq_linear (L q : ℕ) (lam : ℝ)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ)
    (P : ℕ) (R h θ : ℝ) (s : ℕ) :
    positiveDivisorArray L q lam A mInv P R h θ s =
      adaptiveArrayLinear L q lam s (fun d v => divisorQuadraticSumP d A (mInv d) s v P R h θ) := rfl

end Ostmann.QuadraticCenter

end

end OAI
