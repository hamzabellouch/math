import OAI.NumberTheory.Ostmann.Construction.ConstituentFinalComplexity

namespace OAI

/-! # Actual final pair counts at the linear constituent-size scale -/
namespace Ostmann
open scoped Classical

/-- This single constant bounds both the prime-test count and the quadratic
pairwise-coprimality count of the literal final histories. -/
noncomputable def constituentFinalCountRate (N n : ℕ) (s : ℝ) : ℝ :=
  2 * (3 ^ n * N : ℕ) * s * (2 ^ n - 1 : ℕ) + 3 * ((3 ^ n * N : ℕ) * s) ^ 2

theorem constituentFinalCountRate_nonneg (N n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ constituentFinalCountRate N n s := by
  unfold constituentFinalCountRate
  positivity

theorem constituent_final_linear_counts {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (e : Equiv.Perm (SurvivingConstituent role size n))
    (S : ℕ) (s m : ℝ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S)
    (hs : 0 ≤ s) (hm : 0 ≤ m) (hSm : (S : ℝ) ≤ s * (1 + m)) :
    let W := primeWordEmbedding (scheduleConstituentWord role size n)
    let W' := primeWordEmbedding (fun v => List.map e (scheduleConstituentWord role size n v))
    let a := constituentFinalCountRate (Fintype.card I) n s
    (((expandedSchedulePrimes role n n [] (fun i => (W i).map Sum.inl)).count +
      (expandedSchedulePrimes role n n [] (fun i => (W' i).map Sum.inl)).count : ℕ) : ℝ) ≤
        a * (1 + m) ∧
    ((constituentPrimePairChecks (SurvivingConstituent role size n) ++
      atomPairChecks W ++ atomPairChecks W').length : ℝ) ≤ a * (1 + m) ^ 2 := by
  intro W W' a
  have hp := constituent_final_prime_count role size n e S hS hsize
  have hc := constituent_final_top_count role size n e S hsize
  have hrealp : (((expandedSchedulePrimes role n n [] (fun i => (W i).map Sum.inl)).count +
      (expandedSchedulePrimes role n n [] (fun i => (W' i).map Sum.inl)).count : ℕ) : ℝ) ≤
      2 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) : ℝ) * S * (2 ^ n - 1 : ℕ) := by
    calc
      _ ≤ 2 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * S * (2 ^ n - 1 : ℕ)) := by
        exact_mod_cast hp
      _ = _ := by ring
  have hrealc : ((constituentPrimePairChecks (SurvivingConstituent role size n) ++
      atomPairChecks W ++ atomPairChecks W').length : ℝ) ≤
      3 * ((((3 ^ n * Fintype.card I : ℕ) : ℝ) : ℝ) * S) ^ 2 := by
    exact_mod_cast hc
  have ha1 : 2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * s * (2 ^ n - 1 : ℕ) ≤ a := by
    dsimp [a, constituentFinalCountRate]
    linarith [sq_nonneg ((((3 ^ n * Fintype.card I : ℕ) : ℝ) : ℝ) * s)]
  have ha2 : 3 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * s) ^ 2 ≤ a := by
    dsimp [a, constituentFinalCountRate]
    have hh : 0 ≤ 2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * s * (2 ^ n - 1 : ℕ) := by positivity
    linarith
  constructor
  · calc
      _ ≤ 2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * S * (2 ^ n - 1 : ℕ) := hrealp
      _ ≤ 2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * (s * (1 + m)) * (2 ^ n - 1 : ℕ) := by gcongr
      _ = (2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * s * (2 ^ n - 1 : ℕ)) * (1 + m) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ha1 (by linarith)
  · calc
      _ ≤ 3 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * S) ^ 2 := hrealc
      _ ≤ 3 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * (s * (1 + m))) ^ 2 := by gcongr
      _ = (3 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * s) ^ 2) * (1 + m) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ha2 (sq_nonneg _)

end Ostmann

end OAI
