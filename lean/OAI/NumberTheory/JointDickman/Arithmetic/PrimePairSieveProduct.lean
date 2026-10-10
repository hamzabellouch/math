import OAI.NumberTheory.JointDickman.Arithmetic.PrimePairSieveCount
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeNormalizerUpper

namespace OAI

/-! # The logarithm-squared denominator of the prime-pair sieve -/
namespace JointDickman
open Finset

lemma primePair_sieve_product_bound : ∃ A : ℝ, 0 < A ∧ ∀ Z : ℕ, 3 ≤ Z →
    (∏ p ∈ (Nat.primesLE Z).filter (fun p => 3 < p), (1-1/(p:ℝ))) ≤ A/Real.log Z := by
  obtain ⟨A,hA,hbound⟩ := primeNormalizer_upper primeReciprocalMertensInput
  refine ⟨A*Real.log 3,by positivity,?_⟩
  intro Z hZ
  have he : largePrimeSet (Z:ℝ) 3 = (Nat.primesLE Z).filter (fun p => 3 < p) := by
    ext p
    simp only [largePrimeSet,Nat.floor_natCast,mem_filter]
    exact and_congr_right (fun _ => by exact_mod_cast (Iff.rfl : 3 < p ↔ 3 < p))
  have hh := hbound 3 Z 1 (by norm_num) (by exact_mod_cast hZ) (by norm_num) (by norm_num)
  simpa only [primeNormalizer,he,Real.rpow_one,mul_div_assoc] using hh

theorem primePair_count_sieve_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Q Z h : ℕ, 3 ≤ Z → 0 < h →
      (primePairCount Q h:ℝ) ≤
        C*(Q+1:ℝ)*((h:ℝ)/h.totient)/(Real.log Z)^2 +
        2*(Z+1:ℝ)*(Z:ℝ)^2+(Z+1:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := primePair_count_sieve_bound
  obtain ⟨A,hA,hproduct⟩ := primePair_sieve_product_bound
  refine ⟨C*A^2,by positivity,?_⟩
  intro Q Z h hZ hh
  have hlog : 0 < Real.log Z := Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hprod0 : 0 ≤ ∏ p ∈ (Nat.primesLE Z).filter (fun p => 3 < p), (1-1/(p:ℝ)) := by
    apply prod_nonneg
    intro p hp
    have hp3 : (3:ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr (by linarith))
  have hsq := (sq_le_sq₀ hprod0 (by positivity : 0 ≤ A/Real.log Z)).mpr (hproduct Z hZ)
  calc
    _ ≤ C*(Q+1:ℝ)*((h:ℝ)/h.totient)*
        (∏ p ∈ (Nat.primesLE Z).filter (fun p => 3 < p), (1-1/(p:ℝ)))^2 +
        2*(Z+1:ℝ)*(Z:ℝ)^2+(Z+1:ℝ) := hbound Q Z h hZ hh
    _ ≤ C*(Q+1:ℝ)*((h:ℝ)/h.totient)*(A/Real.log Z)^2 +
        2*(Z+1:ℝ)*(Z:ℝ)^2+(Z+1:ℝ) := by
      gcongr
    _ = _ := by ring

end JointDickman

end OAI
