import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDistinguishedFull
import OAI.NumberTheory.CubicMoment.Estimates.SelectedPrimeGeometry

namespace OAI

/-! The original distinguished-coordinate conditions are exactly the
free-prime row conditions, including squarefreeness and the exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma distinguished_prime_product_conditions (c p d e : Eisenstein)
    (hp : primaryPrime p) :
    (Squarefree ((c*p)*d) ∧ IsCoprime ((c*p)*d) e) ↔
      Squarefree (c*d) ∧ IsCoprime (c*d) e ∧ IsCoprime p (c*(d*e)) := by
  have he : (c*p)*d = c*(p*d) := by ring
  have hf : d*(c*e) = c*(d*e) := by ring
  rw [he]
  simpa only [hf] using selectedPrime_product_conditions c p d e hp

lemma distinguished_largest_prime_iff {c p d : Eisenstein}
    (hc : primary c) (hp : primaryPrime p) (hd : primary d)
    (hs : Squarefree ((c*p)*d)) :
    largestPrimeChoice ((c*p)*d) = p ↔
      largestPrimePredicate primeTieCode (primaryPrimeFactors (c*d)) p := by
  have he : (c*p)*d = p*(c*d) := by ring
  rw [he] at hs ⊢
  have hcop : IsCoprime p (c*d) :=
    isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hs).1
  exact largestPrimeChoice_mul_eq_iff hp (primary_mul hc hd)
    (squarefree_mul_iff.mp hs).2.2
    (fun hdiv => hp.2.not_isUnit (hcop.isUnit_of_dvd hdiv))

lemma distinguished_prime_row_conditions {B ρ a b : ℝ} {j j₀ k h : ℕ}
    {Z Q : ℝ} {early : Bool} {c d e p : Eisenstein}
    (hc : primary c) (hd : primary d) (hp : p ∈ primeCutoff B) :
    (Squarefree ((c*p)*d) ∧ IsCoprime ((c*p)*d) e ∧
      (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
      stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
        j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B p = j ∧
      largestPrimeChoice ((c*p)*d) = p) ↔
    (Squarefree (c*d) ∧ IsCoprime (c*d) e ∧
      p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e))) := by
  constructor
  · rintro ⟨hs,hcop,hint,hstop,hbin,hlarge⟩
    obtain ⟨hscd,hcde,hpe⟩ := (distinguished_prime_product_conditions c p d e
      (mem_primeCutoff.mp hp).1).mp ⟨hs,hcop⟩
    refine ⟨hscd,hcde,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hp,hpe⟩,?_⟩,hbin,hint,hstop⟩⟩
    exact (distinguished_largest_prime_iff hc (mem_primeCutoff.mp hp).1 hd hs).mp hlarge
  · rintro ⟨hscd,hcde,hrow⟩
    obtain ⟨hp',hbin,hint,hstop⟩ := Finset.mem_filter.mp hrow
    obtain ⟨hp',hl⟩ := Finset.mem_filter.mp hp'
    obtain ⟨_,hpe⟩ := Finset.mem_filter.mp hp'
    obtain ⟨hs,hcop⟩ := (distinguished_prime_product_conditions c p d e
      (mem_primeCutoff.mp hp).1).mpr ⟨hscd,hcde,hpe⟩
    exact ⟨hs,hcop,hint,hstop,hbin,
      (distinguished_largest_prime_iff hc (mem_primeCutoff.mp hp).1 hd hs).mpr hl⟩

lemma stoppedDistinguished_complement_bound {B ρ a b : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) {j j₀ k h : ℕ}
    (hj : j < geometricBinCount ρ B) {Z Q : ℝ} {early : Bool}
    {c d e p : Eisenstein} (hc : primary c) (hd : primary d)
    (hp : p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e) :
    norm (c*d) ≤ b/geometricBinLower ρ B j := by
  obtain ⟨hp',hbin,hint,_⟩ := Finset.mem_filter.mp hp
  have hpB := mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp').1).1
  have hnorm := (geometricPrimeBin_eq_iff hρ hρ₂ hj hpB.1 hpB.2).mp hbin
  have hn : 0 < norm (c*d) := norm_pos_of_ne_zero
    (mul_ne_zero (primary_ne_zero hc) (primary_ne_zero hd))
  apply (le_div_iff₀ (zero_lt_one.trans (geometricBinLower_gt_one hρ hj))).mpr
  calc
    norm (c*d)*geometricBinLower ρ B j ≤ norm (c*d)*norm p :=
      mul_le_mul_of_nonneg_left hnorm.1 hn.le
    _ = norm ((c*p)*d) := by simp only [norm_mul_eq]; ring
    _ ≤ b := hint.2

end CubicFirstMoment

end

end OAI
