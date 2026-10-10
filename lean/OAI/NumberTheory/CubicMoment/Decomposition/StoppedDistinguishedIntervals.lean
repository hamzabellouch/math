import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedCollection

namespace OAI

/-! The actual distinguished-coordinate stopping region is the
intersection of four norm bounds. All surrogate products here are
computed from the fixed selected divisor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma geometricPrimeSurrogate_pos {ρ B : ℝ} (hρ : 0 < ρ)
    (S : Finset Eisenstein) (bin : Eisenstein → ℕ) :
    0 < primeSurrogate S bin (geometricBinLower ρ B) := by
  unfold primeSurrogate
  exact Finset.prod_pos (fun p _ => pow_pos hρ _)

theorem stopped_distinguished_interval_iff {B ρ a b : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) {j j₀ k h : ℕ}
    (hj : j < geometricBinCount ρ B) (Z Q : ℝ) (early : Bool)
    {c d p : Eisenstein} (hc : primary c) (hd : primary d)
    (hp : primaryPrime p) (hpB : norm p ≤ B) :
    let S := primeSurrogate (primaryPrimeFactors d) (geometricPrimeBin ρ B) (geometricBinLower ρ B)
    let E := primeSurrogate (primeBinPrefix (primaryPrimeFactors d) (geometricPrimeBin ρ B) h)
      (geometricPrimeBin ρ B) (geometricBinLower ρ B)
    let P := geometricBinLower ρ B j
    (geometricPrimeBin ρ B p = j ∧
      (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
      stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early (c*p) d) ↔
    ((∀ q ∈ primaryPrimeFactors d, geometricPrimeBin ρ B q ≤ j₀) ∧
      (primeBin (primaryPrimeFactors d) (geometricPrimeBin ρ B) j₀).card = k) ∧
      (a/norm (c*d) < norm p ∧
      max P (Z/(norm c*S)) ≤ norm p ∧
      norm p < min (ρ*P) (min (Z*geometricBinLower ρ B j₀/(norm c*S))
        (if early = true then ρ*P else Q/(norm c*E))) ∧
      norm p ≤ b/norm (c*d)) := by
  dsimp only
  have hS := geometricPrimeSurrogate_pos (B := B) (zero_lt_one.trans hρ)
    (primaryPrimeFactors d) (geometricPrimeBin ρ B)
  have hE := geometricPrimeSurrogate_pos (B := B) (zero_lt_one.trans hρ)
    (primeBinPrefix (primaryPrimeFactors d) (geometricPrimeBin ρ B) h) (geometricPrimeBin ρ B)
  have hnorm : (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ↔
      a/norm (c*d) < norm p ∧ norm p ≤ b/norm (c*d) := by
    rw [mul_assoc]
    exact selectedPrime_norm_interval (primary_ne_zero hc) (primary_ne_zero hd) p a b
  rw [geometricPrimeBin_eq_iff hρ hρ₂ hj hp hpB,hnorm,
    stoppedSideTest_free_distinguished_interval (geometricPrimeBin ρ B) (geometricBinLower ρ B)
      j₀ k h Z Q early (primary_ne_zero hc) d p (pow_pos (zero_lt_one.trans hρ) _) hS hE]
  by_cases hearly : early = true
  · simp only [hearly,true_or,ite_true,max_le_iff,lt_min_iff]
    tauto
  · simp only [hearly,max_le_iff,lt_min_iff]
    tauto

end CubicFirstMoment

end

end OAI
