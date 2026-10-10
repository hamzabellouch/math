import OAI.NumberTheory.Ostmann.QuadraticCenter.CanonicalAuxiliaryArrays
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductPositive

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def primeProductArraySum (F : Finset ℕ) [NeZero (∏ p : F, p.val)]
    (A : ∀ p : ℕ, Finset (ZMod p)) (lam X : ℝ) (t : ℕ → ℤ) (B q : ℕ) : ℂ :=
  ∑ P ∈ q.divisors, (-1:ℂ)^P.primeFactors.card *
    ∑ s ∈ (Finset.Icc 1 B).filter (fun s => Squarefree s ∧ s.Coprime (∏ p ∈ F,p)),
      (jacobiSym (s:ℤ) q:ℂ) *
        positiveDivisorArray (∏ p ∈ F,p) q lam A
          (fun d => ZMod.cast ((q:ZMod d)⁻¹)) P ((q:ℝ)/X)
          (centerCorrection q (∏ p : F,p.val) (primeProductCenter q t))
          ((primeProductCenter q t:ℝ)/q) s

theorem primeProductPositive_eq_arrays {F : Finset ℕ}
    [∀ p : F, NeZero p.val] [NeZero (∏ p : F,p.val)]
    (hF : ∀ p ∈ F,Nat.Prime p)
    (hcop : Pairwise (fun p q : F => p.val.Coprime q.val))
    (A : ∀ p : ℕ, Finset (ZMod p)) (lam : ℝ) {q : ℕ} (hq : Squarefree q)
    {X : ℝ} (hX : 0 < X) (t : ℕ → ℤ) (B : ℕ)
    (hB : ((q:ℝ)/X)*(∏ p ∈ F,p) ≤ (B:ℝ)) :
    primeProductPositive (fun p : F => p.val) hcop (fun p => A p.val) lam X t q =
      primeProductArraySum F A lam X t B q := by
  unfold primeProductPositive primeProductArraySum
  rw [add_comm]
  exact amplifier_positive_frequency_eq_canonical_arrays hF hcop A lam hq hX
    (centerCorrection q (∏ p : F,p.val) (primeProductCenter q t))
    ((primeProductCenter q t:ℝ)/q) B hB

theorem amplified_distinct_le_array_mean {F : Finset ℕ}
    [∀ p : F, NeZero p.val] [NeZero (∏ p : F,p.val)]
    (hF : ∀ p ∈ F,Nat.Prime p)
    (hcop : Pairwise (fun p q : F => p.val.Coprime q.val))
    (A : ∀ p : ℕ, Finset (ZMod p)) {lam X : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam < 1) (hX : 0 < X)
    (P : Finset ℕ) (hP : ∀ r ∈ P,Nat.Prime r) (ho : ∀ r ∈ P,Odd r)
    (hc : ∀ r ∈ P,r.Coprime (∏ p : F,p.val)) (hJ : 0 < P.card)
    (ε t : ℕ → ℤ) (hε : ∀ r ∈ P,ε r = -1 ∨ ε r = 1)
    {k : ℕ} (hk : 0 < k) (hkJ : k ≤ P.card) (B : ℕ)
    (hB : ∀ q ∈ primeProductSamples P k, ((q:ℝ)/X)*(∏ p ∈ F,p) ≤ (B:ℝ)) :
    (∑' n : ℤ, amplifierWeight (fun p : F => p.val) hcop (fun p => A p.val) lam X n *
      distinctSignAverage P (fun r => ε r * jacobiSym (n - t r) r) k) / Real.sqrt X ≤
      2 * primeProductMean P k (fun q => ‖primeProductArraySum F A lam X t B q‖) := by
  apply (amplified_distinct_le_positive_mean (fun p : F => p.val) hcop
    (fun p => A p.val) hlam hlam1 hX P hP ho hc hJ ε t hε hk hkJ).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply primeProductMean_mono
  intro q hq
  rw [primeProductPositive_eq_arrays hF hcop A lam
    (primeProductSamples_poisson_data hP ho hc hk hq).1 hX t B (hB q hq)]

end Ostmann.QuadraticCenter

end

end OAI
