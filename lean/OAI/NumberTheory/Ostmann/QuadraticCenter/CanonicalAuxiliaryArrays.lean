import OAI.NumberTheory.Ostmann.QuadraticCenter.CanonicalAuxiliarySum

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem divisorFourierFrequency_positive_summable (q d : ℕ)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℤ) (a : ℝ) {R : ℝ} (hR : 0 < R) :
    Summable (fun n : ℕ => divisorFourierFrequency q d A mInv a R ((n:ℤ)+1)) := by
  apply (divisorFourierFrequency_summable q d A mInv a hR).comp_injective
  intro m n h
  exact_mod_cast (add_right_cancel h)

theorem amplifier_positive_frequency_eq_canonical_arrays {F : Finset ℕ}
    [∀ p : F, NeZero p.val] (hF : ∀ p ∈ F,Nat.Prime p)
    (hcop : Pairwise (fun p q : F => p.val.Coprime q.val))
    (A : ∀ p : ℕ, Finset (ZMod p)) (lam : ℝ) {q : ℕ} (hq : Squarefree q)
    {X : ℝ} (hX : 0 < X) (h θ : ℝ) (B : ℕ)
    (hB : ((q:ℝ)/X)*(∏ p ∈ F,p) ≤ (B:ℝ)) :
    (∑' n : ℕ,
      amplifierFrequency (fun p : F => p.val) hcop (fun p => A p.val)
        lam q X (h+θ) ((n:ℤ)+1)) =
      ∑ P ∈ q.divisors, (-1:ℂ)^P.primeFactors.card *
        ∑ s ∈ (Finset.Icc 1 B).filter
            (fun s => Squarefree s ∧ s.Coprime (∏ p ∈ F,p)),
          (jacobiSym (s:ℤ) q:ℂ) *
            positiveDivisorArray (∏ p ∈ F,p) q lam A
              (fun d => ZMod.cast ((q:ZMod d)⁻¹)) P ((q:ℝ)/X) h θ s := by
  classical
  have hR : 0 < (q:ℝ)/X := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hq.ne_zero) hX
  simp_rw [amplifierFrequency_eq_canonical_divisors hF hcop A]
  rw [Summable.tsum_finsetSum (fun d _ =>
    (divisorFourierFrequency_positive_summable q d A
      (ZMod.cast ((q:ZMod d)⁻¹)) (h+θ) hR).mul_left
      ((lam:ℂ)^d.primeFactors.card*(jacobiSym (d:ℤ) q:ℂ) /
        (Real.sqrt (((q:ℝ)/X)*d):ℂ)))]
  simp only [tsum_mul_left]
  exact divisor_positive_frequency_eq_array (canonicalAuxiliary_full_squarefree hF)
    hq lam A (fun d => ZMod.cast ((q:ZMod d)⁻¹)) h θ hR B hB

end Ostmann.QuadraticCenter

end

end OAI
