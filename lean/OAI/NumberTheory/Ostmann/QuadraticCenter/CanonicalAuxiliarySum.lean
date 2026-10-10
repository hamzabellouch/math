import OAI.NumberTheory.Ostmann.QuadraticCenter.CanonicalAuxiliaryFrequency
import OAI.NumberTheory.Ostmann.QuadraticCenter.DivisorGramArithmetic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

lemma canonicalAuxiliary_full_product (F : Finset ℕ) :
    primeSubsetProduct (Finset.univ : Finset F) = ∏ p ∈ F,p := by
  simpa only [primeSubsetProduct] using (Finset.prod_coe_sort F (fun p : ℕ => p))

lemma canonicalAuxiliary_full_squarefree {F : Finset ℕ} (hF : ∀ p ∈ F,Nat.Prime p) :
    Squarefree (∏ p ∈ F,p) := by
  rw [← canonicalAuxiliary_full_product F]
  exact primeSubsetProduct_squarefree hF _

theorem sum_canonicalAuxiliary_subsets {E : Type*} [AddCommMonoid E]
    {F : Finset ℕ} (hF : ∀ p ∈ F,Nat.Prime p) (f : ℕ → E) :
    (∑ U : Finset F,f (primeSubsetProduct U)) =
      ∑ d ∈ (∏ p ∈ F,p).divisors,f d := by
  have h := sum_squarefree_divisors_eq_cube (canonicalAuxiliary_full_squarefree hF) f
  rw [Nat.primeFactors_prod hF] at h
  exact h.symm

theorem amplifierFrequency_eq_canonical_divisors {F : Finset ℕ}
    [∀ p : F, NeZero p.val] (hF : ∀ p ∈ F,Nat.Prime p)
    (hcop : Pairwise (fun p q : F => p.val.Coprime q.val))
    (A : ∀ p : ℕ, Finset (ZMod p)) (lam : ℝ) (q : ℕ) (X a : ℝ) (u : ℤ) :
    amplifierFrequency (fun p : F => p.val) hcop (fun p => A p.val) lam q X a u =
      ∑ d ∈ (∏ p ∈ F,p).divisors,
        ((lam:ℂ)^d.primeFactors.card*(jacobiSym (d:ℤ) q:ℂ) /
          (Real.sqrt (((q:ℝ)/X)*d):ℂ)) *
        divisorFourierFrequency q d A (ZMod.cast ((q:ZMod d)⁻¹)) a ((q:ℝ)/X) u := by
  unfold amplifierFrequency
  simp_rw [subsetAmplifierFrequency_eq_canonical hF hcop A]
  exact sum_canonicalAuxiliary_subsets (E := ℂ) hF
    (fun d => ((lam:ℂ)^d.primeFactors.card*(jacobiSym (d:ℤ) q:ℂ) /
      (Real.sqrt (((q:ℝ)/X)*d):ℂ)) *
      divisorFourierFrequency q d A (ZMod.cast ((q:ZMod d)⁻¹)) a ((q:ℝ)/X) u)

end Ostmann.QuadraticCenter

end

end OAI
