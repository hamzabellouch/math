import OAI.NumberTheory.Jacobsthal.Estimates.NonstructuredCounts

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseStructured
open ErdosSourceCollision ErdosLineCollision ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem prime_sum_partition_le {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (a : ℕ → ℤ) (f : ℕ → ℝ) (hf : ∀ p ∈ P,0 ≤ f p) :
    (∑ p ∈ P,f p) ≤ (∑ p ∈ unalignedPrimes P a r,f p)+(∑ p ∈ ignoredPrimes P l.denominator,f p)+
      ∑ p ∈ P.filter (aligns a r.rational),f p := by
  calc
    _ ≤ ∑ p ∈ P,((if ¬p ∣ l.denominator ∧ ¬aligns a r.rational p then f p else 0)+
        (if p ∣ l.denominator then f p else 0)+(if aligns a r.rational p then f p else 0)) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hd : p ∣ l.denominator <;> by_cases ha : aligns a r.rational p <;>
        simp [hd,ha]
      linarith [hf p hp]
    _ = _ := by simp only [unalignedPrimes,ignoredPrimes,Finset.sum_filter,Finset.sum_add_distrib]

theorem many_aligners_of_richness {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (c eps : ℝ) (hN : 0 < X.card)
    (hrich : c*(P.card : ℝ)*(X.card : ℝ) ≤ ∑ p ∈ P,((incidentPoints X (a p) p (T p)).card : ℝ))
    (hbad : (∑ p ∈ unalignedPrimes P a r,((incidentPoints X (a p) p (T p)).card : ℝ))+
      (∑ p ∈ ignoredPrimes P l.denominator,((incidentPoints X (a p) p (T p)).card : ℝ)) ≤
      eps*(P.card : ℝ)*(X.card : ℝ)) :
    (c-eps)*(P.card : ℝ) ≤ ((P.filter (aligns a r.rational)).card : ℝ) := by
  have hp := prime_sum_partition_le r P a
    (fun p => ((incidentPoints X (a p) p (T p)).card : ℝ)) (fun _ _ => Nat.cast_nonneg _)
  have ha := total_incidence_le_product (P.filter (aligns a r.rational)) X a T
  have hNp : (0 : ℝ) < X.card := by exact_mod_cast hN
  have hh : ((c-eps)*(P.card : ℝ))*(X.card : ℝ) ≤
      ((P.filter (aligns a r.rational)).card : ℝ)*(X.card : ℝ) := by linarith
  exact le_of_mul_le_mul_right hh hNp

theorem intercept_mem_fixed_list {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (a : ℕ → ℤ) (S R Z cp : ℝ) (hS : 0 ≤ S) (hR : 0 ≤ R)
    (hden : (l.denominator : ℝ) ≤ R*Z^10) (hnum : |(l.intercept : ℝ)| ≤ S*R*Z^10)
    (halign : cp*(P.card : ℝ) ≤ ((P.filter (aligns a r.rational)).card : ℝ)) :
    r.rational ∈ sourceRationalList P a S R Z cp := by
  have hh := r.height_transfer (R*Z^10) (S*R*Z^10) hden hnum
  apply (mem_sourceRationalList P a hS hR r.rational).mpr
  refine ⟨?_,hh.1,halign⟩
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hh.2

end ErdosInverseStructured

end

end Erdos970

end OAI
