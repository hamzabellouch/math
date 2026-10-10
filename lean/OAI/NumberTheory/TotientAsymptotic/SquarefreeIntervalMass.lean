import OAI.NumberTheory.TotientAsymptotic.PairedSquarefreeMass

namespace OAI

/-! The squarefree interval estimate with an absolute Mertens error. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prime_interval_upper_bounded_error : ∃ D : ℝ,0 < D ∧ ∀ U V : ℝ,
    2 ≤ U → U ≤ V →
    (∑ p ∈ (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ)),(p:ℝ)⁻¹) ≤ B V-B U+D := by
  obtain ⟨d,hd,hbound⟩ := primeReciprocalLE_bounded_error
  refine ⟨2*d,by positivity,?_⟩
  intro U V hU hUV
  have hu := hbound U hU
  have hv := hbound V (hU.trans hUV)
  rw [prime_interval_reciprocal_eq hU hUV]
  linarith [(abs_le.mp hu).1,(abs_le.mp hv).2]

/-- Unlike the general multiplicity bound, the application’s squarefree
product needs no relation between the number of slots and the lower cutoff. -/
theorem squarefree_interval_allocation_bound : ∃ D : ℝ,0 < D ∧
    ∀ (k : ℕ) (U V I : ℝ),1 ≤ k → 2 ≤ U → U ≤ V →
    (k:ℝ)*(B V-B U+D) ≤ I → ∀ Q : Finset (PairedFactors k),
    (∀ f ∈ Q,0 < pairedProduct f ∧ pairedProduct f=∏ j,f.2 j) →
    (∀ f ∈ Q,Squarefree (pairedProduct f)) →
    (∀ f ∈ Q,((pairedProduct f).primeFactorsList.length:ℝ) ≤ I) →
    (∀ f ∈ Q,∀ p ∈ (pairedProduct f).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V) →
    (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹) ≤ Real.exp (I*(Real.log k+1)) := by
  obtain ⟨D,hD,hprime⟩ := prime_interval_upper_bounded_error
  exact ⟨D,hD,fun k U V I hk hU hUV hI Q hQ hsq hΩ hpf =>
    paired_squarefree_allocation_bound k hk hU hUV (hprime U V hU hUV) hI Q hQ hsq hΩ hpf⟩

end TotientAsymptotic

end

end OAI
