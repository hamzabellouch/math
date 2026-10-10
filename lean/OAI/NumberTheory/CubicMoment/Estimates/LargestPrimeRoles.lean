import OAI.NumberTheory.CubicMoment.Estimates.LargestPrimeSelection
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCoefficients

namespace OAI

/-! The largest prime of a squarefree stopped product occurs on exactly
one side. This is the exact split into distinguished and selected-bin
roles before reindexing the free prime. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_factor_unique_side {p r d : Eisenstein} (hp : Prime p)
    (hs : Squarefree (r*d)) (hd : p ∣ r*d) :
    (p ∣ r ∧ ¬p ∣ d) ∨ (p ∣ d ∧ ¬p ∣ r) := by
  have hcop : IsCoprime r d :=
    isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hs).1
  rcases hp.dvd_or_dvd hd with hr | hd
  · exact Or.inl ⟨hr,fun hd => hp.not_isUnit (hcop.isUnit_of_dvd' hr hd)⟩
  · exact Or.inr ⟨hd,fun hr => hp.not_isUnit (hcop.isUnit_of_dvd' hr hd)⟩

theorem stoppedBeta_largest_roles (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) (selected : Eisenstein → Eisenstein → Prop)
    {b : Eisenstein} (hb : primary b) (hs : Squarefree b)
    (hne : (primaryPrimeFactors b).Nonempty) :
    let p := selectedLargestPrime (primaryPrimeFactors b) hne
    stoppedBeta R D v ψ w selected b =
      (∑ t ∈ primaryPairFiber R D b,
        if selected t.1 t.2 ∧ p ∣ t.1 then v t.1*cutoffMoebius ψ w t.2 else 0)+
      (∑ t ∈ primaryPairFiber R D b,
        if selected t.1 t.2 ∧ p ∣ t.2 then v t.1*cutoffMoebius ψ w t.2 else 0) := by
  dsimp only
  let p := selectedLargestPrime (primaryPrimeFactors b) hne
  have hp := primaryPrimeFactor_spec hb (selectedLargestPrime_spec (primaryPrimeFactors b) hne).1
  unfold stoppedBeta primaryPairCoefficient
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have he : t.1*t.2 = b := (Finset.mem_filter.mp ht).2
  have hs' : Squarefree (t.1*t.2) := he.symm ▸ hs
  have hd : p ∣ t.1*t.2 := by
    rw [he]
    exact hp.2
  rcases prime_factor_unique_side hp.1.2 hs' hd with ⟨hr,hnd⟩ | ⟨hd,hnr⟩
  · by_cases h : selected t.1 t.2 <;> simp only [h,hr,hnd,and_true,and_false,
      ite_true,ite_false,add_zero]
  · by_cases h : selected t.1 t.2 <;> simp only [h,hd,hnr,and_true,and_false,
      ite_true,ite_false,zero_add]

end CubicFirstMoment

end

end OAI
