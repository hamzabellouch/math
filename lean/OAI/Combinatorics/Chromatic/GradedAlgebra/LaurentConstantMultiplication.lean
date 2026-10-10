import Mathlib

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries Finset
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma coeff_mul_zero_sub_mem (J : Submodule ℚ R) (f g : LaurentSeries R)
    (h : ∀ i j : ℤ, i+j=0 → (i,j)≠(0,0) → f.coeff i*g.coeff j∈J) :
    (f*g).coeff 0-f.coeff 0*g.coeff 0∈J := by
  classical
  apply (Submodule.Quotient.eq J).mp
  change J.mkQ ((f*g).coeff 0)=J.mkQ (f.coeff 0*g.coeff 0)
  rw [coeff_mul,map_sum]
  apply Finset.sum_eq_single (0,0)
  · intro ij hij hne
    apply (Submodule.Quotient.mk_eq_zero J).mpr
    exact h ij.1 ij.2 (mem_antidiagonal.mp hij).2.2 hne
  · intro hn
    have hz : f.coeff 0=0 ∨ g.coeff 0=0 := by
      by_contra hc
      push Not at hc
      exact hn (mem_antidiagonal.mpr ⟨hc.1,hc.2,by simp⟩)
    rcases hz with hf|hg
    · simp only [hf,zero_mul,map_zero]
    · simp only [hg,mul_zero,map_zero]

lemma coeff_mul_zero_sub_mem_of_positive (J : Submodule ℚ R) (f g : LaurentSeries R)
    (h : ∀ i j : ℤ, (0 < i ∨ 0 < j) → f.coeff i*g.coeff j∈J) :
    (f*g).coeff 0-f.coeff 0*g.coeff 0∈J := by
  apply coeff_mul_zero_sub_mem J f g
  intro i j hij hne
  apply h i j
  have hn : i≠0 ∨ j≠0 := by simpa only [ne_eq,Prod.mk.injEq,not_and_or] using hne
  omega

end ElementaryPositivity.LaurentAtInfinity

end

end OAI
