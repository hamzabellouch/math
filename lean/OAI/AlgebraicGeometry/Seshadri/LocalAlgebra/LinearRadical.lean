import Mathlib

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.Projective
noncomputable section
open MvPolynomial
variable {K σ : Type*} [Field K]

theorem span_isRadical_of_totalDegree_le_one (p : MvPolynomial σ K)
    (hp : p.totalDegree ≤ 1) : (Ideal.span ({p} : Set (MvPolynomial σ K))).IsRadical := by
  by_cases h0 : p.totalDegree = 0
  · rw [(totalDegree_eq_zero_iff_eq_C (p := p)).mp h0]
    by_cases hc : p.coeff 0 = 0
    · simpa only [hc, C_0, Ideal.span_singleton_zero] using
        (Ideal.isRadical_bot : (⊥ : Ideal (MvPolynomial σ K)).IsRadical)
    · have hu : IsUnit (C (p.coeff 0) : MvPolynomial σ K) :=
        (isUnit_iff_ne_zero.mpr hc).map C
      rw [Ideal.span_singleton_eq_top.mpr hu]
      exact le_top
  · have h1 : p.totalDegree = 1 := by omega
    have hirr : Irreducible p := irreducible_of_totalDegree_eq_one h1 (by
      intro x hx
      apply isUnit_iff_ne_zero.mpr
      intro hx0
      have hp0 : p = 0 := by
        ext d
        simpa only [hx0, zero_dvd_iff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hx d
      simp [hp0] at h1)
    exact (Ideal.span_singleton_prime hirr.ne_zero).mpr
      (irreducible_iff_prime.mp hirr) |>.isRadical

end
end MaximalSeshadri.Projective
end


end
end

end OAI
