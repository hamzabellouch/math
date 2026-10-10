import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalMarkLeft

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

theorem naturalPrescription_covariant {ψ : NatSpectralTensor} {n i j : ℕ}
    (hi : i ≤ n) (hj : j < n) (hψ : LowerExchange ψ n) (X : ℕ → ℂ) :
    siteR j (X j) (X (j+1)) (naturalPrescription ψ n i X)=
      exchangeDenominator (X j) (X (j+1)) •
        naturalPrescription ψ n (Equiv.swap j (j+1) i) (swapSite j X) := by
  by_cases hij : i=j
  · subst i
    simpa only [Equiv.swap_apply_left] using naturalPrescription_mark_right hj (ψ:=ψ) X
  by_cases hij' : i=j+1
  · subst i
    simpa only [Equiv.swap_apply_right] using naturalPrescription_mark_left hj (ψ:=ψ) X
  rw [Equiv.swap_apply_of_ne_of_ne hij hij']
  by_cases hlt : i < j
  · exact naturalPrescription_swap_after hlt hj hψ X
  · exact naturalPrescription_swap_before hi (by omega) hψ X

end PolynomialVacuumAlgebra

end OAI
