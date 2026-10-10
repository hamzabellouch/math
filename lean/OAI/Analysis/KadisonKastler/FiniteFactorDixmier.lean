import OAI.Analysis.KadisonKastler.II1Dixmier
import OAI.Analysis.KadisonKastler.TypeICyclicDixmier
import OAI.Analysis.KadisonKastler.TypeIFactorStability
import OAI.Analysis.KadisonKastler.FiniteOperatorAlgebra

namespace OAI

/-! # Dixmier averaging for every represented finite factor -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

/-- Finiteness in a type I factor forces its minimal cyclic representation
to have a finite orthonormal basis. -/
theorem publishedDixmierOfFiniteTypeI (hM : IsTypeIFactor M)
    (hfinite : FiniteProjectionIn M 1) : PublishedDixmierAveraging M := by
  obtain ⟨p, hp⟩ := hM.minimal
  obtain ⟨ξ, hξ, hpξ⟩ := exists_nonzero_fixed_vector p hp.1
  let K := typeICyclicSpace M ξ
  let e := typeICyclicEquiv hM.factor p hp ξ hξ hpξ
  have hK : ∀ v : K →L[ℂ] K, star v * v = 1 → v * star v = 1 := by
    intro v hv
    let a := e.symm v
    have hi : star a * a = 1 := by
      apply e.injective
      rw [map_mul, map_one]
      have hs : e (star a) = star v :=
        (e.map_star' a).trans (congrArg star (e.apply_symm_apply v))
      change e (star a) * e a = 1
      rw [hs, e.apply_symm_apply]
      exact hv
    have ho := hfinite a hi (one_mul _)
    have he := congrArg e ho
    have hs : e (star a) = star v :=
      (e.map_star' a).trans (congrArg star (e.apply_symm_apply v))
    rw [map_mul, map_one] at he
    change e a * e (star a) = 1 at he
    rw [hs, e.apply_symm_apply] at he
    exact he
  let _ : FiniteDimensional ℂ K := finiteDimensional_of_all_isometries_coisometric hK
  exact publishedDixmierOfFiniteTypeICyclic hM.factor p hp ξ hξ hpξ
    (stdOrthonormalBasis ℂ K)

/-- Dixmier averaging on finite factors is independent of their
represented Hilbert-space multiplicity. -/
theorem publishedDixmierOfFiniteFactor (hM : ScalarCenter M)
    (hfinite : FiniteProjectionIn M 1) : PublishedDixmierAveraging M := by
  by_cases ht : IsTypeIFactor M
  · exact publishedDixmierOfFiniteTypeI ht hfinite
  · exact publishedDixmierOfII1 (isII1Factor_of_finite_of_not_typeI hM zero_ne_one hfinite ht)

end

end KadisonKastler

end OAI
