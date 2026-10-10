import OAI.Algebra.AuslanderReiten.Cones.MappingConeTotal
import OAI.Algebra.AuslanderReiten.Cones.ConeCohomology
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomExt

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CompleteComparison
open CochainComplex CochainComplex.HomComplex

universe u

variable {k R : Type u} [CommRing k] [Ring R] [Algebra k R]
variable {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)

abbrev ConeModule := Cokernel (chainOfCochain (mappingCone φ)) 0

include k

theorem coneModule_properties
    (hF : TotallyAcyclicCochain F) (hG : TotallyAcyclicCochain G)
    (hzero : ∀ n (x : Cochain G F n), x = 0)
    (hinj : ∀ n : ℕ, 0 < n → Function.Injective (coneComparison φ (n : ℤ)))
    (hsurj : ∀ n : ℕ, Function.Surjective (coneComparison φ (n : ℤ)))
    (hker : ∃ w : CohomologyClass G G 0 × CohomologyClass F F 0,
      w ≠ 0 ∧ coneComparison φ 0 w = 0) :
    ¬ Module.Projective R (ConeModule φ) ∧
      GorensteinProjective R (ConeModule φ) ∧
      PositiveExtVanish R (ConeModule φ) (ConeModule φ) ∧
      PositiveExtVanish R (ConeModule φ) R := by
  have hC := (mappingCone_totallyAcyclic φ hF hG).to_chain
  have hgp := mappingCone_cokernel_gorenstein φ hF hG
  have hpos (n : ℕ) (hn : 0 < n) :
      Subsingleton (CohomologyClass (mappingCone φ) (mappingCone φ) (n : ℤ)) := by
    apply coneEnd_cohomology_subsingleton φ (n : ℤ) hzero (hinj n hn)
    have hi : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
    rw [hi]
    exact hsurj (n - 1)
  obtain ⟨w, hw, hcomp⟩ := hker
  exact ⟨not_projective_of_fullHom_nontrivial (k := k) hC
      (coneEnd_nontrivial_of_kernel φ 0 hzero w hw hcomp),
    hgp, positiveExtVanish_of_fullHom (k := k) hC hC.toExactProjectiveComplex hpos,
    hgp.positiveExt_regular⟩

end ArExplicit

end

end OAI
