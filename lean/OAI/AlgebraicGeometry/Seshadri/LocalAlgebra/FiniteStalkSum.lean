import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.FiniteScheme
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.ArtinianLength

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {K : Type} [Field K] {X : Scheme}

abbrev structuralStalkAlgebra (f : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    Algebra K (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra

theorem proper_finite_finrank_eq_sum_stalks (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Fintype X] :
    let _ : Algebra K Γ(X,⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    Module.finrank K Γ(X,⊤) = ∑ x : X,
      let _ := structuralStalkAlgebra f x
      Module.finrank K (X.presheaf.stalk x) := by
  classical
  dsimp only
  let : IsAffine X := proper_finite_scheme_isAffine f
  let : Algebra K Γ(X,⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let : FiniteDimensional K Γ(X,⊤) := proper_finite_functions f
  let : IsArtinianRing Γ(X,⊤) := IsArtinianRing.of_finite K Γ(X,⊤)
  let : Fintype (MaximalSpectrum Γ(X,⊤)) := Fintype.ofFinite _
  let e : X ≃ MaximalSpectrum Γ(X,⊤) :=
    (Equiv.Set.univ X).symm.trans ((isAffineOpen_top X).isoSpec.hom.homeomorph.toEquiv.trans
      IsArtinianRing.primeSpectrumEquivMaximalSpectrum)
  rw [IntersectionLength.finrank_eq_sum_localizations Γ(X,⊤) K, ← e.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  let : Algebra Γ(X,⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,trivial⟩ : (⊤ : X.Opens))
  let : Algebra K (X.presheaf.stalk x) := structuralStalkAlgebra f x
  let : IsScalarTower K Γ(X,⊤) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (e x).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x,trivial⟩
  exact ((IsLocalization.algEquiv (e x).asIdeal.primeCompl
    (Localization.AtPrime (e x).asIdeal) (X.presheaf.stalk x)).restrictScalars K).toLinearEquiv.finrank_eq

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
