import Mathlib

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {K : Type} [Field K] {X Y : Scheme}

lemma proper_finite_scheme_isFinite (f : X ⟶ Y) [IsProper f] [Finite X] : IsFinite f := by
  let : LocallyQuasiFinite f := .of_finite_preimage_singleton f (fun _ => Set.toFinite _)
  exact .of_isProper_of_locallyQuasiFinite f

lemma proper_finite_scheme_isAffine (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] : IsAffine X := by
  let : IsFinite f := proper_finite_scheme_isFinite f
  exact isAffine_of_isAffineHom f

lemma proper_finite_functions (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] :
    let _ : Algebra K Γ(X,⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    FiniteDimensional K Γ(X,⊤) := by
  let : IsFinite f := proper_finite_scheme_isFinite f
  dsimp only
  exact f.finite_appTop.comp (RingHom.Finite.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (by
      exact (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective))

lemma proper_finite_germ_surjective (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] (x : X) :
    Function.Surjective (X.presheaf.germ ⊤ x trivial) := by
  let : IsAffine X := proper_finite_scheme_isAffine f
  let : Algebra K Γ(X,⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let : FiniteDimensional K Γ(X,⊤) := proper_finite_functions f
  let : IsArtinianRing Γ(X,⊤) := IsArtinianRing.of_finite K Γ(X,⊤)
  let : Algebra Γ(X,⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,trivial⟩ : (⊤ : X.Opens))
  let : IsLocalization.AtPrime (X.presheaf.stalk x)
      ((isAffineOpen_top X).primeIdealOf ⟨x,trivial⟩).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x,trivial⟩
  exact IsArtinianRing.localization_surjective
    ((isAffineOpen_top X).primeIdealOf ⟨x,trivial⟩).asIdeal.primeCompl (X.presheaf.stalk x)

theorem proper_finite_stalk_finrank_le (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] (x : X) :
    let _ : Algebra K Γ(X,⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    let _ : Algebra Γ(X,⊤) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,trivial⟩ : (⊤ : X.Opens))
    let _ : Algebra K (X.presheaf.stalk x) :=
      ((algebraMap Γ(X,⊤) (X.presheaf.stalk x)).comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
    FiniteDimensional K (X.presheaf.stalk x) ∧
      Module.finrank K (X.presheaf.stalk x) ≤ Module.finrank K Γ(X,⊤) := by
  dsimp only
  let : Algebra K Γ(X,⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let : Algebra Γ(X,⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,trivial⟩ : (⊤ : X.Opens))
  let : Algebra K (X.presheaf.stalk x) :=
    ((algebraMap Γ(X,⊤) (X.presheaf.stalk x)).comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
  let : IsScalarTower K Γ(X,⊤) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional K Γ(X,⊤) := proper_finite_functions f
  let φ := (IsScalarTower.toAlgHom K Γ(X,⊤) (X.presheaf.stalk x)).toLinearMap
  have hφ : Function.Surjective φ := proper_finite_germ_surjective f x
  exact ⟨Module.Finite.of_surjective φ hφ, φ.finrank_le_finrank_of_surjective hφ⟩

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
