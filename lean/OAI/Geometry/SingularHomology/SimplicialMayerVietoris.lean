import OAI.Geometry.SingularHomology.SingularCoverChains

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SimplicialMayerVietoris

abbrev coefficients : ModuleCat ℝ := ModuleCat.of ℝ ℝ

variable {X : SSet} (A B : X.Subcomplex)

abbrev sequence := SingularCover.unionShortComplex A B

def connecting (n : ℕ) :
    (A ⊔ B : X.Subcomplex).toSSet.homology coefficients (n + 1) ⟶
      (A ⊓ B : X.Subcomplex).toSSet.homology coefficients n :=
  (SingularCover.unionShortComplex_shortExact A B).δ (n + 1) n rfl

theorem middle_homology_isZero (n : ℕ)
    (hA : IsZero (A.toSSet.homology coefficients n))
    (hB : IsZero (B.toSSet.homology coefficients n)) :
    IsZero ((sequence A B).X₂.homology n) := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts
    (HomologicalComplex.homologyFunctor (ModuleCat ℝ) (ComplexShape.down ℕ) n)
  change IsZero ((A.toSSet.chainComplex coefficients ⊞
    B.toSSet.chainComplex coefficients).homology n)
  exact IsZero.of_iso ((biprod_isZero_iff _ _).mpr ⟨hA, hB⟩)
    ((HomologicalComplex.homologyFunctor (ModuleCat ℝ) (ComplexShape.down ℕ) n).mapBiprod _ _)

theorem connecting_injective (n : ℕ)
    (hA : IsZero (A.toSSet.homology coefficients (n + 1)))
    (hB : IsZero (B.toSSet.homology coefficients (n + 1))) :
    Function.Injective (connecting A B n) := by
  apply (ModuleCat.mono_iff_injective _).mp
  exact (SingularCover.unionShortComplex_shortExact A B).mono_δ (n + 1) n rfl
    (middle_homology_isZero A B (n + 1) hA hB)

theorem connecting_range (n : ℕ) :
    LinearMap.range (connecting A B n).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (sequence A B).f n).hom := by
  exact ((SingularCover.unionShortComplex_shortExact A B).homology_exact₁ (n + 1) n rfl).moduleCat_range_eq_ker

theorem connecting_kernel (n : ℕ) :
    LinearMap.ker (connecting A B n).hom =
      LinearMap.range (HomologicalComplex.homologyMap (sequence A B).g (n + 1)).hom := by
  exact ((SingularCover.unionShortComplex_shortExact A B).homology_exact₃ (n + 1) n rfl).moduleCat_range_eq_ker.symm

def connectingIso (n : ℕ)
    (hA₁ : IsZero (A.toSSet.homology coefficients (n + 1)))
    (hB₁ : IsZero (B.toSSet.homology coefficients (n + 1)))
    (hA₀ : IsZero (A.toSSet.homology coefficients n))
    (hB₀ : IsZero (B.toSSet.homology coefficients n)) :
    (A ⊔ B : X.Subcomplex).toSSet.homology coefficients (n + 1) ≅
      (A ⊓ B : X.Subcomplex).toSSet.homology coefficients n :=
  (SingularCover.unionShortComplex_shortExact A B).δIso (n + 1) n rfl
    (middle_homology_isZero A B (n + 1) hA₁ hB₁)
    (middle_homology_isZero A B n hA₀ hB₀)

end Problem340.SimplicialMayerVietoris

end

end OAI
