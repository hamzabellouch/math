import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.SectionMaps
import OAI.AlgebraicGeometry.Seshadri.Divisors.LinearSections

namespace OAI

section
noncomputable section
                                           
section
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K σ : Type u} [CommRing K] [Fintype σ] {X : Scheme.{u}}

lemma coordinatesMap_hyperplane (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) (t : σ → K) :
    coordinatesMap X k a i hi ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (linearEquation t) =
      X.basicOpen (∑ j, k (t j) * a j) := by
  rw [coordinatesMap, Scheme.Hom.comp_preimage,
    fromUnitCoordinate_preimage _ (coordinates_X_mem (K := K) i) _
      (by simpa only [MvPolynomial.eval₂Hom_X'] using hi) (by decide)
      (linearEquation_homogeneous t)]
  simp only [linearEquation, map_sum, map_mul, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', Scheme.toSpecΓ_preimage_basicOpen]

def sectionCombination {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (t : σ → K) : O X ⟶ M :=
  ∑ j, scalarEnd (k (t j)) ≫ s j

theorem sectionsMorphism_hyperplane {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (t : σ → K) :
    sectionsMorphism k s hcover ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (linearEquation t) =
      SectionOpens.isoOpen (sectionCombination k s t) := by
  classical
  ext x
  have hx : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let U := SectionOpens.isoOpen (s i)
  have H : U.ι ⁻¹ᵁ (sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (PolyGrade K σ) (linearEquation t)) =
      U.ι ⁻¹ᵁ SectionOpens.isoOpen (sectionCombination k s t) := by
    rw [← Scheme.Hom.comp_preimage, sectionsMorphism_local,
      coordinatesMap_hyperplane, preimage_isoOpen (sectionCombination k s t) U.ι
        (sectionFrame (s i))]
    congr 1
    simp only [sectionCombination, restrictSection_sum, coefficient_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact (coefficient_restrict_scalar_comp U.ι (sectionFrame (s i)) (k (t j)) (s j)).symm
  exact Set.ext_iff.mp (congrArg SetLike.coe H) (⟨x, hi⟩ : U.toScheme)

end
end MaximalSeshadri.Projective

end


end
end

end OAI
