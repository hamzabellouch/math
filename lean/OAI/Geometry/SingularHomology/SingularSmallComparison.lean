import OAI.Geometry.SingularHomology.SingularSmallNaturality
import OAI.Geometry.SingularHomology.SubdivisionQuasiIso
import OAI.Geometry.SingularHomology.SingularAcyclicModels

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.SingularSmallChains

variable {X : Type} [TopologicalSpace X] {ι : Type*} (U : ι → Set X)

theorem inclusion_quasiIso_of_natural_subdivision
    (S : singularFunctor ⟶ singularFunctor)
    (H : ∀ Y : TopCat, Homotopy (S.app Y) (𝟙 (singularFunctor.obj Y)))
    (hH : HomotopyNatural (T := 𝟙 singularFunctor) H)
    (hsmall : ∀ n (z : (realSingularChainComplex X).X n), ∃ k : ℕ,
      (((End.of (S.app (TopCat.of X))) ^ k).asHom.f n).hom z ∈
        LinearMap.range ((inclusion U).f n).hom) : QuasiIso (inclusion U) := by
  apply SubdivisionComparison.quasiIso_of_eventual_iterate_range
    (inclusion U) (inclusion_f_injective U)
    (End.of (S.app (TopCat.of X))) (End.of (restrictChainMap U S))
    (restrictChainMap_inclusion U S).symm (H (TopCat.of X))
  · simpa only [restrictChainMap_id] using restrictHomotopy U (S := S) (T := 𝟙 singularFunctor) H hH
  · intro n z
    obtain ⟨k, x, hx⟩ := hsmall n z
    exact ⟨k, x, hx.symm⟩

def homologyIsoOfNaturalSubdivision
    (S : singularFunctor ⟶ singularFunctor)
    (H : ∀ Y : TopCat, Homotopy (S.app Y) (𝟙 (singularFunctor.obj Y)))
    (hH : HomotopyNatural (T := 𝟙 singularFunctor) H)
    (hsmall : ∀ n (z : (realSingularChainComplex X).X n), ∃ k : ℕ,
      (((End.of (S.app (TopCat.of X))) ^ k).asHom.f n).hom z ∈
        LinearMap.range ((inclusion U).f n).hom)
    (n : ℕ) : (chains U).homology n ≅ RealSingularHomology n X := by
  change (chains U).homology n ≅ (realSingularChainComplex X).homology n
  letI := inclusion_quasiIso_of_natural_subdivision U S H hH hsmall
  letI : IsIso (HomologicalComplex.homologyMap (inclusion U) n) :=
    (quasiIsoAt_iff_isIso_homologyMap (inclusion U) n).mp inferInstance
  exact asIso (HomologicalComplex.homologyMap (inclusion U) n)

theorem inclusion_quasiIso_of_natural_subdivision_zero
    (S : singularFunctor ⟶ singularFunctor)
    (hzero : ∀ Y : TopCat, (S.app Y).f 0 = 𝟙 ((singularFunctor.obj Y).X 0))
    (hsmall : ∀ n (z : (realSingularChainComplex X).X n), ∃ k : ℕ,
      (((End.of (S.app (TopCat.of X))) ^ k).asHom.f n).hom z ∈
        LinearMap.range ((inclusion U).f n).hom) : QuasiIso (inclusion U) := by
  apply inclusion_quasiIso_of_natural_subdivision U S
    (SingularAcyclicModels.homotopyApp S (𝟙 _) hzero) _ hsmall
  intro i j Y Z f
  exact SingularAcyclicModels.homotopyApp_naturality S (𝟙 _) hzero f i j

end Problem340.SingularSmallChains

end

end OAI
