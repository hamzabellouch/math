import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.FiniteAtlas
import OAI.AlgebraicGeometry.Seshadri.Projective.AmpleEmbedding

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.BertiniIntegral
attribute [local instance] MvPolynomial.gradedAlgebra

theorem Surface.ample_embedding_option (S : Surface) (L : LineBundle S.scheme)
    (hL : LineBundle.IsAmple S.scheme L) :
    ∃ e : ℕ, 0 < e ∧ ∃ N : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (modulePow S.scheme L.sheaf e),
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) s hs) := by
  classical
  obtain ⟨e, he, N, s, hs, hc⟩ := S.ample_embedding_fin L hL
  let f : Option (Fin N) ≃ Fin (N+1) := (finSuccEquiv N).symm
  have ht : (⨆ i, SectionOpens.isoOpen (s (f i))) = ⊤ :=
    (f.iSup_comp (g := fun j => SectionOpens.isoOpen (s j))).trans hs
  exact ⟨e, he, N, s ∘ f, ht, sectionsMorphism_reindex_closed _ s hs f ht⟩

theorem Surface.ample_smooth_integral_hyperplane (S : Surface) (L : LineBundle S.scheme)
    (hL : LineBundle.IsAmple S.scheme L) :
    ∃ e : ℕ, 0 < e ∧ ∃ N : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (modulePow S.scheme L.sheaf e),
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
        let h := sectionsMorphism
          (S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) s hs
        IsClosedImmersion h ∧ ∀ q : MvPolynomial (Option (Fin N)) ℂ, q ≠ 0 →
          ∃ t : Option (Fin N) → ℂ, MvPolynomial.aeval t q ≠ 0 ∧
            IsIntegral (projectiveHyperplane h t).subscheme ∧
            Smooth ((projectiveHyperplane h t).subschemeι ≫ S.structureMap) := by
  let : Uncountable ℂ := Complex.ofReal_injective.uncountable
  obtain ⟨e, he, N, s, hs, hc⟩ := S.ample_embedding_option L hL
  refine ⟨e, he, N, s, hs, hc, ?_⟩
  intro q hq
  apply MaximalSeshadri.ProjectiveBertini.exists_smooth_integral_projective_hyperplane
    S.scheme S.structureMap _ ?_ q hq
  change _ ≫ projectiveBase = _
  exact (sectionsMorphism_over _ s hs).trans (toSpec_scalarMap S.structureMap)

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
