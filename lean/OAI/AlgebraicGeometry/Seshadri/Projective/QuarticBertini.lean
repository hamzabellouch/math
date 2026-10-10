import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.LocalBertiniSection
import OAI.AlgebraicGeometry.Seshadri.Projective.QuarticReindex

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.BertiniIntegral
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]

theorem doublePointQuartics_bertini {X : Scheme} {M : X.Modules}
    (g : X ⟶ Spec (CommRingCat.of K))
    (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)]
    {n : ℕ} (e : Option (Fin n) ≃ QuarticIndex σ)
    [IsIntegral (centeredOpen s).toScheme] [CompactSpace (centeredOpen s)]
    [SmoothOfRelativeDimension 2 ((centeredOpen s).ι ≫ g)]
    (P : MvPolynomial (Option (Fin n)) K) (hP : P ≠ 0) :
    let k := g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    let V := centeredOpen s
    let t (j : Option σ) := restrictSection V.ι (s j)
    let q := (doublePointQuartics t) ∘ e
    let hq := sections_cover_reindex _ (doublePointQuartics_cover t (restricted_centered_cover s)) e
    let h := sectionsMorphism (V.ι.appTop.hom.comp k) q hq
    ∃ v : Option (Fin n) → K, MvPolynomial.aeval v P ≠ 0 ∧
      IsIntegral (projectiveHyperplane h v).subscheme ∧
      Smooth ((projectiveHyperplane h v).subschemeι ≫ V.ι ≫ g) ∧
      ∀ x : V, ∃ U : V.toScheme.affineOpens, x ∈ U.1 ∧
        ∃ f : Γ(V.toScheme, U.1), IsRegular f ∧
          (projectiveHyperplane h v).ideal U = Ideal.span {f} ∧
          ∃ b : (modulePow V.toScheme (M.restrict V.ι) 4).restrict U.1.ι ≅ O U.1.toScheme,
            U.1.topIso.hom (coefficient b (restrictSection U.1.ι
              (sectionCombination (V.ι.appTop.hom.comp k) q v))) = f := by
  let k := g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let V := centeredOpen s
  let t (j : Option σ) := restrictSection V.ι (s j)
  let q := (doublePointQuartics t) ∘ e
  let hq := sections_cover_reindex _ (doublePointQuartics_cover t (restricted_centered_cover s)) e
  let h := sectionsMorphism (V.ι.appTop.hom.comp k) q hq
  have hbase : h ≫ projectiveToSpec = V.ι ≫ g := by
    change h ≫ projectiveBase = _
    rw [sectionsMorphism_over]
    have hk : V.ι.appTop.hom.comp k = (V.ι ≫ g).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := by
      simp only [k, RingHom.comp_assoc, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    rw [hk, toSpec_scalarMap]
  obtain ⟨v, hv, hi, hsm, heq⟩ :=
    MaximalSeshadri.ProjectiveBertini.exists_smooth_integral_cartier_section_of_local_coordinates
      V.toScheme (V.ι ≫ g) (modulePow V.toScheme (M.restrict V.ι) 4)
      (V.ι.appTop.hom.comp k) q hq h rfl hbase
      (doublePointQuartics_reindexed_local_coordinates k s hs e) P hP
  refine ⟨v, hv, hi, ?_, ?_⟩
  · exact hsm
  · exact heq

end
end MaximalSeshadri.Projective
end


end
end

end OAI
