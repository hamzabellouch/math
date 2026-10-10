import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.AmpleBertini
import OAI.AlgebraicGeometry.Seshadri.Projective.CenteredEmbedding
import OAI.AlgebraicGeometry.Seshadri.Projective.QuarticIdealBertini

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

attribute [local instance] MvPolynomial.gradedAlgebra

theorem Surface.ample_quartic_smooth_integral_away (S : Surface)
    (L : LineBundle S.scheme) (hL : LineBundle.IsAmple S.scheme L) :
    ∃ d : ℕ, 0 < d ∧ ∃ N n : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (modulePow S.scheme L.sheaf d),
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
      ∃ e : Option (Fin n) ≃ QuarticIndex (Fin N), ∃ y : S.scheme,
        (∀ x : S.scheme, x ∉ centeredOpen s ↔ x = y) ∧
        IsClosedImmersion (sectionsMorphism
          (S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) s hs) ∧
        ∀ P : MvPolynomial (Option (Fin n)) ℂ, P ≠ 0 →
          ∃ v : Option (Fin n) → ℂ, MvPolynomial.aeval v P ≠ 0 ∧
            let k := S.structureMap.appTop.hom.comp
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
            let V := centeredOpen s
            let J := (doublePointQuarticIdeal k s hs (v ∘ e.symm)).comap V.ι
            IsIntegral J.subscheme ∧ Smooth (J.subschemeι ≫ V.ι ≫ S.structureMap) := by
  classical
  let : Uncountable ℂ := Complex.ofReal_injective.uncountable
  obtain ⟨d, hd, N, s, hs, hc⟩ := S.ample_embedding_option L hL
  let := hc
  obtain ⟨s, hs, hc, y, hy⟩ := exists_centered_embedding
    (S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) s hs
  let := hc
  have hV := centeredOpen_nonempty_of_singleton S.structureMap s y hy
  let : Nonempty (centeredOpen s) := ⟨⟨hV.choose, hV.choose_spec⟩⟩
  let : IsIntegral (centeredOpen s).toScheme := inferInstance
  let : CompactSpace (centeredOpen s) :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (centeredOpen s : Set S.scheme))
  let : SmoothOfRelativeDimension 2 ((centeredOpen s).ι ≫ S.structureMap) := by
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
  have hN : Nonempty (Fin N) := by
    obtain ⟨x, hx⟩ := hV
    obtain ⟨i, _⟩ := Opens.mem_iSup.mp hx
    exact ⟨i⟩
  let := hN
  let Q := QuarticIndex (Fin N)
  have hQ : 0 < Fintype.card Q := Fintype.card_pos
  let n := Fintype.card Q - 1
  have hn : n + 1 = Fintype.card Q := Nat.sub_add_cancel hQ
  let e : Option (Fin n) ≃ Q := (finSuccEquiv n).symm.trans
    ((finCongr hn).trans (Fintype.equivFin Q).symm)
  refine ⟨d, hd, N, n, s, hs, e, y, hy, hc, ?_⟩
  intro P hP
  exact exists_global_quartic_smooth_integral_away S.structureMap s hs e P hP

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
