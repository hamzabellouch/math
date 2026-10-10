import OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine
import OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange
import OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ClosedPushforward

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

lemma sections_empty (M : X.Modules) (U : X.Opens) (hU : U = ⊥) :
    Subsingleton (M.val.obj (op U)) := by
  exact AddCommGrpCat.subsingleton_of_isZero
    (TopCat.Sheaf.isTerminalOfEqEmpty ((SheafOfModules.toSheaf.{0} X.ringCatSheaf).obj M) hU).isZero

lemma map_epi (f : X ⟶ Y) [IsClosedImmersion f] {M N : X.Modules}
    (φ : M ⟶ N) [Epi φ] : Epi ((Scheme.Modules.pushforward f).map φ) := by
  let FX := SheafOfModules.toSheaf.{0} X.ringCatSheaf
  let FY := SheafOfModules.toSheaf.{0} Y.ringCatSheaf
  let S := ShortComplex.mk _ _ (kernel.condition φ)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel φ }
  have hepi : Epi (FX.map φ) := (ModuleSheafExact.shortExact_map X.ringCatSheaf hS).epi_g
  have hφ : TopCat.Presheaf.IsLocallySurjective (FX.map φ).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mpr hepi
  have hloc : TopCat.Presheaf.IsLocallySurjective
      (FY.map ((Scheme.Modules.pushforward f).map φ)).hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro U t y hy
    by_cases him : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := him
      obtain ⟨W,hWU,⟨s,hs⟩,hxW⟩ :=
        (TopCat.Presheaf.isLocallySurjective_iff _).mp hφ (f ⁻¹ᵁ U) t x hy
      obtain ⟨V',hV',hpre⟩ := f.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp W.isOpen
      let V : Y.Opens := ⟨V', hV'⟩ ⊓ U
      have hV : f ⁻¹ᵁ V = W := by
        ext z
        change (f z ∈ V' ∧ f z ∈ U) ↔ z ∈ W
        have hh : f z ∈ V' ↔ z ∈ W := Set.ext_iff.mp hpre z
        exact ⟨fun h => hh.mp h.1, fun h => ⟨hh.mpr h,hWU h⟩⟩
      refine ⟨V,inf_le_right,?_,?_,⟩
      · change ∃ s, (φ.val.app (op (f ⁻¹ᵁ V))) s =
          N.val.map ((Opens.map f.base).map (homOfLE inf_le_right)).op t
        subst W
        exact ⟨s,hs⟩
      · exact ⟨(Set.ext_iff.mp hpre x).mpr hxW,hy⟩
    · let V : Y.Opens := U ⊓ ⟨(Set.range f)ᶜ, f.isClosedEmbedding.isClosed_range.isOpen_compl⟩
      have hV : f ⁻¹ᵁ V = ⊥ := by
        ext x
        change (f x ∈ U ∧ f x ∉ Set.range f) ↔ False
        simp
      have := sections_empty N (f ⁻¹ᵁ V) hV
      refine ⟨V,inf_le_left,⟨0,?_⟩,⟨hy,him⟩⟩
      exact @Subsingleton.elim (N.val.obj (op (f ⁻¹ᵁ V))) (sections_empty N _ hV) _ _
  let : Epi (FY.map ((Scheme.Modules.pushforward f).map φ)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hloc
  exact FY.epi_of_epi_map inferInstance

instance preservesEpis (f : X ⟶ Y) [IsClosedImmersion f] :
    (Scheme.Modules.pushforward f).PreservesEpimorphisms where
  preserves {_ _} φ _ := map_epi f φ

instance preservesHomology (f : X ⟶ Y) [IsClosedImmersion f] :
    (Scheme.Modules.pushforward f).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

instance preservesFiniteColimits (f : X ⟶ Y) [IsClosedImmersion f] :
    PreservesFiniteColimits (Scheme.Modules.pushforward f) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

open PiExponent.CoherentAffineFinite PiExponent.FiniteGlobalPresentation
open PiExponent.ClosedPushforwardAffine

private theorem presentation_transport {Z : Scheme.{0}}
    {M N : SheafOfModules Z.ringCatSheaf} (e : M ≅ N)
    (P : M.Presentation) (hP : P.IsFinite) : ∃ Q : N.Presentation, Q.IsFinite := by
  let : IsIso e.hom := e.isIso_hom
  exact ⟨P.ofIsIso e.hom,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

instance pushforward_isFinitePresentation (f : X ⟶ Y) [IsClosedImmersion f]
    [IsLocallyNoetherian Y] (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pushforward f).obj M).IsFinitePresentation := by
  apply isFinitePresentation_of_affine_presentations
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  have hM := (locallyFinitelyGenerated_of_finitePresentation M).restrict (f ⁻¹ᵁ U.1).ι
  obtain ⟨P,hP⟩ := affine_pushforward_exists_finitePresentation (f ∣_ U.1)
    (M.restrict (f ⁻¹ᵁ U.1).ι) hM
  exact presentation_transport (Z := U.1.toScheme) (OpenBaseChange.iso f U.1 M).symm P hP

end PiExponentSeshadri.ClosedPushforward

end

end OAI
