import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.CurveFinite
import OAI.AlgebraicGeometry.Seshadri.Sheaves.SupportedSheaf
import OAI.AlgebraicGeometry.Seshadri.Divisors.CartierSection

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens

variable {X : Scheme.{0}}

lemma cokernel_stalk_subsingleton {M N : X.Modules} (s : M ⟶ N) (x : X)
    (hx : x ∈ isoOpen s) :
    Subsingleton ((cokernel s).presheaf.stalk x) := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf ⋙
    TopCat.Sheaf.forget AddCommGrpCat X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let : F.PreservesZeroMorphisms := by
    constructor
    intro M N
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (0 : M ⟶ N)).hom = 0
    rw [Functor.map_zero]
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map 0 = 0
    exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_zero _ _
  let : PreservesColimitsOfSize.{0,0} F := by
    refine @comp_preservesColimits _ _ _ _ _ _ _ _ ?_ ?_
    · exact ModuleSheafExact.toSheafPreservesColimits X.ringCatSheaf
    · exact inferInstanceAs (PreservesColimitsOfSize.{0,0}
        (TopCat.Sheaf.forget AddCommGrpCat.{0} (X : TopCat) ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x))
  obtain ⟨U,hx,hU⟩ := (mem_isoOpen_iff s x).mp hx
  let := hU
  let : IsIso (F.map s) := stalk_isIso_of_restrict s U.ι ⟨x,hx⟩
  have hz : IsZero (F.obj (cokernel s)) :=
    (isZero_cokernel_of_epi (F.map s)).of_iso (PreservesCokernel.iso F s)
  exact AddCommGrpCat.subsingleton_of_isZero hz

lemma LineBundle.isoOpen_ne_bot [IsIntegral X] (L : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) : isoOpen s ≠ ⊥ := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨V,hx,⟨e⟩⟩ := L.locallyRankOne x
  let : Nonempty V := ⟨⟨x,hx⟩⟩
  have hc : coefficient e (restrictSection V.ι s) ≠ 0 := by
    intro h
    apply hs
    apply L.restricted_coefficient_injective V.ι e
    change coefficient e (restrictSection V.ι s) =
      coefficient e (restrictSection V.ι (0 : O X ⟶ L.sheaf))
    rw [restrictSection_zero]
    exact h.trans (coefficient_zero e).symm
  intro hz
  have he := preimage_isoOpen s V.ι e
  rw [hz] at he
  have hb : V.toScheme.basicOpen (coefficient e (restrictSection V.ι s)) = ⊥ := by
    simpa only [Scheme.Hom.preimage_bot] using he.symm
  exact hc (eq_zero_of_basicOpen_eq_bot _ hb)

lemma LineBundle.cokernel_support_finite [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (L : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    ((isoOpen s : Set X)ᶜ).Finite := by
  apply proper_closed_finite_of_dimension_one hd (isoOpen s).isOpen.isClosed_compl
  intro he
  have hb : isoOpen s = ⊥ := by
    apply SetLike.coe_injective
    simpa using he
  exact L.isoOpen_ne_bot s hs hb

theorem LineBundle.cokernel_flasque [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (L : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj (cokernel s)) := by
  let S : Set X := (isoOpen s : Set X)ᶜ
  have hfin : S.Finite := L.cokernel_support_finite hd s hs
  have hclosed : ∀ x ∈ S, IsClosed ({x} : Set X) := by
    intro x hx
    have hc : closure ({x} : Set X) ⊆ S :=
      closure_minimal (Set.singleton_subset_iff.mpr hx) (isoOpen s).isOpen.isClosed_compl
    have hsub : (closure ({x} : Set X)).Subsingleton := by
      apply proper_irreducible_closed_subsingleton hd isClosed_closure
        isIrreducible_singleton.closure
      intro he
      have hb : S = Set.univ := Set.eq_univ_of_univ_subset (he ▸ hc)
      exact L.isoOpen_ne_bot s hs (SetLike.coe_injective (by simpa [S] using hb))
    have he : closure ({x} : Set X) = {x} := by
      apply Set.Subset.antisymm
      · intro y hy
        exact hsub hy (subset_closure (Set.mem_singleton x))
      · exact subset_closure
    exact he ▸ isClosed_closure
  apply FiniteSupport.finite_closed_support_flasque _ S hfin hclosed
  intro x hx
  apply cokernel_stalk_subsingleton s x
  exact not_not.mp hx

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
