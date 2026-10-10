import OAI.NumberTheory.PiExponent.Ampleness.AmpleIso
import OAI.NumberTheory.PiExponent.Approximation.FrameSections

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open scoped AlgebraicGeometry

theorem open_eq_top_of_subsingleton {X : Scheme} [Subsingleton X]
    (U : X.Opens) (x : X) (hx : x ∈ U) : U = ⊤ := by
  apply top_unique
  intro y _
  simpa only [Subsingleton.elim y x] using hx

theorem exists_global_frame_of_top_frame {X : Scheme} (M : X.Modules)
    (e : M.restrict (⊤ : X.Opens).ι ≅ O (⊤ : X.Opens).toScheme) :
    ∃ s : GlobalSections X M, sectionOpen X s = ⊤ := by
  let s := (moduleSectionEquiv M).symm (openSectionEquiv M ⊤ e.inv)
  have hs : restrictSection (⊤ : X.Opens).ι s = e.inv := by
    apply (openSectionEquiv M ⊤).injective
    rw [openSectionEquiv_restrict]
    exact (moduleSectionEquiv M).apply_symm_apply _
  have hi : IsIso (restrictSection (⊤ : X.Opens).ι s) := by rw [hs]; infer_instance
  let := (Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι).isIso_inv
  have hi' : IsIso ((Scheme.Modules.restrictFunctor (⊤ : X.Opens).ι).map s) := by
    exact (isIso_comp_left_iff (Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι).inv _).mp hi
  refine ⟨s, top_unique ?_⟩
  exact le_iSup_of_le ⊤ (le_iSup_of_le hi' le_rfl)

theorem isAmple_of_subsingleton {X : Scheme} [Subsingleton X]
    (L : LineBundle X) : L.IsAmple := by
  intro x V hx
  have hV : V = ⊤ := open_eq_top_of_subsingleton V x hx
  obtain ⟨U, hxU, ⟨e⟩⟩ := (L.pow 1).locallyRankOne x
  have hU : U = ⊤ := open_eq_top_of_subsingleton U x hxU
  subst U
  obtain ⟨s, hs⟩ := exists_global_frame_of_top_frame (L.pow 1).sheaf e
  change GlobalSections X (modulePow X L.sheaf 1) at s
  change sectionOpen X s = ⊤ at hs
  obtain ⟨W, hWa, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  have hW : W = ⊤ := open_eq_top_of_subsingleton W x hxW
  refine ⟨1, by decide, s, ?_, ?_, ?_⟩
  · rw [hs]; trivial
  · rw [hs, hV]
  · rw [hs, ← hW]; exact hWa

theorem isAmple_of_integral_dimension_zero {X : Scheme}
    [IsIntegral X] [IsLocallyNoetherian X] (hdim : topologicalKrullDim X ≤ 0)
    (L : LineBundle X) : L.IsAmple := by
  let : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  let : Subsingleton X := ⟨fun x y =>
    (PreirreducibleSpace.isPreirreducible_univ (X := X)).subsingleton
      (Set.mem_univ x) (Set.mem_univ y)⟩
  exact isAmple_of_subsingleton L

structure IntegralCurve (X : Scheme) where
  scheme : Scheme
  embedding : scheme ⟶ X
  closedImmersion : IsClosedImmersion embedding
  integral : IsIntegral scheme
  dimension : topologicalKrullDim scheme = 1

attribute [instance] IntegralCurve.closedImmersion IntegralCurve.integral

theorem no_integralCurve_of_dimension_zero {X : Scheme}
    (hdim : topologicalKrullDim X ≤ 0) : IsEmpty (IntegralCurve X) := by
  refine ⟨fun C => ?_⟩
  have hh := C.embedding.isClosedEmbedding.isEmbedding.topologicalKrullDim_le
  rw [C.dimension] at hh
  have : (1 : WithBot ℕ∞) ≤ 0 := hh.trans hdim
  norm_num at this

end
end PiExponent.NumericalAmpleness

end OAI
