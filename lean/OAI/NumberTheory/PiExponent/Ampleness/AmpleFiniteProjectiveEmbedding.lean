import OAI.NumberTheory.PiExponent.Ampleness.NoetherianAmpleProjectiveSections
import OAI.NumberTheory.PiExponent.Cohomology.AmpleCohomologyFinite
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.ProjectiveO1
variable {X : Scheme.{0}}

theorem ample_finite_projective_embedding [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) :
    ∃ r : ℕ, ∃ i : X ⟶ projectiveSpace ℂ (Fin (r+1)),
      IsClosedImmersion i ∧ i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  obtain ⟨n, _, σ, hσ, s, hs, hc⟩ := H.ample_projective_sections_noetherian p hH
  let : Fintype σ := hσ
  have hne : Nonempty σ := by
    obtain ⟨x⟩ : Nonempty X := inferInstance
    have hx : x ∈ ⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i) := by
      rw [hs]
      trivial
    obtain ⟨i, _⟩ := Opens.mem_iSup.mp hx
    exact ⟨i⟩
  have hpos : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr hne
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
  let e : Fin (r+1) ≃ σ := ((Fintype.equivFin σ).trans (finCongr hr)).symm
  let t : Fin (r+1) → GlobalSections X (modulePow X H.sheaf n) := s ∘ e
  have ht : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (t i)) = ⊤ :=
    (e.iSup_comp (g := fun j => PiExponentSeshadri.SectionOpens.isoOpen (s j))).trans hs
  let k := baseScalars p
  let : IsClosedImmersion (sectionsMorphism k s hs) := hc
  let i : X ⟶ projectiveSpace ℂ (Fin (r+1)) := sectionsMorphism k t ht
  have hclosed : IsClosedImmersion i := sectionsMorphism_reindex_closed k s hs e ht
  refine ⟨r, i, hclosed, ?_⟩
  rw [← AmpleCohomologyFinite.projectiveBase_eq_polynomialProjectiveProjection]
  exact (sectionsMorphism_over k t ht).trans (toSpec_scalarMap p)

end
end PiExponent.NumericalAmpleness

end OAI
