import OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers
import OAI.NumberTheory.PiExponent.Approximation.SectionOpens
import OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem isAmple_of_global_frame_affine [IsAffine X] (L : LineBundle X)
    (e : L.sheaf ≅ structureSheaf X) : L.IsAmple := by
  intro x V hx
  obtain ⟨r,hr,hxr⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨x,hx⟩ (by trivial)
  let E := globalPowerFrame e 1
  let s : GlobalSections X (L.pow 1).sheaf := scalarEnd r ≫ E.inv
  have he : coefficient E s = r := by
    have hcomp : (scalarEnd r ≫ E.inv) ≫ E.hom = scalarEnd r := by
      exact (Category.assoc (scalarEnd r) E.inv E.hom).trans
        ((congrArg (fun g : structureSheaf X ⟶ structureSheaf X => scalarEnd r ≫ g)
          E.inv_hom_id).trans (Category.comp_id (scalarEnd r)))
    exact (congrArg (fun f : structureSheaf X ⟶ structureSheaf X => endValue f)
      hcomp).trans (endValue_scalarEnd r)
  have hopen : sectionOpen X s = X.basicOpen r := by
    change PiExponentSeshadri.SectionOpens.isoOpen s = _
    exact (isoOpen_eq_basicOpen E s).trans (congrArg X.basicOpen he)
  exact ⟨1,by decide,s,hopen.symm ▸ hxr,hopen.le.trans hr,hopen.symm ▸ (isAffineOpen_top X).basicOpen r⟩

theorem isAmple_of_proper_dimension_zero [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 0) (L : LineBundle X) : L.IsAmple := by
  let : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : Finite X := finite_of_compact_of_discrete
  let : IsAffine X := proper_finite_scheme_isAffine p
  obtain ⟨e⟩ := PiExponentSeshadri.FiniteSupport.lineBundle_trivial L
  exact isAmple_of_global_frame_affine L e

end
end PiExponent.NumericalAmpleness

end OAI
