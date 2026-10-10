import OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization
import OAI.NumberTheory.PiExponent.Cohomology.AmpleCohomologyFinite
import OAI.NumberTheory.PiExponent.Cohomology.CurveTwoAffineVanishing
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationInvariance
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveFiniteCoordinates

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open CurveNormalizationModel

variable {X : Scheme.{0}} [IsIntegral X]
variable {σ : Type} [Finite σ] [Nonempty σ]
variable {E : Type} [Field E] [Algebra ℂ E]

theorem parameterCurve_pullback_euler_degree
    (p : X ⟶ Spec (.of ℂ)) [IsProper p]
    (j : X ⟶ ProjectiveO1.projectiveSpace ℂ σ) [IsClosedImmersion j]
    (hj : j ≫ polynomialProjectiveProjection ℂ σ = p)
    (hd : topologicalKrullDim X ≤ 1)
    (f : E) (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
    (g : parameterCurve f hf ⟶ X) [IsFinite g]
    (hg : g ≫ p = parameterCurveStructureMap f hf)
    (W : X.Opens) (hW : W ≠ ⊥) [IsIso (g ∣_ W)] (L : LineBundle X) :
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (L.pullback g).sheaf -
        eulerCharacteristic (parameterCurveStructureMap f hf) 1
          (structureSheaf (parameterCurve f hf)) =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  let : Fintype σ := Fintype.ofFinite σ
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  let : X.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from p]
    infer_instance
  let : (structureSheaf X).IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : (structureSheaf X).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (structureSheaf X)).choose.isQuasicoherent
  let : L.sheaf.IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  obtain ⟨U,V,hU,hV,hcover⟩ :=
    ProjectiveCurveTwoAffine.two_affine_cover_of_closed_embedding j hd
  let : Subsingleton (cohomology (structureSheaf X) 2) :=
    CurveTwoAffineVanishing.cohomology_subsingleton U V hU hV hcover _ 2 le_rfl
  let : Subsingleton (cohomology L.sheaf 2) :=
    CurveTwoAffineVanishing.cohomology_subsingleton U V hU hV hcover _ 2 le_rfl
  have hO : LowCohomologyFinite p (structureSheaf X) := fun n _ =>
    ProjectiveFiniteCoordinates.projectiveOver_cohomology_finite p j hj _ n
  have hL : LowCohomologyFinite p L.sheaf := fun n _ =>
    ProjectiveFiniteCoordinates.projectiveOver_cohomology_finite p j hj _ n
  have hOY : LowCohomologyFinite (g ≫ p) (structureSheaf (parameterCurve f hf)) := by
    rw [hg]
    exact parameterCurve_finiteLineCohomology f hf ((parameterCurvePolarization f hf).pow 0)
  have hLY : LowCohomologyFinite (g ≫ p) (L.pullback g).sheaf := by
    rw [hg]
    exact parameterCurve_finiteLineCohomology f hf (L.pullback g)
  simpa only [hg] using
    pullback_euler_degree_of_open_iso g p hd W hW U V hU hV hcover L hO hL hOY hLY

theorem parameterCurve_pullback_euler_degree_of_ample
    (p : X ⟶ Spec (.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (hd : topologicalKrullDim X ≤ 1)
    (f : E) (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
    (g : parameterCurve f hf ⟶ X) [IsFinite g]
    (hg : g ≫ p = parameterCurveStructureMap f hf)
    (W : X.Opens) (hW : W ≠ ⊥) [IsIso (g ∣_ W)] (L : LineBundle X) :
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (L.pullback g).sheaf -
        eulerCharacteristic (parameterCurveStructureMap f hf) 1
          (structureSheaf (parameterCurve f hf)) =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  obtain ⟨n,hn,τ,hτ,s,hs,hclosed⟩ := H.ample_projective_sections_noetherian p hH
  let : Fintype τ := hτ
  have : Nonempty τ := by
    have hx : genericPoint X ∈ (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) := by
      rw [hs]
      trivial
    obtain ⟨i,-⟩ := Opens.mem_iSup.mp hx
    exact ⟨i⟩
  let j : X ⟶ ProjectiveO1.projectiveSpace ℂ τ := sectionsMorphism (baseScalars p) s hs
  have : IsClosedImmersion j := hclosed
  have hj : j ≫ polynomialProjectiveProjection ℂ τ = p := by
    rw [← AmpleCohomologyFinite.projectiveBase_eq_polynomialProjectiveProjection]
    exact (sectionsMorphism_over (baseScalars p) s hs).trans (toSpec_scalarMap p)
  exact parameterCurve_pullback_euler_degree p j hj hd f hf g hg W hW L

theorem exists_intrinsic_normalization_preserving_degree
    (p : X ⟶ Spec (.of ℂ)) [IsProper p]
    (j : X ⟶ ProjectiveO1.projectiveSpace ℂ σ) [IsClosedImmersion j]
    (hj : j ≫ polynomialProjectiveProjection ℂ σ = p)
    (hdim : topologicalKrullDim X = 1) :
    letI := CurveNormalizationMorphism.structureFieldAlgebra p
    ∀ (f : X.functionField) (hf : Transcendental ℂ f),
      ∀ [FiniteDimensional (IntermediateField.adjoin ℂ {f}) X.functionField],
      ∃ g : parameterCurve f hf ⟶ X,
        g ≫ p = parameterCurveStructureMap f hf ∧
        parameterCurveGenericPoint f hf ≫ g = X.fromSpecStalk (genericPoint X) ∧
        IsFinite g ∧ ∀ L : LineBundle X,
          eulerCharacteristic (parameterCurveStructureMap f hf) 1 (L.pullback g).sheaf -
              eulerCharacteristic (parameterCurveStructureMap f hf) 1
                (structureSheaf (parameterCurve f hf)) =
            eulerCharacteristic p 1 L.sheaf -
              eulerCharacteristic p 1 (structureSheaf X) := by
  let := CurveNormalizationMorphism.structureFieldAlgebra p
  intro f hf hfinite
  obtain ⟨g,hg,hgeneric,hgfinite,W,hW,hiso⟩ :=
    CurveNormalizationMorphism.exists_intrinsic_normalization_morphism p hdim f hf
  let := hgfinite
  let := hiso
  have hw : W ≠ ⊥ := by
    intro hw
    simp only [hw, Opens.mem_bot] at hW
  exact ⟨g,hg,hgeneric,hgfinite,fun L =>
    parameterCurve_pullback_euler_degree p j hj hdim.le f hf g hg W hw L⟩

end PiExponent.CurveNormalizationDegree

end

end OAI
