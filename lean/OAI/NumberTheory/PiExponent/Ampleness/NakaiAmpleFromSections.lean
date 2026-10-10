import OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive
import OAI.NumberTheory.PiExponent.Ampleness.FinitePullbackAmple
import OAI.NumberTheory.PiExponent.Ampleness.NakaiEffectivity
import OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree
import OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective PiExponentSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{0}}

theorem curveDegree_eq_zero_of_sectionsMorphism_contracted
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (k : ℕ) (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ z, sectionOpen X (s z)) = ⊤)
    (C : IntegralCurve X)
    (y : ProjectiveO1.projectiveSpace ℂ (Fin k))
    (hconstant : ∀ c : C.scheme, sectionsMorphism (baseScalars p) s hs (C.embedding c) = y) :
    curveDegree p L C = 0 := by
  classical
  obtain ⟨c⟩ : Nonempty C.scheme := inferInstance
  have hc : C.embedding c ∈ ⨆ z, sectionOpen X (s z) := by rw [hs]; trivial
  obtain ⟨z,hz⟩ := Opens.mem_iSup.mp hc
  have hpre : sectionsMorphism (baseScalars p) s hs ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin k) ℂ) (MvPolynomial.X z) =
      sectionOpen X (s z) := sectionsMorphism_preimage (baseScalars p) s hs z
  have hy : y ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin k) ℂ)
      (MvPolynomial.X z) := by
    rw [← hpre] at hz
    change sectionsMorphism (baseScalars p) s hs (C.embedding c) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin k) ℂ) (MvPolynomial.X z) at hz
    rwa [hconstant c] at hz
  have hrange : Set.range C.embedding ⊆ (sectionOpen X (s z) : Set X) := by
    rintro x ⟨c',rfl⟩
    rw [← hpre]
    change sectionsMorphism (baseScalars p) s hs (C.embedding c') ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin k) ℂ) (MvPolynomial.X z)
    rwa [hconstant c']
  let e := ConstantPullbackDegree.pullbackFrame_of_range_subset L C.embedding
    (sectionOpen X (s z)) hrange (sectionFrame (s z))
  change eulerCharacteristic (C.embedding ≫ p) 1 (L.pullback C.embedding).sheaf -
    eulerCharacteristic (C.embedding ≫ p) 1 (structureSheaf C.scheme) = 0
  rw [eulerCharacteristic_iso (C.embedding ≫ p) e 1]
  exact sub_self _

theorem isAmple_of_section_cover_of_curveDegree_pos [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (k : ℕ) (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ z, sectionOpen X (s z)) = ⊤)
    (hpositive : ∀ C : IntegralCurve X, 0 < curveDegree p L C) : L.IsAmple := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (baseScalars p))) := by
    change IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)))
    rw [toSpec_scalarMap p]
    infer_instance
  let f : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin k) :=
    sectionsMorphism (baseScalars p) s hs
  let : IsProper f := sectionsMorphism_proper (baseScalars p) s hs
  let : JacobsonSpace (ProjectiveO1.projectiveSpace ℂ (Fin k)) :=
    LocallyOfFiniteType.jacobsonSpace (polynomialProjectiveProjection ℂ (Fin k))
  let : IsFinite f := isFinite_of_no_contracted_integralCurves f d hdim (by
    intro C y hy j hj
    have hconstant (c : C.scheme) : f (C.embedding c) = y := by
      have hc : f.fiberι y (j c) ∈ Set.range (f.fiberι y) := ⟨j c,rfl⟩
      rw [f.range_fiberι] at hc
      change f (f.fiberι y (j c)) = y at hc
      have he := congrArg (fun g : C.scheme ⟶ X => g c) hj
      simpa only [Scheme.Hom.comp_apply] using he ▸ hc
    have hz := curveDegree_eq_zero_of_sectionsMorphism_contracted p L k s hs C y hconstant
    have hp := hpositive C
    omega)
  apply L.ample_of_affine_section_cover s hs
  intro z
  change IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s z))
  exact (sectionsMorphism_preimage (baseScalars p) s hs z) ▸
    (standardChart_isAffineOpen (R := ℂ) z).preimage f

end
end PiExponent.NumericalAmpleness

end OAI
