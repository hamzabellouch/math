import OAI.NumberTheory.PiExponent.Ampleness.LineAmpleOperations
import OAI.NumberTheory.PiExponent.Ampleness.NakaiDivisorAmple
import OAI.NumberTheory.PiExponent.Ampleness.NakaiStationarity
import OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover
import OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice
import OAI.NumberTheory.PiExponent.Cohomology.EulerRegularTwists
import OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceFinite

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Filter
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem exists_nonzero_power_section_of_euler_growth
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      (L.pullback I.subschemeι).IsAmple)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) atTop atTop) :
    ∃ a : ℕ, 0 < a ∧ ∃ s : GlobalSections X (L.pow a).sheaf, s ≠ 0 := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  obtain ⟨b,G,hG,G',hG'⟩ := exists_common_tensor_generators H L hH
  let := hG
  let := hG'
  let B := H.pow b
  obtain ⟨k,u,hu⟩ := GeneratorsSectionCover.exists_fin_section_cover B G
  obtain ⟨k',v,hv⟩ := GeneratorsSectionCover.exists_fin_section_cover (L.tensor B) G'
  obtain ⟨s,hs⟩ := exists_mono_section_of_finite_cover p (L.tensor B) v hv
  obtain ⟨t,ht⟩ := exists_mono_section_of_finite_cover p B u hu
  let := hs
  let := ht
  have hD := hlower (zeroIdeal (L.tensor B) s)
    (regular_sectionZero_dimension_le (L.tensor B) s d hdim)
  have hE := hlower (zeroIdeal B t) (regular_sectionZero_dimension_le B t d hdim)
  have heuler (n : ℕ) : eulerCharacteristic p (d+1) ((L.pow n).tensor (H.pow 0)).sheaf =
      eulerCharacteristic p (d+1) (L.pow n).sheaf :=
    eulerCharacteristic_iso p (moduleTensorRightUnit (L.pow n).sheaf) (d+1)
  have hgrowth' : Tendsto
      (fun n => eulerCharacteristic p (d+1) ((L.pow n).tensor (H.pow 0)).sheaf) atTop atTop := by
    simpa only [heuler] using hgrowth
  have hsections := eventually_nonzero_mixedPower_sections_of_growth p L B (H.pow 0)
    s t hD hE (d+1) (by omega) hgrowth'
  obtain ⟨N,hN⟩ := eventually_atTop.mp hsections
  obtain ⟨σ,hσ⟩ := hN (N+1) (by omega)
  let e := moduleTensorRightUnit (L.pow (N+1)).sheaf
  refine ⟨N+1,by omega,σ ≫ e.hom,?_⟩
  intro hz
  apply hσ
  apply (cancel_mono e.hom).mp
  exact hz.trans (zero_comp (C := X.Modules) (f := e.hom)).symm

theorem exists_power_section_cover_of_euler_growth [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ PiExponent.polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      (L.pullback I.subschemeι).IsAmple)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) atTop atTop) :
    ∃ a : ℕ, 0 < a ∧ ∃ k : ℕ, ∃ s : Fin k → GlobalSections X (L.pow a).sheaf,
      (⨆ j, sectionOpen X (s j)) = ⊤ := by
  obtain ⟨a,ha,s,hs⟩ := exists_nonzero_power_section_of_euler_growth p H L hH d hdim hlower hgrowth
  let A := L.pow a
  let := A.mono_section s hs
  let j := (zeroIdeal A s).subschemeι
  have hL := hlower (zeroIdeal A s) (regular_sectionZero_dimension_le A s d hdim)
  have hA : (A.pullback j).IsAmple :=
    PiExponent.AmpleIso.isAmple_of_sheaf_iso ((L.pullback j).pow a) (A.pullback j)
      (PiExponentSeshadri.PullbackTensor.powIso j L a).symm (hL.pow a ha)
  have hfinite (n : ℕ) : letI := Module.compHom (cohomology (A.pow n).sheaf 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology (A.pow n).sheaf 1) := by
    let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation (A.pow n)
    exact ProjectiveSpaceFinite.projectiveOver_cohomology_finite p r i hi (A.pow n).sheaf 1
  obtain ⟨N,hN⟩ := eventual_power_section_cover_of_ample_zeroDivisor p A s hfinite hA
  obtain ⟨k,t,ht⟩ := hN N le_rfl
  let e := linePowerMul L a (N+1)
  refine ⟨a*(N+1),Nat.mul_pos ha (by omega),k,fun z => t z ≫ e.hom,?_⟩
  exact (iSup_congr fun j =>
    PiExponent.AmpleIso.sectionOpen_postcomp_iso (t j) e).trans ht

end
end PiExponent.NumericalAmpleness

end OAI
