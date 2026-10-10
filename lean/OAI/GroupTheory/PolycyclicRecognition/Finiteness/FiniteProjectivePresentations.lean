import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteRepresentationQuotients
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteIntegralRepresentations

namespace OAI

/-! # Finite projective covers of finitely generated representations -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
variable {G : Type} [Group G]

structure FiniteIntegralProjectivePresentation (A : Rep.{0} ℤ G)
    extends ProjectivePresentation A where
  finite : IntegralRepresentationFinite G p

theorem finiteIntegralFreeCover_exists (A : Rep.{0} ℤ G)
    (hA : IntegralRepresentationFinite G A) :
    ∃ (ι : Type) (_ : Finite ι) (f : Rep.free ℤ G ι ⟶ A), Epi f := by
  classical
  let : Module ℤ A := A.hV2
  let : Module.Finite ℤ[G] A.ρ.asModule := hA
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := ℤ[G])
    (M := A.ρ.asModule))
  let : Finite s := hs.to_subtype
  let f : Rep.free ℤ G s ⟶ A := Rep.freeLift ℤ G A (fun a : s => A.ρ.asModuleEquiv a.val)
  let fM := Representation.IntertwiningMap.equivLinearMapAsModule
    (Representation.free ℤ G s) A.ρ f.hom
  have hfM : Function.Surjective fM := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro a ha
    refine ⟨Finsupp.single (⟨a, ha⟩ : s) (MonoidAlgebra.single 1 1), ?_⟩
    apply A.ρ.asModuleEquiv.injective
    change f.hom (Finsupp.single (⟨a, ha⟩ : s) (MonoidAlgebra.single 1 1)) = _
    change Representation.freeLift A.ρ (fun a : s => A.ρ.asModuleEquiv a.val)
      (Finsupp.single (⟨a, ha⟩ : s) (MonoidAlgebra.single 1 1)) = A.ρ.asModuleEquiv a
    rw [Representation.freeLift_single_single]
    simp only [map_one, Module.End.one_apply]
    exact @one_smul ℤ A _ A.hV2.toMulAction _
  have hf : Epi f := by
    rw [Rep.epi_iff_surjective]
    intro a
    obtain ⟨b, hb⟩ := hfM (A.ρ.asModuleEquiv.symm a)
    exact ⟨b, congrArg A.ρ.asModuleEquiv hb⟩
  exact ⟨s, inferInstance, f, hf⟩

theorem finiteIntegralProjectivePresentation_exists (A : Rep.{0} ℤ G)
    (hA : IntegralRepresentationFinite G A) :
    Nonempty (FiniteIntegralProjectivePresentation A) := by
  obtain ⟨ι, hι, f, hf⟩ := finiteIntegralFreeCover_exists A hA
  let := hι
  exact ⟨{
    p := Rep.free ℤ G ι
    f := f
    epi := hf
    finite := integralRepresentationFinite_free G ι }⟩

/-- A projective presentation chosen with finite source whenever the target
is finitely generated. The finiteness proof stays inside the chosen object. -/
def chosenIntegralPresentation (A : Rep.{0} ℤ G) : ProjectivePresentation A := by
  classical
  exact if h : IntegralRepresentationFinite G A then
    (finiteIntegralProjectivePresentation_exists A h).some.toProjectivePresentation
  else (EnoughProjectives.presentation A).some

theorem chosenIntegralPresentation_finite (A : Rep.{0} ℤ G)
    (hA : IntegralRepresentationFinite G A) :
    IntegralRepresentationFinite G (chosenIntegralPresentation A).p := by
  simp only [chosenIntegralPresentation, dite_eq_left hA]
  exact (finiteIntegralProjectivePresentation_exists A hA).some.finite

end PolycyclicRecognition

end

end OAI
