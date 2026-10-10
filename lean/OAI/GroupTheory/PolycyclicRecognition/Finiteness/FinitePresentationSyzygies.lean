import OAI.GroupTheory.PolycyclicRecognition.Finiteness.StableResolutionLimit
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Projective

namespace OAI

/-! # Finite presentation of integral resolution syzygies

Two consecutive finite projective terms give a finitely presented quotient
syzygy. This supplies the finite-presentation input for passing Hom through
directed colimits in the FP-infinity argument.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem projectiveRepresentation_module (A : Rep.{0} ℤ G) [Projective A] :
    Module.Projective ℤ[G] A.ρ.asModule := by
  have h : Projective (Rep.toModuleMonoidAlgebra.obj A) :=
    (Rep.equivalenceModuleMonoidAlgebra.map_projective_iff A).mpr inferInstance
  let := h
  exact ModuleCat.projective_of_module_projective (Rep.toModuleMonoidAlgebra.obj A)

theorem projectiveRepresentation_finitePresentation (A : Rep.{0} ℤ G) [Projective A]
    (hA : IntegralRepresentationFinite G A) : Module.FinitePresentation ℤ[G] A.ρ.asModule := by
  let := projectiveRepresentation_module A
  let : Module.Finite ℤ[G] A.ρ.asModule := hA
  exact Module.finitePresentation_of_projective ℤ[G] A.ρ.asModule

theorem resolutionOpcycles_finitePresentation
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    (h₀ : IntegralRepresentationFinite G (P.complex.X n))
    (h₁ : IntegralRepresentationFinite G (P.complex.X (n + 1))) :
    Module.FinitePresentation ℤ[G] (P.complex.opcycles n).ρ.asModule := by
  let F := Rep.toModuleMonoidAlgebra (k := ℤ) (G := G)
  let S := ShortComplex.mk (P.complex.d (n + 1) n) (P.complex.pOpcycles n)
    (P.complex.d_pOpcycles (n + 1) n)
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel _
    (P.complex.opcyclesIsCokernel (n + 1) n (by simp))
  have he : LinearMap.range (F.map S.f).hom = LinearMap.ker (F.map S.g).hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker (S.map F)).mp (hS.map F)
  let : Module.Finite ℤ[G] (F.obj S.X₁) := h₁
  let : Module.FinitePresentation ℤ[G] (F.obj S.X₂) :=
    projectiveRepresentation_finitePresentation (P.complex.X n) h₀
  let : Epi (F.map S.g) := by
    change Epi (F.map (P.complex.pOpcycles n))
    infer_instance
  apply Module.finitePresentation_of_surjective (F.map S.g).hom
    ((ModuleCat.epi_iff_surjective (F.map S.g)).mp inferInstance)
  rw [← he]
  exact Submodule.fg_range (F.map S.f).hom

theorem TypeFPInfinity.exists_finitelyPresented_syzygy
    (hG : TypeFPInfinity G) (n : ℕ) :
    ∃ P : ProjectiveResolution (trivialIntegral G),
      (∀ i, i ≤ n + 1 → IntegralRepresentationFinite G (P.complex.X i)) ∧
      Module.FinitePresentation ℤ[G] (P.complex.opcycles n).ρ.asModule := by
  obtain ⟨P, hP⟩ := hG (n + 1)
  exact ⟨P, hP, resolutionOpcycles_finitePresentation P n (hP n (by omega))
    (hP (n + 1) le_rfl)⟩

end PolycyclicRecognition

end

end OAI
