import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FinitePresentationSyzygies
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequentialHomLimit
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteFinsuppHom
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RepCochainMaps
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CoefficientNaturalCohomology

namespace OAI

/-! # Vanishing coefficient limits in finite resolution degrees

A finite group-ring module sends a coefficient system with zero direct limit
to an eventually zero Hom system. Applying this to a cocycle in a projective
resolution proves the corresponding zero-finitary cohomology statement.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {G : Type} [Group G]

abbrev resolutionCochainCoefficientMap (C : ChainComplex (Rep.{0} ℤ G) ℕ)
    {A B : Rep.{0} ℤ G} (u : A ⟶ B) :
    C.linearYonedaObj ℤ A ⟶ C.linearYonedaObj ℤ B :=
  repCochainPostcomp ℤ C u

theorem homologyMap_cycle_eq_zero_of_component
    {C D : CochainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) (n : ℕ)
    (z : C.cycles n) (hz : φ.f n (C.iCycles n z) = 0) :
    homologyMap φ n (C.homologyπ n z) = 0 := by
  have hz' : cyclesMap φ n z = 0 := by
    apply (ModuleCat.mono_iff_injective (D.iCycles n)).mp inferInstance
    have h := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (cyclesMap_i φ n)) z
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, map_zero] using h.trans hz
  have h := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (homologyπ_naturality φ n)) z
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hz', map_zero] using h

variable (A : ℕ → Rep.{0} ℤ G)
  (f : ∀ i j, i ≤ j → (A i ⟶ A j))

abbrev coefficientModuleTransition (i j : ℕ) (h : i ≤ j) :
    (A i).ρ.asModule →ₗ[ℤ[G]] (A j).ρ.asModule :=
  representationModuleHomEquiv ℤ G (A i) (A j) (f i j h)

variable [DirectedSystem (fun i => (A i).ρ.asModule)
  (fun i j h => coefficientModuleTransition A f i j h)]

theorem finiteRepresentation_eventually_zero
    [Subsingleton (Module.DirectLimit (fun i => (A i).ρ.asModule)
      (coefficientModuleTransition A f))]
    (B : Rep.{0} ℤ G) (hB : IntegralRepresentationFinite G B)
    (i : ℕ) (u : B ⟶ A i) :
    ∃ (j : ℕ) (hij : i ≤ j), u ≫ f i j hij = 0 := by
  let : Module.Finite ℤ[G] B.ρ.asModule := hB
  let u' := representationModuleHomEquiv ℤ G B (A i) u
  have hu : (Module.DirectLimit.of ℤ[G] ℕ (fun i => (A i).ρ.asModule)
      (coefficientModuleTransition A f) i).comp u' = 0 := by
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  obtain ⟨j, hij, hj⟩ := sequentialLimit_eventually_zero_finite
    (coefficientModuleTransition A f) i u' hu
  refine ⟨j, hij, ?_⟩
  apply (representationModuleHomEquiv ℤ G B (A j)).injective
  change (representationModuleHomEquiv ℤ G B (A j)) (u ≫ f i j hij) = 0
  convert hj using 1
  apply LinearMap.ext
  intro x
  rfl

theorem finiteResolutionCohomology_eventually_zero
    [Subsingleton (Module.DirectLimit (fun i => (A i).ρ.asModule)
      (coefficientModuleTransition A f))]
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    (hP : IntegralRepresentationFinite G (P.complex.X n))
    (i : ℕ) (x : (P.complex.linearYonedaObj ℤ (A i)).homology n) :
    ∃ (j : ℕ) (hij : i ≤ j),
      homologyMap (resolutionCochainCoefficientMap P.complex (f i j hij)) n x = 0 := by
  let C := P.complex.linearYonedaObj ℤ (A i)
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance x
  obtain ⟨j, hij, hj⟩ := finiteRepresentation_eventually_zero A f
    (P.complex.X n) hP i (C.iCycles n z)
  refine ⟨j, hij, homologyMap_cycle_eq_zero_of_component _ n z ?_⟩
  exact hj

theorem TypeFP.cohomology_eventually_zero
    [Subsingleton (Module.DirectLimit (fun i => (A i).ρ.asModule)
      (coefficientModuleTransition A f))]
    (n : ℕ) (hG : TypeFP G n) (i : ℕ) (x : groupCohomology (A i) n) :
    ∃ (j : ℕ) (hij : i ≤ j), groupCohomology.map (MonoidHom.id G) (f i j hij) n x = 0 := by
  obtain ⟨P, hP⟩ := hG
  obtain ⟨j, hij, hj⟩ := finiteResolutionCohomology_eventually_zero A f P n
    (hP n le_rfl) i ((coefficientNaturalCohomologyIso P (A i) n).hom x)
  refine ⟨j, hij, ?_⟩
  apply (coefficientNaturalCohomologyIso P (A j) n).toLinearEquiv.injective
  change (coefficientNaturalCohomologyIso P (A j) n).hom.hom
    (groupCohomology.map (MonoidHom.id G) (f i j hij) n x) =
      (coefficientNaturalCohomologyIso P (A j) n).hom.hom 0
  have hn := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (coefficientNaturalCohomologyIso_naturality P (f i j hij) n)) x
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, map_zero, hj] using hn

theorem TypeFPInfinity.cohomology_eventually_zero
    [Subsingleton (Module.DirectLimit (fun i => (A i).ρ.asModule)
      (coefficientModuleTransition A f))]
    (hG : TypeFPInfinity G) (n i : ℕ) (x : groupCohomology (A i) n) :
    ∃ (j : ℕ) (hij : i ≤ j), groupCohomology.map (MonoidHom.id G) (f i j hij) n x = 0 :=
  TypeFP.cohomology_eventually_zero A f n (hG n) i x

end PolycyclicRecognition

end

end OAI
