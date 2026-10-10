import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequentialRepresentationColimit
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedIdentityClass

namespace OAI

/-! # Detecting a zero cohomology class at a finite coefficient stage

For positive degrees, a boundary in the coefficient colimit can be lifted to
one finite stage. Finite presentation lifts the cochain, and finite generation
kills the resulting error at a later stage.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem cochain_class_zero_of_boundary (C : CochainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (z : C.cycles (n + 1)) (y : C.X n) (hy : C.d n (n + 1) y = C.iCycles (n + 1) z) :
    C.homologyπ (n + 1) z = 0 := by
  have he : C.toCycles n (n + 1) y = z := by
    apply (ModuleCat.mono_iff_injective (C.iCycles (n + 1))).mp inferInstance
    have h := ConcreteCategory.congr_hom (C.toCycles_i n (n + 1)) y
    exact h.trans hy
  rw [← he]
  exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ n (n + 1)) y

theorem resolution_cohomologyMap_zero_of_boundary
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    {A B : Rep.{0} ℤ G} (f : A ⟶ B)
    (z : (P.complex.linearYonedaObj ℤ A).cycles (n + 1))
    (y : P.complex.X n ⟶ B)
    (hy : P.complex.d (n + 1) n ≫ y =
      (P.complex.linearYonedaObj ℤ A).iCycles (n + 1) z ≫ f) :
    homologyMap (repCochainPostcomp ℤ P.complex f) (n + 1)
      ((P.complex.linearYonedaObj ℤ A).homologyπ (n + 1) z) = 0 := by
  let φ := repCochainPostcomp ℤ P.complex f
  let C := P.complex.linearYonedaObj ℤ B
  have hd : C.d n (n + 1) y = C.iCycles (n + 1) (cyclesMap φ (n + 1) z) := by
    have he := ConcreteCategory.congr_hom (cyclesMap_i φ (n + 1)) z
    change C.iCycles (n + 1) (cyclesMap φ (n + 1) z) =
      (P.complex.linearYonedaObj ℤ A).iCycles (n + 1) z ≫ f at he
    exact hy.trans he.symm
  have hz := cochain_class_zero_of_boundary C n (cyclesMap φ (n + 1) z) y hd
  have he := ConcreteCategory.congr_hom (homologyπ_naturality φ (n + 1)) z
  change homologyMap φ (n + 1) ((P.complex.linearYonedaObj ℤ A).homologyπ (n + 1) z) =
    C.homologyπ (n + 1) (cyclesMap φ (n + 1) z) at he
  exact he.trans hz

theorem finiteResolutionCohomology_colimit_kernel
    (D : SequentialRepresentationDiagram G) (A : Rep.{0} ℤ G) (c : D.ColimitCocone A)
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    [Module.FinitePresentation ℤ[G] (P.complex.X n).ρ.asModule]
    [Module.Finite ℤ[G] (P.complex.X (n + 1)).ρ.asModule]
    (i : ℕ) (x : (P.complex.linearYonedaObj ℤ (D.obj i)).homology (n + 1))
    (hx : homologyMap (repCochainPostcomp ℤ P.complex (c.ι i)) (n + 1) x = 0) :
    ∃ (j : ℕ) (hij : i ≤ j),
      homologyMap (repCochainPostcomp ℤ P.complex (D.map i j hij)) (n + 1) x = 0 := by
  let Ci := P.complex.linearYonedaObj ℤ (D.obj i)
  let C := P.complex.linearYonedaObj ℤ A
  let φ := repCochainPostcomp ℤ P.complex (c.ι i)
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (Ci.homologyπ (n + 1))).mp inferInstance x
  have hz : C.homologyπ (n + 1) (cyclesMap φ (n + 1) z) = 0 := by
    have he := ConcreteCategory.congr_hom (homologyπ_naturality φ (n + 1)) z
    change homologyMap φ (n + 1) (Ci.homologyπ (n + 1) z) =
      C.homologyπ (n + 1) (cyclesMap φ (n + 1) z) at he
    exact he.symm.trans hx
  obtain ⟨y, hy⟩ := cochain_boundary_of_class_zero C n (cyclesMap φ (n + 1) z) hz
  let y' : P.complex.X n ⟶ A := y
  let u : P.complex.X (n + 1) ⟶ D.obj i := Ci.iCycles (n + 1) z
  have hdy : P.complex.d (n + 1) n ≫ y' = u ≫ c.ι i := by
    have he := ConcreteCategory.congr_hom (cyclesMap_i φ (n + 1)) z
    exact hy.trans he
  obtain ⟨j, v, hv⟩ := c.lift_finitelyPresented (P.complex.X n) y'
  let k := max i j
  let vk := v ≫ D.map j k (le_max_right i j)
  let uk := u ≫ D.map i k (le_max_left i j)
  let r := uk - P.complex.d (n + 1) n ≫ vk
  have hr : r ≫ c.ι k = 0 := by
    change (uk - P.complex.d (n + 1) n ≫ vk) ≫ c.ι k = 0
    rw [Preadditive.sub_comp]
    change (u ≫ D.map i k _) ≫ c.ι k -
      (P.complex.d (n + 1) n ≫ (v ≫ D.map j k _)) ≫ c.ι k = 0
    rw [Category.assoc, c.comm, Category.assoc, Category.assoc, c.comm,
      hv, hdy, sub_self]
  obtain ⟨l, hkl, hl⟩ := c.eventually_zero_hom (P.complex.X (n + 1)) k r hr
  refine ⟨l, (le_max_left i j).trans hkl, ?_⟩
  apply resolution_cohomologyMap_zero_of_boundary P n (D.map i l _) z
    (vk ≫ D.map k l hkl)
  have he : uk ≫ D.map k l hkl = (P.complex.d (n + 1) n ≫ vk) ≫ D.map k l hkl := by
    exact sub_eq_zero.mp ((Preadditive.sub_comp _ _ _).symm.trans hl)
  change P.complex.d (n + 1) n ≫ vk ≫ D.map k l hkl = u ≫ D.map i l _
  rw [← Category.assoc, ← he]
  change (u ≫ D.map i k _) ≫ D.map k l _ = u ≫ D.map i l _
  rw [Category.assoc, D.map_comp]

theorem TypeFPInfinity.cohomology_colimit_kernel
    (hG : TypeFPInfinity G) (D : SequentialRepresentationDiagram G)
    (A : Rep.{0} ℤ G) (c : D.ColimitCocone A) (n i : ℕ)
    (x : groupCohomology (D.obj i) (n + 1))
    (hx : groupCohomology.map (MonoidHom.id G) (c.ι i) (n + 1) x = 0) :
    ∃ (j : ℕ) (hij : i ≤ j),
      groupCohomology.map (MonoidHom.id G) (D.map i j hij) (n + 1) x = 0 := by
  obtain ⟨P, hP⟩ := hG (n + 1)
  let : Module.FinitePresentation ℤ[G] (P.complex.X n).ρ.asModule :=
    projectiveRepresentation_finitePresentation _ (hP n (by omega))
  let : Module.Finite ℤ[G] (P.complex.X (n + 1)).ρ.asModule := hP (n + 1) le_rfl
  have hz : homologyMap (repCochainPostcomp ℤ P.complex (c.ι i)) (n + 1)
      ((coefficientNaturalCohomologyIso P (D.obj i) (n + 1)).hom x) = 0 := by
    have he := ConcreteCategory.congr_hom
      (coefficientNaturalCohomologyIso_naturality P (c.ι i) (n + 1)) x
    change (coefficientNaturalCohomologyIso P A (n + 1)).hom
        (groupCohomology.map (MonoidHom.id G) (c.ι i) (n + 1) x) =
      homologyMap (repCochainPostcomp ℤ P.complex (c.ι i)) (n + 1)
        ((coefficientNaturalCohomologyIso P (D.obj i) (n + 1)).hom x) at he
    rw [hx, map_zero] at he
    exact he.symm
  obtain ⟨j, hij, hj⟩ := finiteResolutionCohomology_colimit_kernel D A c P n i
    ((coefficientNaturalCohomologyIso P (D.obj i) (n + 1)).hom x) hz
  refine ⟨j, hij, ?_⟩
  apply (coefficientNaturalCohomologyIso P (D.obj j) (n + 1)).toLinearEquiv.injective
  change (coefficientNaturalCohomologyIso P (D.obj j) (n + 1)).hom.hom
      (groupCohomology.map (MonoidHom.id G) (D.map i j hij) (n + 1) x) =
    (coefficientNaturalCohomologyIso P (D.obj j) (n + 1)).hom.hom 0
  have he := ConcreteCategory.congr_hom
    (coefficientNaturalCohomologyIso_naturality P (D.map i j hij) (n + 1)) x
  change (coefficientNaturalCohomologyIso P (D.obj j) (n + 1)).hom
      (groupCohomology.map (MonoidHom.id G) (D.map i j hij) (n + 1) x) =
    homologyMap (repCochainPostcomp ℤ P.complex (D.map i j hij)) (n + 1)
      ((coefficientNaturalCohomologyIso P (D.obj i) (n + 1)).hom x) at he
  simpa only [map_zero, hj] using he

end PolycyclicRecognition

end

end OAI
