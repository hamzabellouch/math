import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SequentialCohomologyKernel

namespace OAI

/-! # Lifting cohomology classes from a sequential coefficient colimit -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem finiteResolutionCohomology_colimit_surj
    (D : SequentialRepresentationDiagram G) (A : Rep.{0} ℤ G) (c : D.ColimitCocone A)
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    [Module.FinitePresentation ℤ[G] (P.complex.X n).ρ.asModule]
    [Module.Finite ℤ[G] (P.complex.X (n + 1)).ρ.asModule]
    (x : (P.complex.linearYonedaObj ℤ A).homology n) :
    ∃ (i : ℕ) (y : (P.complex.linearYonedaObj ℤ (D.obj i)).homology n),
      homologyMap (repCochainPostcomp ℤ P.complex (c.ι i)) n y = x := by
  let C := P.complex.linearYonedaObj ℤ A
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance x
  let u : P.complex.X n ⟶ A := C.iCycles n z
  have hdu : P.complex.d (n + 1) n ≫ u = 0 :=
    ConcreteCategory.congr_hom (C.iCycles_d n (n + 1)) z
  obtain ⟨i, v, hv⟩ := c.lift_finitelyPresented (P.complex.X n) u
  have hr : (P.complex.d (n + 1) n ≫ v) ≫ c.ι i = 0 := by
    rw [Category.assoc, hv, hdu]
  obtain ⟨j, hij, hj⟩ := c.eventually_zero_hom (P.complex.X (n + 1)) i
    (P.complex.d (n + 1) n ≫ v) hr
  let Cj := P.complex.linearYonedaObj ℤ (D.obj j)
  let v' := v ≫ D.map i j hij
  have hv' : P.complex.d (n + 1) n ≫ v' = 0 := by
    change P.complex.d (n + 1) n ≫ v ≫ D.map i j hij = 0
    rw [← Category.assoc, hj]
  let z' : Cj.cycles n := Cj.cyclesMk v' (n + 1) (by simp) hv'
  let φ := repCochainPostcomp ℤ P.complex (c.ι j)
  have he : cyclesMap φ n z' = z := by
    apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
    have hm := ConcreteCategory.congr_hom (cyclesMap_i φ n) z'
    change C.iCycles n (cyclesMap φ n z') = C.iCycles n z
    change C.iCycles n (cyclesMap φ n z') = Cj.iCycles n z' ≫ c.ι j at hm
    have hz' : Cj.iCycles n z' = v' := Cj.i_cyclesMk v' (n + 1) (by simp) hv'
    rw [hm]
    change (Cj.iCycles n z' : P.complex.X n ⟶ D.obj j) ≫ c.ι j = u
    rw [hz']
    change (v ≫ D.map i j hij) ≫ c.ι j = u
    rw [Category.assoc, c.comm, hv]
  refine ⟨j, Cj.homologyπ n z', ?_⟩
  have hm := ConcreteCategory.congr_hom (homologyπ_naturality φ n) z'
  change homologyMap φ n (Cj.homologyπ n z') = C.homologyπ n (cyclesMap φ n z') at hm
  exact hm.trans (congrArg (C.homologyπ n) he)

theorem TypeFPInfinity.cohomology_colimit_surj
    (hG : TypeFPInfinity G) (D : SequentialRepresentationDiagram G)
    (A : Rep.{0} ℤ G) (c : D.ColimitCocone A) (n : ℕ) (x : groupCohomology A n) :
    ∃ (i : ℕ) (y : groupCohomology (D.obj i) n),
      groupCohomology.map (MonoidHom.id G) (c.ι i) n y = x := by
  obtain ⟨P, hP⟩ := hG (n + 1)
  let : Module.FinitePresentation ℤ[G] (P.complex.X n).ρ.asModule :=
    projectiveRepresentation_finitePresentation _ (hP n (by omega))
  let : Module.Finite ℤ[G] (P.complex.X (n + 1)).ρ.asModule := hP (n + 1) le_rfl
  obtain ⟨i, y, hy⟩ := finiteResolutionCohomology_colimit_surj D A c P n
    ((coefficientNaturalCohomologyIso P A n).hom x)
  let e := coefficientNaturalCohomologyIso P (D.obj i) n
  refine ⟨i, e.inv y, ?_⟩
  apply (coefficientNaturalCohomologyIso P A n).toLinearEquiv.injective
  have hn := ConcreteCategory.congr_hom
    (coefficientNaturalCohomologyIso_naturality P (c.ι i) n) (e.inv y)
  have hei : e.hom (e.inv y) = y := ConcreteCategory.congr_hom e.inv_hom_id y
  change (coefficientNaturalCohomologyIso P A n).hom
    (groupCohomology.map (MonoidHom.id G) (c.ι i) n (e.inv y)) =
      homologyMap (repCochainPostcomp ℤ P.complex (c.ι i)) n
        (e.hom (e.inv y)) at hn
  rw [hei] at hn
  exact hn.trans hy

end PolycyclicRecognition

end

end OAI
