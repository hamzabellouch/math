import OAI.CategoryTheory.ThickClosure.PeriodicHom
import OAI.CategoryTheory.ThickClosure.LocalizationHom

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.PeriodicDerivedHom
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HahnWilson.PeriodicSplitting HahnWilson.PeriodicDerived HahnWilson.PeriodicHom
universe u w
variable {R : Type u} [Ring R] {D : ℕ}
variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]

abbrev Qh : HomotopyCategory (ModuleCat.{u} R) (.down (ZMod D)) ⥤ PeriodicDerived R D :=
  HomologicalComplexUpToQuasiIso.Qh

omit [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}] in
lemma free_coyoneda_inverts (G : ZMod D → ModuleCat.{u} R) [∀ i, Projective (G i)] :
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).IsInvertedBy
      (coyoneda.obj (Opposite.op (homotopyQuotient.obj (diagonalComplex G)))) := by
  rintro ⟨P⟩ ⟨P'⟩ f hf
  obtain ⟨f, rfl⟩ := homotopyQuotient.map_surjective f
  have hq : QuasiIso f :=
    (HomologicalComplex.mem_quasiIso_iff f).mp
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).mp hf)
  rw [CategoryTheory.isIso_iff_bijective]
  exact free_hom_quasiIso_bijective G f

theorem free_derived_map_bijective (G : ZMod D → ModuleCat.{u} R)
    [∀ i, Projective (G i)] (P : PeriodicComplex R D) :
    Function.Bijective (Qh.map :
      (homotopyQuotient.obj (diagonalComplex G) ⟶ homotopyQuotient.obj P) →
      (Qh.obj (homotopyQuotient.obj (diagonalComplex G)) ⟶
        Qh.obj (homotopyQuotient.obj P))) :=
  HahnWilson.LocalizationHom.map_bijective_of_inverts _ _ _ Qh _ _
    (free_coyoneda_inverts G)

lemma quotient_homology_zero_iff {P P' : PeriodicComplex R D}
    (f : homotopyQuotient.obj P ⟶ homotopyQuotient.obj P') (i : ZMod D) :
    (homology R D i).map (Qh.map f) = 0 ↔
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.down (ZMod D)) i).map f = 0 := by
  let e := HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh (ModuleCat.{u} R)
    (.down (ZMod D)) i
  have he := NatIso.naturality_1 e f
  constructor
  · intro hf
    simpa [hf] using he.symm
  · intro hf
    simpa [hf] using (NatIso.naturality_2 e f).symm

theorem free_derived_zero_iff (G : ZMod D → ModuleCat.{u} R)
    [∀ i, Projective (G i)] (P : PeriodicComplex R D)
    (f : Qh.obj (homotopyQuotient.obj (diagonalComplex G)) ⟶
      Qh.obj (homotopyQuotient.obj P)) :
    f = Qh.map 0 ↔ ∀ i, (homology R D i).map f = 0 := by
  obtain ⟨g, rfl⟩ := (free_derived_map_bijective G P).2 f
  rw [(free_derived_map_bijective G P).1.eq_iff]
  obtain ⟨g, rfl⟩ := homotopyQuotient.map_surjective g
  rw [HomotopyCategory.quotient_map_eq_zero_iff, homotopy_zero_iff]
  apply forall_congr'
  intro i
  rw [quotient_homology_zero_iff]
  change (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.down (ZMod D)) i).map g = 0 ↔ _
  let e := HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (.down (ZMod D)) i
  rw [← NatIso.naturality_1 e g]
  simp only [Preadditive.IsIso.comp_left_eq_zero, Preadditive.IsIso.comp_right_eq_zero]
  rfl

end HahnWilson.PeriodicDerivedHom

end

end OAI
