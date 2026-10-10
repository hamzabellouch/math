import OAI.CategoryTheory.ThickClosure.GradedSplit

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.Unroll
open CategoryTheory CategoryTheory.Limits HomologicalComplex ZeroObject
universe u v w
variable (R : Type u) [Ring R] (D : ℕ)
variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]
  [HasDerivedCategory.{v} (ModuleCat.{u} R)]

instance derived_preservesZero : (derivedFunctor R D).PreservesZeroMorphisms := by
  have hq : IsZero ((q R D).obj (0 : PC R D)) :=
    HahnWilson.CyclicStructure.isZero_map (HomologicalComplex.quasiIso (ModuleCat.{u} R)
      (.down (ZMod D))) (q R D) (isZero_zero _)
  have hu : IsZero ((derivedFunctor R D).obj ((q R D).obj (0 : PC R D))) :=
    IsZero.of_iso ((GradedSplit.F₀ R D).map_isZero (isZero_zero _))
      ((derivedFactors R D).app _)
  have hz : IsZero ((derivedFunctor R D).obj (0 : PD R D)) :=
    IsZero.of_iso hu ((derivedFunctor R D).mapIso ((hq.iso (isZero_zero _)).symm))
  exact Functor.preservesZeroMorphisms_of_map_zero_object (hz.iso (isZero_zero _))

end HahnWilson.Unroll

namespace HahnWilson.HomologyBridge
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HahnWilson.PrincipalModules HahnWilson.PeriodicSplitting HahnWilson.PeriodicDerived
open HahnWilson.Unroll HahnWilson.GradedSplit
universe u v w
variable (R : Type u) [Ring R] (D : ℕ)
variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]
  [HasDerivedCategory.{v} (ModuleCat.{u} R)]

lemma zero_iff {X Y : PeriodicDerived R D} (f : X ⟶ Y) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map ((derivedFunctor R D).map f) = 0 ↔
      (homology R D (-(n : ZMod D))).map f = 0 := by
  let e := derivedHomologyIso R D n
  have h := e.hom.naturality f
  constructor
  · intro hf
    apply (cancel_epi (e.hom.app X)).mp
    rw [← h]
    change (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
      ((derivedFunctor R D).map f) ≫ _ = _
    rw [hf, CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]
  · intro hf
    apply (cancel_mono (e.hom.app Y)).mp
    change (derivedFunctor R D ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map f ≫ _ = _
    rw [h]
    change _ ≫ (homology R D (-(n : ZMod D))).map f = _
    rw [hf, CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]

lemma all_zero_iff {X Y : PeriodicDerived R D} (f : X ⟶ Y) :
    (∀ n : ℤ, (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
      ((derivedFunctor R D).map f) = 0) ↔
      ∀ i : ZMod D, (homology R D i).map f = 0 := by
  constructor
  · intro h i
    obtain ⟨n,hn⟩ := ZMod.intCast_surjective (-i)
    have hi : -(n : ZMod D) = i := by rw [hn, neg_neg]
    exact hi ▸ (zero_iff R D f n).mp (h n)
  · intro h n
    exact (zero_iff R D f n).mpr (h _)

omit [HasDerivedCategory.{v} (ModuleCat.{u} R)] in
lemma torsion_of_iso {M N : ModuleCat.{u} R} (e : M ≅ N)
    (h : IsTorsionModule R N) : IsTorsionModule R M := by
  intro x
  obtain ⟨a,ha,hx⟩ := h (e.hom x)
  refine ⟨a,ha,?_⟩
  apply e.toLinearEquiv.injective
  simpa using hx

lemma torsion (X : PeriodicDerived R D)
    (h : ∀ i, IsTorsionModule R ((homology R D i).obj X)) (n : ℤ) :
    IsTorsionModule R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
      ((derivedFunctor R D).obj X)) :=
  torsion_of_iso R ((derivedHomologyIso R D n).app X) (h _)

lemma torsion_shift_diagonal (L : ZMod D → ModuleCat.{u} R)
    (h : ∀ i, IsTorsionModule R (L i)) (m n : ℤ) :
    IsTorsionModule R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
      (((F₀ R D).obj (dg R D L))⟦m⟧)) := by
  let e := ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).shiftIso m n (m+n) rfl).app
    ((F₀ R D).obj (dg R D L))
  exact torsion_of_iso R (e ≪≫ F₀DiagonalHomologyIso R D L (m+n)) (h _)

end HahnWilson.HomologyBridge

end

end OAI
