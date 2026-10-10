import OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleBaseChange
import OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescent
import OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity

namespace OAI

noncomputable section
namespace PiExponent.ReducedComponentAmple
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry

variable {R : Type} [CommRing R] [IsNoetherianRing R]

theorem isAmple_of_finite_closed_cover {ι : Type*} (s : Finset ι) :
    ∀ {X : Scheme.{0}} [IsNoetherian X] [IsReduced X]
      (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
      (L H : LineBundle X), H.IsAmple →
      ∀ I : ι → X.IdealSheafData,
      (∀ x : X, ∃ i ∈ s, x ∈ (I i).support) →
      (∀ i ∈ s, (L.pullback (I i).subschemeι).IsAmple) → L.IsAmple := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro X _ _ p _ L H hH I hcover hample x U hx
    obtain ⟨i,hi,_⟩ := hcover x
    simp at hi
  | @insert i s hi ih =>
    intro X _ _ p _ L H hH I hcover hample
    let Z : Closeds X := s.sup (fun j => (I j).support)
    let J : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Z
    have hJsupport : J.support = Z := by
      ext x
      simp only [J, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    let : IsLocallyNoetherian J.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
    let : CompactSpace J.subscheme :=
      QuasiCompact.compactSpace_of_compactSpace J.subschemeι
    let : IsNoetherian J.subscheme := {}
    let : IsReduced J.subscheme := NumericalAmpleness.isReduced_vanishingIdeal_subscheme Z
    have hH' : (H.pullback J.subschemeι).IsAmple :=
      LineBundle.IsAmple.pullback_closedImmersion H hH J.subschemeι
    have hcoverJ : ∀ x : J.subscheme, ∃ j ∈ s,
        x ∈ ((I j).comap J.subschemeι).support := by
      intro x
      have hx : J.subschemeι x ∈ Z := by
        rw [← hJsupport]
        exact x.property
      have hx' : ∃ j ∈ s, J.subschemeι x ∈ ((I j).support : Set X) := by
        change J.subschemeι x ∈ ((s.sup (fun j => (I j).support) : Closeds X) : Set X) at hx
        rw [Closeds.coe_finset_sup] at hx
        simpa only [Finset.sup_eq_iSup, Function.comp_apply, Set.iSup_eq_iUnion,
          Set.mem_iUnion, exists_prop] using hx
      obtain ⟨j,hj,hxj⟩ := hx'
      refine ⟨j,hj,?_⟩
      rw [Scheme.IdealSheafData.support_comap]
      change J.subschemeι x ∈ ((I j).support : Set X)
      exact hxj
    have hampleJ : ∀ j ∈ s,
        ((L.pullback J.subschemeι).pullback ((I j).comap J.subschemeι).subschemeι).IsAmple := by
      intro j hj
      exact isAmple_comap_restriction (I j) J.subschemeι L
        (hample j (Finset.mem_insert_of_mem hj))
    have hJ : (L.pullback J.subschemeι).IsAmple :=
      ih (J.subschemeι ≫ p) (L.pullback J.subschemeι) (H.pullback J.subschemeι)
        hH' (fun j => (I j).comap J.subschemeι) hcoverJ hampleJ
    apply PiExponentSeshadri.ComponentAmpleDescent.isAmple_of_reduced_closed_cover
      p L H hH (I i) J ?_ (hample i (Finset.mem_insert_self _ _)) hJ
    apply top_unique
    intro x _
    change x ∈ ((I i).support : Set X) ∪ (J.support : Set X)
    obtain ⟨j,hj,hxj⟩ := hcover x
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Or.inl hxj
    · apply Or.inr
      rw [hJsupport]
      exact (Finset.le_sup (f := fun j => (I j).support) hj) hxj

theorem isAmple_of_reduced_components {X : Scheme.{0}} [IsNoetherian X] [IsReduced X]
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (L H : LineBundle X) (hH : H.IsAmple)
    (hcomponents : ∀ C : irreducibleComponents X,
      (L.pullback (CurveCycle.reducedComponentι X C)).IsAmple) : L.IsAmple := by
  classical
  let : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  let : Fintype (irreducibleComponents X) := Fintype.ofFinite _
  let I : irreducibleComponents X → X.IdealSheafData := fun C =>
    Scheme.IdealSheafData.vanishingIdeal
      (⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)
  apply isAmple_of_finite_closed_cover Finset.univ p L H hH I
  · intro x
    have hx : x ∈ ⋃₀ irreducibleComponents X := by
      rw [sUnion_irreducibleComponents]
      trivial
    obtain ⟨C,hC,hxC⟩ := hx
    refine ⟨⟨C,hC⟩, Finset.mem_univ _, ?_⟩
    change x ∈ ((I ⟨C,hC⟩).support : Set X)
    simp only [I, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change x ∈ C
    exact hxC
  · intro C _
    exact hcomponents C

end PiExponent.ReducedComponentAmple

end

end OAI
