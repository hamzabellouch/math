import OAI.CategoryTheory.Thomason.Gray.GrayMappingInterchangeEvaluation
import OAI.CategoryTheory.Thomason.Simplicial.PosetSieveNaturality
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionUnions
import OAI.CategoryTheory.Thomason.Transfer.NonsingularFaceGluing

namespace OAI

section

/-! # Finite-poset unit comparisons from the strict Gray input alone

Geometric gluing and direct realization of the Gray prisms remove every
Kan–Quillen hypothesis from these unit comparisons. The exact right Gray
and finite internal-hom truncation inputs remain explicit.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace RelativePrismData

theorem weakEquivalence_iff_direct {E : Type} [PartialOrder E] (D : RelativePrismData E)
    (h : NormalizedSimplexIdentities) [StrictColimitsInput] (G : RightGrayInput h)
    (aw : SimplexComplex.AlexanderWhitneyInput h) :
    h.streetWeakEquivalences (h.categorification.map (nerveMap D.first.monotone.functor)) ↔
      h.streetWeakEquivalences (h.categorification.map (nerveMap D.last.monotone.functor)) := by
  have hfirst := D.prism_endpoint h G false
  have hlast := D.prism_endpoint h G true
  let W : (h.categorification.obj (nerve E) ⟶ h.categorification.obj (nerve E)) → Prop :=
    fun f => h.streetWeakEquivalences f
  exact (congrArg W hfirst).symm.to_iff.trans
    ((G.cylinder_weakEquivalence_iff_direct aw (D.prism h G)).trans
      (congrArg W hlast).to_iff)

end RelativePrismData

theorem nerve_greatest_point_weakEquivalences_direct {P : Type} [PartialOrder P] (x : P) (hx : ∀ y, y ≤ x) :
    realizationWeakEquivalences (nerveMap (posetFromPoint x).monotone.functor) ∧
      realizationWeakEquivalences (nerveMap (posetToPoint P).monotone.functor) := by
  apply retraction_weakEquivalences realizationWeakEquivalences
  · rw [← orderNerveMap_comp, poset_point_retraction, orderNerveMap_id]
  · rw [← orderNerveMap_comp]
    apply (RealizedCylinder.weakEquivalence_iff (orderNerveHomotopy OrderHom.id
      ((posetFromPoint x).comp (posetToPoint P)) hx)).mp
    rw [orderNerveMap_id]
    exact realizationWeakEquivalences.id_mem _

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

theorem unit_of_point_iso_direct
    {X : SSet.{0}} (e : (Δ[0] : SSet.{0}) ≅ X) :
    realizationWeakEquivalences (h.categorificationAdjunction.unit.app X) := by
  have := h.unit_point_isIso
  exact (weak_component_iff realizationWeakEquivalences h.categorificationAdjunction.unit
    e.hom (realizationWeakEquivalences.of_isIso _)
    (realizationWeakEquivalences.of_isIso _)).mp
      (realizationWeakEquivalences.of_isIso _)

/-- The same contraction is weak after actual strict categorification. -/
theorem categorified_greatest_point_weakEquivalences_direct
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)

    {P : Type} [PartialOrder P] (x : P) (hx : ∀ y, y ≤ x) :
    h.streetWeakEquivalences (h.posetMap (posetFromPoint x)) ∧
      h.streetWeakEquivalences (h.posetMap (posetToPoint P)) := by
  have : h.streetWeakEquivalences.HasTwoOutOfThreeProperty :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).HasTwoOutOfThreeProperty
  have : h.streetWeakEquivalences.IsStableUnderRetracts :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).IsStableUnderRetracts
  have : h.streetWeakEquivalences.ContainsIdentities :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).ContainsIdentities
  apply retraction_weakEquivalences h.streetWeakEquivalences
  · rw [← h.posetMap_comp, poset_point_retraction, h.posetMap_id]
  · rw [← h.posetMap_comp]
    apply ((greatestElementPrism x hx).weakEquivalence_iff_direct h G aw).mp
    change h.streetWeakEquivalences (h.posetMap (OrderHom.id : P →o P))
    rw [h.posetMap_id]
    exact h.streetWeakEquivalences.id_mem _

/-- The finite-poset unit input is proved here for every greatest-element
poset; finiteness is not needed in this case. -/
theorem unit_greatestElement_direct (G : RightGrayInput h)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    {P : Type} [PartialOrder P] (x : P) (hx : ∀ y, y ≤ x) :
    realizationWeakEquivalences (h.categorificationAdjunction.unit.app (nerve P)) := by
  exact (weak_component_iff realizationWeakEquivalences h.categorificationAdjunction.unit
    (nerveMap (posetFromPoint x).monotone.functor)
    (nerve_greatest_point_weakEquivalences_direct x hx).1
    (h.categorified_greatest_point_weakEquivalences_direct G aw x hx).1).mp
      (h.unit_of_point_iso_direct (SSet.stdSimplex.isoNerve 0))

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

theorem unit_of_point_iso_direct
    {X : SSet.{0}} (e : (Δ[0] : SSet.{0}) ≅ X) :
    realizationWeakEquivalences ((r.categorificationAdjunction h).unit.app X) := by
  have := r.unit_point_isIso h
  exact (weak_component_iff realizationWeakEquivalences (r.categorificationAdjunction h).unit
    e.hom (realizationWeakEquivalences.of_isIso _)
    (realizationWeakEquivalences.of_isIso _)).mp
      (realizationWeakEquivalences.of_isIso _)

/-- Reflection of the strict contraction gives actual finite Street weak
equivalences on both the point inclusion and the collapse. -/
theorem categorified_greatest_point_weakEquivalences_direct
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    {P : Type} [PartialOrder P] (x : P) (hx : ∀ y, y ≤ x) :
    realizationWeakEquivalences ((h.finiteStreetNerve (n + 1)).map
      (r.reflect.map (h.posetMap (posetFromPoint x)))) ∧
    realizationWeakEquivalences ((h.finiteStreetNerve (n + 1)).map
      (r.reflect.map (h.posetMap (posetToPoint P)))) := by
  let F := h.categorification ⋙ r.reflect ⋙ h.finiteStreetNerve (n + 1)
  apply retraction_weakEquivalences realizationWeakEquivalences
  · change F.map (nerveMap (posetFromPoint x).monotone.functor) ≫
      F.map (nerveMap (posetToPoint P).monotone.functor) = 𝟙 _
    rw [← F.map_comp, ← orderNerveMap_comp, poset_point_retraction,
      orderNerveMap_id, F.map_id]
  · change realizationWeakEquivalences (F.map (nerveMap (posetToPoint P).monotone.functor) ≫
      F.map (nerveMap (posetFromPoint x).monotone.functor))
    rw [← F.map_comp, ← orderNerveMap_comp]
    apply ((greatestElementPrism x hx).finite_weakEquivalence_iff_direct h G t r aw).mp
    change realizationWeakEquivalences (F.map (nerveMap (OrderHom.id : P →o P).monotone.functor))
    rw [orderNerveMap_id, F.map_id]
    exact realizationWeakEquivalences.id_mem _

/-- The actual unit comparison is weak on all greatest-element posets in
dimension n+1. No finite-poset unit theorem is used. -/
theorem unit_greatestElement_direct
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    {P : Type} [PartialOrder P] (x : P) (hx : ∀ y, y ≤ x) :
    realizationWeakEquivalences ((r.categorificationAdjunction h).unit.app (nerve P)) := by
  exact (weak_component_iff realizationWeakEquivalences (r.categorificationAdjunction h).unit
    (nerveMap (posetFromPoint x).monotone.functor)
    (nerve_greatest_point_weakEquivalences_direct x hx).1
    (r.categorified_greatest_point_weakEquivalences_direct h G t aw x hx).1).mp
      (r.unit_of_point_iso_direct h (SSet.stdSimplex.isoNerve 0))

end FiniteReflectionInput

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Finite-poset units in omega dimension require the strict Gray input,
with no Kan–Quillen, extension, transfer, or localization assumption. -/
theorem unit_finite_poset_fromGray (G : RightGrayInput h)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (P : Type) [PartialOrder P] [Finite P] :
    realizationWeakEquivalences (h.categorificationAdjunction.unit.app (nerve P)) := by
  let s := h.constructedOmegaPosetSieveInput.allDimensions
  refine finite_poset_comparison_induction h.categorificationAdjunction.unit
    constructedSimplicialGluingUnconditional ?_ ?_ ?_ ?_ P
  · intro Q _ _
    have := h.unit_empty_isIso Q
    exact realizationWeakEquivalences.of_isIso _
  · intro Q _ x hx
    exact h.unit_greatestElement_direct G aw x hx
  · intro Q _ _ A hA
    exact s.omega_nerve_mono A hA
  · intro Q _ _ A B hA hB hc
    exact h.street_sieve_maps_isPushout s A B hA hB hc

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The finite-dimensional unit comparison only adds the specified
interval internal-hom truncation input. -/
theorem unit_finite_poset_fromGray (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (P : Type) [PartialOrder P] [Finite P] :
    realizationWeakEquivalences ((r.categorificationAdjunction h).unit.app (nerve P)) := by
  let s := h.constructedOmegaPosetSieveInput.allDimensions
  refine finite_poset_comparison_induction (r.categorificationAdjunction h).unit
    constructedSimplicialGluingUnconditional ?_ ?_ ?_ ?_ P
  · intro Q _ _
    have := r.unit_empty_isIso h Q
    exact realizationWeakEquivalences.of_isIso _
  · intro Q _ x hx
    exact r.unit_greatestElement_direct h G t aw x hx
  · intro Q _ _ A hA
    exact r.posetStreet_mono h s A hA
  · intro Q _ _ A B hA hB hc
    exact r.street_sieve_maps_isPushout h s A B hA hB hc

end FiniteReflectionInput

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Strict Gray cylinder comparisons and finite internal-hom truncation give
the finite-poset unit comparisons. -/
theorem finitePosetUnitInput_fromGray (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h) : PublishedFinitePosetUnitInput h where
  omega P := h.unit_finite_poset_fromGray G aw P
  finite _ r P := r.unit_finite_poset_fromGray h G t aw P

/-- On finite-poset nerves the actual Street and ordinary realization weak
criteria agree using only the right Gray data. -/
theorem finite_poset_map_weakEquivalence_fromGray
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    {P Q : Type} [PartialOrder P] [PartialOrder Q] [Finite P] [Finite Q]
    (f : nerve P ⟶ nerve Q) :
    h.streetWeakEquivalences (h.categorification.map f) ↔ realizationWeakEquivalences f :=
  map_iff_of_unit_components realizationWeakEquivalences h.categorificationAdjunction.unit f
    (h.unit_finite_poset_fromGray G aw P) (h.unit_finite_poset_fromGray G aw Q)

end NormalizedSimplexIdentities

end Thomason.Construction

end

end OAI
