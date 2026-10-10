import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionUnions
import OAI.CategoryTheory.Thomason.Strict.FiniteSieveNaturality

namespace OAI

section

/-! # The actual finite-dimensional full-fibre maps detect weak equivalences -/

namespace Thomason.Construction.SieveMap

open CategoryTheory StrictOmegaCategory

variable {n : ℕ} (r : FiniteReflectionInput n)
  {P Q : Type} [PartialOrder P] [PartialOrder Q]
  (A : Set P) (B : Set Q) (f : P →o Q) (hf : ∀ x, f x ∈ B ↔ x ∈ A)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]
  (hA : IsLowerSet A) (hB : IsLowerSet B)

/-- The original finite full-fibre restriction has the same Street weak
property as the reflected categorification of the restricted poset map. -/
theorem finiteFiberMap_weak_iff :
    realizationWeakEquivalences ((h.finiteStreetNerve (n+1)).map
      (finiteFiberMap r A B f hf h hA hB)) ↔
    realizationWeakEquivalences ((h.finiteStreetNerve (n+1)).map
      (r.reflect.map (h.posetMap (restriction A B f hf)))) := by
  have := finiteSieve_isIso r A h hA
  have := finiteSieve_isIso r B h hB
  let N := h.finiteStreetNerve (n+1)
  let i := N.map (r.posetFiberMap h A hA)
  let j := N.map (r.posetFiberMap h B hB)
  let u := N.map (finiteFiberMap r A B f hf h hA hB)
  let v := N.map (r.reflect.map (h.posetMap (restriction A B f hf)))
  have : IsIso i := by dsimp [i]; infer_instance
  have hj : IsIso j := by dsimp [j]; infer_instance
  have hn : i ≫ u = v ≫ j := by
    exact (N.map_comp _ _).symm.trans
      ((congrArg N.map (finiteNaturality r A B f hf h hA hB)).trans (N.map_comp _ _))
  change realizationWeakEquivalences u ↔ realizationWeakEquivalences v
  calc
    _ ↔ realizationWeakEquivalences (i ≫ u) :=
      (realizationWeakEquivalences.cancel_left_of_respectsIso i u).symm
    _ ↔ realizationWeakEquivalences (v ≫ j) := by rw [hn]; rfl
    _ ↔ _ := @MorphismProperty.cancel_right_of_respectsIso _ _
      realizationWeakEquivalences _ _ _ _ v j hj

/-- In every positive finite dimension, the full-fibre map is weak exactly
when the ordinary restricted nerve is weak. -/
theorem finiteFiberMap_weak_iff_nerve [Finite P] [Finite Q]
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h) (kq : KanQuillenPublishedInput.{0}) :
    realizationWeakEquivalences ((h.finiteStreetNerve (n+1)).map
      (finiteFiberMap r A B f hf h hA hB)) ↔
      realizationWeakEquivalences (nerveMap (restriction A B f hf).monotone.functor) :=
  (finiteFiberMap_weak_iff r A B f hf h hA hB).trans
    (r.finite_poset_map_weakEquivalence_iff h G t aw
      h.constructedOmegaPosetSieveInput.allDimensions (constructedSimplicialGluing kq) kq _)

/-- The same concrete full-fibre maps are detected by the Thomason right
adjoint Ex²N. -/
theorem finiteFiberMap_extended_weak_iff_nerve [Finite P] [Finite Q]
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h) (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X : SSet.{0}, realizationWeakEquivalences (canonicalExtension.app X)) :
    realizationWeakEquivalences ((h.finiteStreetNerve (n+1) ⋙ SSet.ex ⋙ SSet.ex).map
      (finiteFiberMap r A B f hf h hA hB)) ↔
      realizationWeakEquivalences (nerveMap (restriction A B f hf).monotone.functor) := by
  have := kq.twoOutOfThree
  exact (realization_ex_twice_iff hj _).trans
    (finiteFiberMap_weak_iff_nerve r A B f hf h hA hB G t aw kq)

end Thomason.Construction.SieveMap

end

end OAI
