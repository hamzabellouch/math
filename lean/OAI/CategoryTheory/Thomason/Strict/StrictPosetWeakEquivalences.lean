import OAI.CategoryTheory.Thomason.Simplicial.HornWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.LoopDimensionShift
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Simplicial.RealizationSubcomplexSemantics
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeFunctor
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory

namespace OAI

section

/-! # Joint labels agree with intersections of poset sieves -/

namespace Thomason.Construction

open CategoryTheory StrictOmegaCategory

/-- The characteristic label of an intersection is the maximum of the two labels. -/
theorem sieveCharacteristic_inter {E : Type} [PartialOrder E]
    (A B : Set E) (hA : IsLowerSet A) (hB : IsLowerSet B) (x : E) :
    sieveCharacteristic (A ∩ B) (hA.inter hB) x =
      max (sieveCharacteristic A hA x) (sieveCharacteristic B hB x) := by
  classical
  have hzero : sieveCharacteristic (A ∩ B) (hA.inter hB) x = 0 ↔
      sieveCharacteristic A hA x = 0 ∧ sieveCharacteristic B hB x = 0 := by
    simp only [sieveCharacteristic_zero_iff, Set.mem_inter_iff]
  have h01 (i : Fin 2) : i = 0 ∨ i = 1 := by omega
  rcases h01 (sieveCharacteristic A hA x) with ha | ha <;>
    rcases h01 (sieveCharacteristic B hB x) with hb | hb <;> rw [ha, hb]
  · exact (hzero.mpr ⟨ha, hb⟩).trans (by rfl)
  all_goals
    have hz : sieveCharacteristic (A ∩ B) (hA.inter hB) x ≠ 0 := by
      intro hz
      obtain ⟨ha', hb'⟩ := hzero.mp hz
      omega
    have hone : sieveCharacteristic (A ∩ B) (hA.inter hB) x = 1 := by omega
    exact hone.trans (by decide)

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- On the actual categorification, the joint label is exactly the canonical
membership label for the intersected sieve. -/
theorem membershipLabel_inter {E : Type} [PartialOrder E]
    (A B : Set E) (hA : IsLowerSet A) (hB : IsLowerSet B) :
    maxLabel (h.membershipLabel A hA) (h.membershipLabel B hB) =
      h.membershipLabel (A ∩ B) (hA.inter hB) := by
  apply Hom.ext
  funext x
  apply StrictPoset.Cell.ext
  · exact (sieveCharacteristic_inter A B hA hB ((h.posetEvaluation E).toFun x).first).symm
  · exact (sieveCharacteristic_inter A B hA hB ((h.posetEvaluation E).toFun x).last).symm

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Reflection preserves the same joint-label compatibility on all cells. -/
theorem membershipLabel_inter {E : Type} [PartialOrder E]
    (A B : Set E) (hA : IsLowerSet A) (hB : IsLowerSet B) :
    maxLabel (r.membershipLabel h A hA) (r.membershipLabel h B hB) =
      r.membershipLabel h (A ∩ B) (hA.inter hB) := by
  apply Hom.ext
  funext x
  apply StrictPoset.Cell.ext
  · exact (sieveCharacteristic_inter A B hA hB ((r.posetEvaluation h E).toFun x).first).symm
  · exact (sieveCharacteristic_inter A B hA hB ((r.posetEvaluation h E).toFun x).last).symm

end FiniteReflectionInput
end Thomason.Construction

end

section

/-! # Actual realization topology of full strict higher subcategories -/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory Convexity Opposite Topology StrictOmegaCategory
open scoped Simplicial

noncomputable section

variable (h : NormalizedSimplexIdentities) (C : StrictOmegaCategory.{0})

/-- The actual full Street nerve realizes to its intrinsic carrier subspace. -/
def fullStreetCarrierHomeomorph (S : Set C) :
    SSet.toTop.obj (h.streetNerve.obj (C.fullOn S)) ≃ₜ
      Set.ofPred (fun x : SSet.toTop.obj (h.streetNerve.obj C) =>
        RealizationPrism.carrier (h.streetNerve.obj C) x ≤ h.fullStreetSubcomplex C S) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (h.fullStreetIso C S))).trans
    (RealizationPrism.carrierHomeomorph (h.streetNerve.obj C) (h.fullStreetSubcomplex C S))

/-- This homeomorphism preserves the original strict full-inclusion map. -/
theorem fullStreetCarrierHomeomorph_inclusion (S : Set C) :
    (RealizationPrism.carrierInclusion (h.streetNerve.obj C) (h.fullStreetSubcomplex C S)).comp
      (h.fullStreetCarrierHomeomorph C S : C(_, _)) =
        (SSet.toTop.map (h.streetNerve.map (C.fullInclusion S))).hom := by
  have he := congrArg SSet.toTop.map (h.fullStreetIso_hom_ι C S)
  rw [SSet.toTop.map_comp] at he
  exact congrArg (fun f => f.hom) he

/-- Full strict higher subcategories give closed embeddings on actual Street realizations. -/
theorem fullInclusion_realization_isClosedEmbedding (S : Set C) :
    IsClosedEmbedding (SSet.toTop.map (h.streetNerve.map (C.fullInclusion S))).hom := by
  rw [← h.fullStreetCarrierHomeomorph_inclusion C S]
  exact (RealizationPrism.carrier_isClosed (h.streetNerve.obj C)
    (h.fullStreetSubcomplex C S)).isClosedEmbedding_subtypeVal.comp
      (h.fullStreetCarrierHomeomorph C S).isClosedEmbedding

/-- The actual Street weak test for a full inclusion is the weak test of its closed carrier subspace. -/
theorem fullInclusion_streetWeak_iff (S : Set C) :
    h.streetWeakEquivalences (C.fullInclusion S) ↔
      IsWeakHomotopyEquivalence
        (RealizationPrism.carrierInclusion (h.streetNerve.obj C) (h.fullStreetSubcomplex C S)) := by
  change IsWeakHomotopyEquivalence
    (SSet.toTop.map (h.streetNerve.map (C.fullInclusion S))).hom ↔ _
  rw [← h.fullStreetCarrierHomeomorph_inclusion C S]
  have hh := homeomorph_isWeakHomotopyEquivalence (h.fullStreetCarrierHomeomorph C S)
  exact ⟨fun hw => hh.of_precomp hw, fun hw => hh.comp hw⟩

/-- Full Street subcomplexes commute with inverse image along strict higher functors. -/
theorem fullStreetSubcomplex_preimage {D : StrictOmegaCategory.{0}} (f : D ⟶ C) (S : Set C) :
    (h.fullStreetSubcomplex C S).preimage (h.streetNerve.map f) =
      h.fullStreetSubcomplex D (f.toFun ⁻¹' S) := by
  ext n t
  change (∀ a, C.FullCell S (f.toFun (t.toFun a))) ↔
    ∀ a, D.FullCell (f.toFun ⁻¹' S) (t.toFun a)
  simp only [FullCell, source, target, Set.mem_preimage, ← f.map_face]

/-- Realizing a strict full inverse image gives the actual inverse image of the
    corresponding closed Street carrier subspace. -/
def fullStreetPreimageHomeomorph {D : StrictOmegaCategory.{0}} (f : D ⟶ C) (S : Set C) :
    SSet.toTop.obj (h.streetNerve.obj (D.fullOn (f.toFun ⁻¹' S))) ≃ₜ
      ((SSet.toTop.map (h.streetNerve.map f)).hom ⁻¹'
        Set.ofPred (fun x : SSet.toTop.obj (h.streetNerve.obj C) =>
          RealizationPrism.carrier (h.streetNerve.obj C) x ≤ h.fullStreetSubcomplex C S)) :=
  (h.fullStreetCarrierHomeomorph D (f.toFun ⁻¹' S)).trans
    (Homeomorph.setCongr (by
      ext x
      change (RealizationPrism.carrier (h.streetNerve.obj D) x ≤
        h.fullStreetSubcomplex D (f.toFun ⁻¹' S)) ↔
        (RealizationPrism.carrier (h.streetNerve.obj C)
          ((SSet.toTop.map (h.streetNerve.map f)).hom x) ≤ h.fullStreetSubcomplex C S)
      rw [RealizationPrism.carrier_image, SSet.Subcomplex.image_le_iff,
        h.fullStreetSubcomplex_preimage]))

/-- In particular, full fibres of ordered labels realize as closed subspaces. -/
theorem labelFiberInclusion_realization_isClosedEmbedding
    (p : C ⟶ StrictPoset.category (Fin 2)) (e : Fin 2) :
    IsClosedEmbedding (SSet.toTop.map (h.streetNerve.map (labelFiberInclusion p e))).hom :=
  h.fullInclusion_realization_isClosedEmbedding C _

end

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Exact compatibility of Street and ordinary poset weak equivalences -/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory

noncomputable section

variable (h : NormalizedSimplexIdentities)
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

theorem strictPosetNerveMap_naturality (f : P →o Q) :
    h.streetNerve.map (StrictPoset.map f) ≫ h.strictPosetNerveMap Q =
      h.strictPosetNerveMap P ≫ nerveMap f.monotone.functor := by
  ext n s
  rfl

/-- On actual strict posets, the Street weak equivalences are exactly the
    ordinary-nerve realization weak equivalences. -/
theorem strictPoset_map_weak_iff (f : P →o Q) :
    h.streetWeakEquivalences (StrictPoset.map f) ↔
      realizationWeakEquivalences (nerveMap f.monotone.functor) := by
  change realizationWeakEquivalences (h.streetNerve.map (StrictPoset.map f)) ↔ _
  have hP := realizationWeakEquivalences.of_isIso (h.strictPosetNerveMap P)
  have hQ := realizationWeakEquivalences.of_isIso (h.strictPosetNerveMap Q)
  constructor
  · intro hf
    apply realizationWeakEquivalences.of_precomp (h.strictPosetNerveMap P) _ hP
    rw [← h.strictPosetNerveMap_naturality f]
    exact realizationWeakEquivalences.comp_mem _ _ hf hQ
  · intro hf
    apply realizationWeakEquivalences.of_postcomp _ (h.strictPosetNerveMap Q) hQ
    rw [h.strictPosetNerveMap_naturality f]
    exact realizationWeakEquivalences.comp_mem _ _ hP hf

/-- Comparable monotone maps have the same actual Street weak test,
    through the explicitly realized ordinary-nerve homotopy. -/
theorem strictPoset_orderHomotopy_weak_iff (f g : P →o Q) (hfg : ∀ x, f x ≤ g x) :
    h.streetWeakEquivalences (StrictPoset.map f) ↔
      h.streetWeakEquivalences (StrictPoset.map g) := by
  rw [h.strictPoset_map_weak_iff f, h.strictPoset_map_weak_iff g]
  exact RealizedCylinder.weakEquivalence_iff (orderNerveHomotopy f g hfg)

end

end Thomason.Construction.NormalizedSimplexIdentities

end

end OAI
