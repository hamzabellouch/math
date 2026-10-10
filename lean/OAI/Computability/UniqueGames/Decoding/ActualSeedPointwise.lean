import OAI.Computability.UniqueGames.Decoding.ActualAdviceUpperLemmas

namespace OAI

section

/-!
Pointwise and uniform-law identification of the retained projection seed with
the actual decoder draw. Auxiliary slots at full positions affect neither the
projection nor the displayed target question. The entire target map is retained
when it is repacked into its independent hidden and complement components.
-/

namespace UniqueGamesTheorem.Decoder.ActualSeedPointwise

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Foundations.Games
open ActualSource
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

theorem rawProjection_congr_slots {k : Nat} (rhsB : Fin k → Bool)
    (J : Finset (Fin k)) (slot slot' : Fin k → PartnerProjection.Slot)
    (h : ∀ j, j ∈ J → slot j = slot' j) :
    RawPartnerTarget.rawProjection rhsB J slot =
      RawPartnerTarget.rawProjection rhsB J slot' := by
  have hp : PartnerLinear.projection rhsB (PartnerMapCoordinates.activeOf J) slot =
      PartnerLinear.projection rhsB (PartnerMapCoordinates.activeOf J) slot' := by
    apply LinearMap.ext
    intro x
    change PartnerProjection.project rhsB (PartnerMapCoordinates.activeOf J) slot x =
      PartnerProjection.project rhsB (PartnerMapCoordinates.activeOf J) slot' x
    apply PartnerProjection.partner_ext
    · rfl
    · rfl
    · funext j
      by_cases hj : j ∈ J
      · simp [PartnerProjection.project, PartnerMapCoordinates.activeOf, hj, h j hj]
      · simp [PartnerProjection.project, PartnerMapCoordinates.activeOf, hj]
  simp only [RawPartnerTarget.rawProjection, hp]

theorem supported_congr_slots {k : Nat} {Id Name : Type}
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (occ : Fin k → Id)
    (slot slot' : Fin k → PartnerProjection.Slot)
    (h : ∀ j, j ∈ J → slot j = slot' j) :
    RawPrivateTable.supported J names occ slot =
      RawPrivateTable.supported J names occ slot' := by
  apply Subtype.ext
  funext j
  by_cases hj : j ∈ J
  · simp [RawPrivateTable.supported, RawPrivateTable.displayed, hj, h j hj]
  · simp [RawPrivateTable.supported, RawPrivateTable.displayed, hj]

variable {k s d rs : Nat}

/-- This applies to every hidden draw, with all its other data fixed. -/
theorem observedAgreement_changePositions (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector rs))
    (slot : Fin k → PartnerProjection.Slot)
    (hslot : ∀ j, j ∈ draw.singletons → draw.positions j = slot j) :
    VisiblePolicies.observedAgreement S labeling good draw =
      VisiblePolicies.observedAgreement S labeling good { draw with positions := slot } := by
  cases draw with
  | mk J occ positions A M T =>
    have hp := rawProjection_congr_slots (fun j => toBit (ActualGame.rhs S (occ j)))
      J positions slot hslot
    have hs := supported_congr_slots J (ActualGame.names S) occ positions slot hslot
    simp only [VisiblePolicies.observedAgreement, AdviceExperiment.leftObservation,
      AdviceExperiment.rightObservation, AdviceExperiment.projection,
      RawPrivateTable.projection, hp, hs]
    rfl

/-- Seed and actual-draw agreement before averaging any sampled map. -/
theorem seedAgreement_pointwise (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (occ : Fin k → Fin S.occurrences) (A : Alphabet s →ₗ[F2] Vector rs)
    (choices : Fin k → PaddedLaw.ProjectionChoice)
    (slot : Fin k → PartnerProjection.Slot)
    (hslot : ∀ j, j ∈ PaddedLaw.choiceMask choices →
      PaddedLaw.choiceSlots choices j = slot j)
    (Y : RawPartnerTarget.RawPoint (PaddedLaw.choiceMask choices) →ₗ[F2]
      (Alphabet s × Vector d)) :
    VisiblePolicies.observedAgreement S labeling good
        (AdviceLaw.seedToActualDraw occ A ⟨choices, Y⟩) =
      VisiblePolicies.observedAgreement S labeling good
        (ActualAdviceUpper.actualDraw S A (PaddedLaw.choiceMask choices) occ slot
          ((LinearMap.snd F2 (Alphabet s) (Vector d)).comp Y)
          ((LinearMap.fst F2 (Alphabet s) (Vector d)).comp Y)) :=
  observedAgreement_changePositions S labeling good
    (AdviceLaw.seedToActualDraw occ A ⟨choices, Y⟩) slot hslot

private theorem seedAgreement_repack_at (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (occ : Fin k → Fin S.occurrences) (A : Alphabet s →ₗ[F2] Vector rs)
    (choices : Fin k → PaddedLaw.ProjectionChoice) (J : Finset (Fin k))
    (hJ : PaddedLaw.choiceMask choices = J)
    (slot : Fin k → PartnerProjection.Slot)
    (hslot : ∀ j, j ∈ PaddedLaw.choiceMask choices →
      PaddedLaw.choiceSlots choices j = slot j) :
    (FiniteDistribution.uniform
      (RawPartnerTarget.RawPoint (PaddedLaw.choiceMask choices) →ₗ[F2]
        (Alphabet s × Vector d))).expectation (fun Y =>
          VisiblePolicies.observedAgreement S labeling good
            (AdviceLaw.seedToActualDraw occ A ⟨choices, Y⟩)) =
      (FiniteDistribution.uniform
        ((RawPartnerTarget.RawPoint J →ₗ[F2] Vector d) ×
          (RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s))).expectation (fun TM =>
            VisiblePolicies.observedAgreement S labeling good
              (ActualAdviceUpper.actualDraw S A J occ slot TM.1 TM.2)) := by
  subst J
  simp only [FiniteDistribution.expectation_uniform, ← Fintype.expect_eq_sum_div_card]
  apply Fintype.expect_equiv
    ((LinearMap.prodEquiv F2).toEquiv.symm.trans (Equiv.prodComm _ _))
  intro Y
  exact seedAgreement_pointwise S labeling good occ A choices slot hslot Y

/-- Exact uniform-law identification with Bernoulli-mask and iid-slot sampling.
All dependent mask transport is confined to this theorem. -/
theorem seedAgreement_repack (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (occ : Fin k → Fin S.occurrences) (A : Alphabet s →ₗ[F2] Vector rs)
    (mask : Fin k → Bool) (slots : Fin k → Fin 3) :
    (FiniteDistribution.uniform
      (RawPartnerTarget.RawPoint
        (PaddedLaw.choiceMask (AdviceLaw.choicesOfMaskSlots mask slots)) →ₗ[F2]
          (Alphabet s × Vector d))).expectation (fun Y =>
            VisiblePolicies.observedAgreement S labeling good
              (AdviceLaw.seedToActualDraw occ A
                ⟨AdviceLaw.choicesOfMaskSlots mask slots, Y⟩)) =
      (FiniteDistribution.uniform
        ((RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
          (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2]
            Alphabet s))).expectation (fun TM =>
              VisiblePolicies.observedAgreement S labeling good
                (ActualAdviceUpper.actualDraw S A (Clean.NativeExperiment.maskSet mask)
                  occ (fun j => Clean.ActualAdviceBridge.indexSlot (slots j)) TM.1 TM.2)) := by
  apply seedAgreement_repack_at S labeling good occ A
    (AdviceLaw.choicesOfMaskSlots mask slots) (Clean.NativeExperiment.maskSet mask)
    (AdviceLaw.choices_mask mask slots)
  intro j hj
  have hmask : mask j = true := by
    rw [AdviceLaw.choices_mask] at hj
    simpa only [Clean.NativeExperiment.maskSet, Finset.mem_filter, Finset.mem_univ,
      true_and] using hj
  exact AdviceLaw.choices_active_slot mask slots j hmask

end
end UniqueGamesTheorem.Decoder.ActualSeedPointwise

end

end OAI
