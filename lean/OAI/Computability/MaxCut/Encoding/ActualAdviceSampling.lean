import Mathlib
import OAI.Computability.MaxCut.Encoding.VisibleTransfer

namespace OAI

/-!
The stochastic clean upper bound applies to the literal agreement of the two
actual local decoders.  The equality below retains every sampled mask, all
occurrence/position draws, and both independently uniform target maps.
-/

namespace MaxCutGames.Decoder.ActualAdviceSampling

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction MaxCutGames.Soundness
open MaxCutGames.Foundations.Games
open ActualSource ActualAdviceUpper

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

theorem product_probability {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (ν : FiniteDistribution Y) (p : X → Y → Prop) :
    (μ.product ν).probability (fun xy => decide (p xy.1 xy.2)) =
      μ.expectation (fun x => ν.expectation (fun y => if p x y then 1 else 0)) := by
  have hp : (μ.product ν).probability (fun xy => decide (p xy.1 xy.2)) =
      (μ.product ν).expectation (fun xy => if p xy.1 xy.2 then 1 else 0) := by
    simp [FiniteDistribution.probability, FiniteDistribution.expectation, mul_ite]
  rw [hp, FiniteDistribution.expectation_product]

theorem fixedMapSuccess_eq_product {O N D : Type}
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    [AddCommGroup D] [Module F2 D] [Fintype D]
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (policy : Clean.ActualAdviceStochasticBridge.Policies k g D)
    (J : Finset (Fin k)) (Y : RawPartnerTarget.RawPoint J →ₗ[F2] D) :
    Clean.ActualAdviceStochasticBridge.fixedMapSuccess μ g policy J Y =
      (FiniteDistribution.table (fun _ : Fin k => μ)).expectation (fun draw =>
        ((policy.first J (fun j => (draw j).1)
          (Y.comp (Clean.ActualAdviceBridge.projection g J draw))).product
          (policy.second J (Clean.ActualAdviceBridge.displayedQuestion g J draw) Y)).probability
          (fun answers => decide
            (Clean.ActualAdviceBridge.projection g J draw answers.1.val = answers.2.val))) := by
  unfold Clean.ActualAdviceStochasticBridge.fixedMapSuccess
  apply FiniteDistribution.expectation_congr
  intro draw
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum,
    mul_ite, decide_eq_true_eq, mul_one, mul_zero]

theorem fixedMapSuccess_eq_observed (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (μ : FiniteDistribution (Fin S.occurrences × Fin 3))
    (A : Alphabet s →ₗ[F2] Vector rs) (J : Finset (Fin k))
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    Clean.ActualAdviceStochasticBridge.fixedMapSuccess μ (sourceIncidence S)
      (policies S labeling good A) J (AdviceLaw.visibleMap A T M) =
      (FiniteDistribution.table (fun _ : Fin k => μ)).expectation (fun draw =>
        VisiblePolicies.observedAgreement S labeling good
          (actualDraw S A J (fun j => (draw j).1)
            (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) T M)) := by
  rw [fixedMapSuccess_eq_product]
  apply FiniteDistribution.expectation_congr
  intro draw
  rw [source_projection_eq]
  exact policyAgreement_actual S labeling good A J (fun j => (draw j).1)
    (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) T M

/-- The actual experiment, before identifying its visible-map marginal with
the clean-coordinate law. The two private answer draws are already averaged
inside `observedAgreement`. -/
def sampledAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (μ : FiniteDistribution (Fin S.occurrences × Fin 3))
    (A : Alphabet s →ₗ[F2] Vector rs)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) : ℝ :=
  ((Clean.bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform
      ((RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
        (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s))).expectation
      fun TM => (FiniteDistribution.table (fun _ : Fin k => μ)).expectation fun draw =>
        VisiblePolicies.observedAgreement S labeling good
          (actualDraw S A (Clean.NativeExperiment.maskSet mask) (fun j => (draw j).1)
            (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) TM.1 TM.2)

theorem actualSuccess_eq_sampledAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (μ : FiniteDistribution (Fin S.occurrences × Fin 3))
    (A : Alphabet s →ₗ[F2] Vector rs)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    AdviceLaw.actualSuccess μ (sourceIncidence S) A (policies S labeling good A)
        β hβ₀ hβ₁ = sampledAgreement S labeling good μ A β hβ₀ hβ₁ := by
  unfold AdviceLaw.actualSuccess sampledAgreement
  apply FiniteDistribution.expectation_congr
  intro mask
  apply FiniteDistribution.expectation_congr
  intro TM
  exact fixedMapSuccess_eq_observed S labeling good μ A _ TM.1 TM.2

/-- The dimension bound for the true average of the actual observation-local
decoders, including all ranks of the uniformly sampled public row map. -/
theorem sampledAgreement_average_bound (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, (sourceIncidence S).name o i =
      (sourceIncidence S).name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue (sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) :
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
      (fun A => sampledAgreement S labeling good
        (Clean.IncidenceGap.slotLaw (FiniteDistribution.uniform (Fin S.occurrences)))
        A β hβ₀ hβ₁) ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k := by
  simp_rw [← actualSuccess_eq_sampledAgreement]
  exact actual_source_average_bound S labeling good β hβ₀ hβ₁ distinct hopt

end

end MaxCutGames.Decoder.ActualAdviceSampling

/-!
Pointwise and uniform-law identification of the retained projection seed with
the actual decoder draw. Auxiliary slots at full positions affect neither the
projection nor the displayed target question. The entire target map is retained
when it is repacked into its independent hidden and complement components.
-/

namespace MaxCutGames.Decoder.ActualSeedPointwise

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction MaxCutGames.Soundness
open MaxCutGames.Foundations.Games
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

private theorem seedAgreement_repack_at_inline_ActualSeedPointwise (S : Source)
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
  apply seedAgreement_repack_at_inline_ActualSeedPointwise S labeling good occ A
    (AdviceLaw.choicesOfMaskSlots mask slots) (Clean.NativeExperiment.maskSet mask)
    (AdviceLaw.choices_mask mask slots)
  intro j hj
  have hmask : mask j = true := by
    rw [AdviceLaw.choices_mask] at hj
    simpa only [Clean.NativeExperiment.maskSet, Finset.mem_filter, Finset.mem_univ,
      true_and] using hj
  exact AdviceLaw.choices_active_slot mask slots j hmask

end
end MaxCutGames.Decoder.ActualSeedPointwise

/-!
The complete seed used for the lower-bound conditioning argument and the
mask/slot/map experiment used for the clean upper bound have exactly the same
actual decoder success. Unused positions are removed only by the pointwise
observation equality; occurrence IDs and their ordered local copies remain.
-/

namespace MaxCutGames.Decoder.ActualSeedSampling

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction MaxCutGames.Soundness
open MaxCutGames.Foundations.Games
open ActualSource ActualAdviceUpper ActualAdviceSampling

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

theorem uniform_occurrence_slots {O : Type} [Fintype O] [Nonempty O]
    (H : (Fin k → O × Fin 3) → ℝ) :
    (FiniteDistribution.table (fun _ : Fin k =>
      Clean.IncidenceGap.slotLaw (FiniteDistribution.uniform O))).expectation H =
      (FiniteDistribution.uniform (Fin k → O)).expectation (fun occ =>
        (FiniteDistribution.uniform (Fin k → Fin 3)).expectation
          (fun slots => H (fun j => (occ j, slots j)))) := by
  change (((FiniteDistribution.uniform O).product
    (FiniteDistribution.uniform (Fin 3))).iid k).expectation H = _
  rw [Clean.NativeExperiment.expectation_iid_product,
    FiniteDistribution.iid_uniform, FiniteDistribution.iid_uniform]

/-- A named pointwise observable makes the finite expectation permutations
explicit without changing the actual sampled draw. -/
def drawAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs) (mask : Fin k → Bool)
    (occ : Fin k → Fin S.occurrences) (slots : Fin k → Fin 3)
    (TM :
      (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
      (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s)) : ℝ :=
  VisiblePolicies.observedAgreement S labeling good
    (actualDraw S A (Clean.NativeExperiment.maskSet mask) occ
      (fun j => Clean.ActualAdviceBridge.indexSlot (slots j)) TM.1 TM.2)

theorem sampledAgreement_eq_separated (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    sampledAgreement S labeling good
      (Clean.IncidenceGap.slotLaw (FiniteDistribution.uniform (Fin S.occurrences)))
      A β hβ₀ hβ₁ =
      ((Clean.bernoulli β hβ₀ hβ₁).iid k).expectation (fun mask =>
        (FiniteDistribution.uniform (Fin k → Fin S.occurrences)).expectation (fun occ =>
          (FiniteDistribution.uniform (Fin k → Fin 3)).expectation (fun slots =>
            (FiniteDistribution.uniform
              ((RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
                (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s))).expectation
              (drawAgreement S labeling good A mask occ slots)))) := by
  unfold sampledAgreement
  apply FiniteDistribution.expectation_congr
  intro mask
  calc
    _ = (FiniteDistribution.uniform
        ((RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
          (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s))).expectation
        (fun TM => (FiniteDistribution.uniform (Fin k → Fin S.occurrences)).expectation
          (fun occ => (FiniteDistribution.uniform (Fin k → Fin 3)).expectation
            (fun slots => drawAgreement S labeling good A mask occ slots TM))) := by
      apply FiniteDistribution.expectation_congr
      intro TM
      exact uniform_occurrence_slots _
    _ = _ := by
      rw [FiniteDistribution.expectation_comm]
      apply FiniteDistribution.expectation_congr
      intro occ
      exact FiniteDistribution.expectation_comm _ _ _

/-- Exact sampler join: the complete hidden seed used by conditioning has
the same success as the genuine local-policy experiment used by the upper
bound, with no extra hidden-data conditioning on either side. -/
theorem fullSeedLaw_eq_sampledAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    (AdviceLaw.fullSeedLaw (V := Alphabet s × Vector d)
      (FiniteDistribution.uniform (Fin k → Fin S.occurrences))
      (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)) β hβ₀ hβ₁).expectation
      (fun seed => VisiblePolicies.observedAgreement S labeling good
        (AdviceLaw.seedToActualDraw seed.1.1 seed.1.2 seed.2)) =
      (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun A => sampledAgreement S labeling good
          (Clean.IncidenceGap.slotLaw (FiniteDistribution.uniform (Fin S.occurrences)))
          A β hβ₀ hβ₁) := by
  unfold AdviceLaw.fullSeedLaw
  rw [FiniteDistribution.expectation_product, FiniteDistribution.expectation_product,
    FiniteDistribution.expectation_comm]
  apply FiniteDistribution.expectation_congr
  intro A
  rw [sampledAgreement_eq_separated]
  calc
    _ = (FiniteDistribution.uniform (Fin k → Fin S.occurrences)).expectation (fun occ =>
        ((Clean.bernoulli β hβ₀ hβ₁).iid k).expectation (fun mask =>
          (FiniteDistribution.uniform (Fin k → Fin 3)).expectation (fun slots =>
            (FiniteDistribution.uniform
              ((RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
                (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s))).expectation
              (drawAgreement S labeling good A mask occ slots)))) := by
      apply FiniteDistribution.expectation_congr
      intro occ
      rw [AdviceLaw.projectionSeed_mask_slots_expectation]
      apply FiniteDistribution.expectation_congr
      intro mask
      apply FiniteDistribution.expectation_congr
      intro slots
      exact ActualSeedPointwise.seedAgreement_repack S labeling good occ A mask slots
    _ = _ := FiniteDistribution.expectation_comm _ _ _

theorem fullSeedLaw_upper (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, (sourceIncidence S).name o i =
      (sourceIncidence S).name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue (sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) :
    (AdviceLaw.fullSeedLaw (V := Alphabet s × Vector d)
      (FiniteDistribution.uniform (Fin k → Fin S.occurrences))
      (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)) β hβ₀ hβ₁).expectation
      (fun seed => VisiblePolicies.observedAgreement S labeling good
        (AdviceLaw.seedToActualDraw seed.1.1 seed.1.2 seed.2)) ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k := by
  rw [fullSeedLaw_eq_sampledAgreement]
  exact sampledAgreement_average_bound S labeling good β hβ₀ hβ₁ distinct hopt

end

end MaxCutGames.Decoder.ActualSeedSampling

/-! The contradiction uses the same actual seed and local decoder on both
sides. Its lower bound comes from full-table variation followed by visible
conditioning; its upper bound comes from the exact incidence sampler. -/

namespace MaxCutGames.Decoder.ActualMatrixContradiction

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

private theorem univ_fintype_eq_inline_ActualMatrixContradiction {X : Type*} (a b : Fintype X) :
    @Finset.univ X a = @Finset.univ X b :=
  congrArg (fun t : Fintype X => @Finset.univ X t) (Subsingleton.elim a b)

private def expectationOf_inline_ActualMatrixContradiction {X : Type*} {i : Fintype X}
    (μ : @FiniteDistribution X i) (f : X → ℝ) : ℝ :=
  @FiniteDistribution.expectation X i μ f

private theorem card_to_natCard_inline_ActualMatrixContradiction (X : Type*) (i : Fintype X) :
    @Fintype.card X i = Nat.card X :=
  (@Nat.card_eq_fintype_card X i).symm

theorem law_expectation_eq (S : Source) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (f : ActualSeedEvents.Seed S k s d r → ℝ) :
    expectationOf_inline_ActualMatrixContradiction (ActualSeedEvents.law S k s d r β hβ hβ') f =
      expectationOf_inline_ActualMatrixContradiction (AdviceLaw.fullSeedLaw (V := Alphabet s × Vector d)
        (FiniteDistribution.uniform (Fin k → Fin S.occurrences))
        (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)) β hβ hβ') f := by
  simp only [expectationOf_inline_ActualMatrixContradiction, FiniteDistribution.expectation, ActualSeedEvents.law,
    AdviceLaw.fullSeedLaw, FiniteDistribution.product, FiniteDistribution.uniform]

theorem contradiction (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α g₀ β : ℝ) (hα : 0 < α)
    (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
    (hvariation : ActualProjectedTransfer.slopeVariation k s d β ≤
      ConstantSelection.variationBudget α g₀ s r)
    (hrate : (1 - (β / (2 : ℝ) ^ (d + r)) / 3600) ^ k <
      ConstantSelection.decodingMass α g₀ s r)
    (hdistinct : S.DistinctNames)
    (hopt : Clean.IncidenceGap.parityValue (ActualAdviceUpper.sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) : False := by
  have hlower := ActualProjectedTransfer.actual_success_lower S labeling α g₀ β
    hα hsmall hβ hβ' hgood hvariation
  have hnames : ∀ o i j, (ActualAdviceUpper.sourceIncidence S).name o i =
      (ActualAdviceUpper.sourceIncidence S).name o j → i = j :=
    Outer.SourceIncidence.names_distinct S hdistinct
  have hupper := ActualSeedSampling.fullSeedLaw_upper S labeling
    (SelectedPolicies.goodPredicate S labeling α hα hsmall) β hβ hβ' hnames hopt
  have hbound : ConstantSelection.decodingMass α g₀ s r ≤
      (1 - (β / (2 : ℝ) ^ (d + r)) / 3600) ^ k := by
    apply hlower.trans
    change expectationOf_inline_ActualMatrixContradiction (ActualSeedEvents.law S k s d r β hβ hβ') _ ≤ _
    rw [law_expectation_eq]
    exact hupper
  exact (not_lt_of_ge hbound) hrate

end
end MaxCutGames.Decoder.ActualMatrixContradiction

end OAI
