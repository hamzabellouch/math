import OAI.Computability.UniqueGames.Decoding.ActualAdviceUpperLemmas
import OAI.Computability.UniqueGames.Decoding.ActualSeedPointwise
import OAI.Computability.UniqueGames.Decoding.TableKeysCompletenessLemmas
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI

section

/-!
The complete seed used for the lower-bound conditioning argument and the
mask/slot/map experiment used for the clean upper bound have exactly the same
actual decoder success. Unused positions are removed only by the pointwise
observation equality; occurrence IDs and their ordered local copies remain.
-/

namespace UniqueGamesTheorem.Decoder.ActualSeedSampling

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Foundations.Games
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

end UniqueGamesTheorem.Decoder.ActualSeedSampling

end

section

/-! Whole-table variation for the exact projected seed law in the selected
event coordinates. The projection is averaged out before the comparison. -/

namespace UniqueGamesTheorem.Decoder.ActualSeedVariation

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

theorem uniform_pushforward_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (e : X ≃ Y) :
    (FiniteDistribution.uniform X).pushforward e = FiniteDistribution.uniform Y := by
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  simp only [FiniteDistribution.transport, FiniteDistribution.uniform,
    Fintype.card_congr e]

theorem totalVariation_pushforward_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (μ ν : FiniteDistribution X) (e : X ≃ Y) :
    (μ.pushforward e).totalVariation (ν.pushforward e) = μ.totalVariation ν := by
  rw [FiniteDistribution.pushforward_equiv, FiniteDistribution.pushforward_equiv]
  unfold FiniteDistribution.totalVariation FiniteDistribution.transport
  congr 1
  exact e.symm.sum_comp (fun x => |μ.weight x - ν.weight x|)

/-- Three independent uniform samples are uniform on their full product. -/
theorem ideal_full_uniform (S : Source) (k s d r : ℕ) :
    AdviceLaw.withKernel
      ((FiniteDistribution.uniform (ActualGame.Question S k)).product
        (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)))
      (fun _ => FiniteDistribution.uniform (ActualGame.Map k s d)) =
        FiniteDistribution.uniform (ActualEvents.FullTableSample S k s d r) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro p
  simp only [AdviceLaw.withKernel, FiniteDistribution.product, FiniteDistribution.uniform,
    Fintype.card_prod, Nat.cast_mul]
  ring

theorem ideal_pad_coordinates (S : Source) (k s d r : ℕ) :
    (AdviceLaw.withKernel
      ((FiniteDistribution.uniform (ActualGame.Question S k)).product
        (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)))
      (fun _ => FiniteDistribution.uniform (ActualGame.Map k s d))).pushforward
        (ActualEvents.fullTableEquiv S k s d r) = ActualEvents.unrestricted S k s d r := by
  rw [ideal_full_uniform]
  exact uniform_pushforward_equiv _

theorem actual_totalVariation_le_slope (S : Source) (k s d r : ℕ)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (ActualEvents.unrestricted S k s d r).totalVariation
      ((ActualSeedEvents.law S k s d r β hβ hβ').pushforward (ActualSeedEvents.pad S k s d r)) ≤
        Foundations.Information.totalVariation
          (SparseLaw.independentWeights
            (SparseLaw.mixture β (SparseLaw.singletonPairWeights (Ambient s d))) k)
          (SparseLaw.uniformWeights (Fin k → Ambient s d × Ambient s d)) := by
  rw [FiniteDistribution.totalVariation_comm]
  have h := AdviceLaw.fullSeed_totalVariation_le_slope (V := Ambient s d)
    (FiniteDistribution.uniform (ActualGame.Question S k))
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r))
    (fun i => toBit (ActualGame.rhs S i)) β hβ hβ'
  rw [← ideal_pad_coordinates S k s d r]
  change ((ActualSeedEvents.law S k s d r β hβ hβ').pushforward
      (fun x => ActualEvents.fullTableEquiv S k s d r
        (AdviceLaw.fullSeedPad (fun i => toBit (ActualGame.rhs S i)) x))).totalVariation _ ≤ _
  rw [← FiniteDistribution.pushforward_comp, totalVariation_pushforward_equiv]
  convert h using 1 <;> congr 4
  exact Subsingleton.elim _ _

end
end UniqueGamesTheorem.Decoder.ActualSeedVariation

end

section

namespace UniqueGamesTheorem.Decoder.MatrixGap

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Integration
open ActualSource

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Fixed matrix-test parameters, before the separate bipartite subdivision
and repetition. Existence is proved by the spectral/decoding argument. -/
structure Parameters (p : ℚ) where
  k : Nat
  s : Nat
  d : Nat
  k_pos : 1 ≤ k
  s_pos : 1 ≤ s
  T : NoiseTables.Table s d
  f : Ambient s d → Alphabet s
  equivariant : ∀ x c, f (x + (c, 0)) = f x + c
  stability : (T.gadget f equivariant).stabilityError ≤ p
  sound : ∀ S : Source, S.DistinctNames →
    Clean.IncidenceGap.parityValue (ActualAdviceUpper.sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5 →
    InstanceValue.value (TableKeysAddressGame.tableOutput S k T) ≤ (99 : ℝ) / 100

/-- The rate of any semantic vertex labeling is realized on the direct
address output. Isolated unused addresses receive an arbitrary valid label. -/
theorem semantic_rate_le_address_value (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) :
    (GapSemantics.satisfactionRate (TableKeysGame.outputInstance S k g) labeling : ℝ) ≤
      InstanceValue.value (TableKeysAddressGame.outputInstance S k g en) := by
  have h := semantic_acceptance_le_address_value S k g en labeling
  rw [TableKeysGame.acceptanceProbability_eq_count] at h
  exact h

namespace Parameters

variable {p : ℚ}

/-- The actual output constructor depends only on finite tables, not on the
correcting map or its equivariance proof. -/
def output (P : Parameters p) (S : Source) : Instance (2 ^ P.s) :=
  TableKeysAddressGame.tableOutput S P.k P.T

theorem completeness (P : Parameters p) (S : Source)
    (assignment : Fin S.variables → Bool) (ξ : ℚ)
    (hfailure : S.failure assignment ≤ ξ) :
    (1 : ℝ) - ((P.k : ℝ) * (ξ : ℝ) + (p : ℝ) / 2) ≤
      InstanceValue.value (TableKeysAddressGame.tableOutput S P.k P.T) :=
  address_value_ge_of_near_assignment S P.k P.T P.f P.equivariant assignment
    ξ p hfailure P.stability

theorem output_translations (P : Parameters p) (S : Source) :
    TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv P.s).symm
      (P.output S) :=
  TableKeysAddressGame.tableOutput_translations S P.k P.T

end Parameters

end

end UniqueGamesTheorem.Decoder.MatrixGap

end

end OAI
