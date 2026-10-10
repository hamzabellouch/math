import OAI.NumberTheory.PrimePackets.EntropyGeneratingSupremum

namespace OAI

/-!
# Actual finite generating observations on countably generated spaces

The observations record finitely many bits of Mathlib's canonical countable
generating family. Thus the entropy approximation hypotheses are supplied by
the measurable space itself, rather than assumed for an arbitrary sequence.
-/

noncomputable section
open MeasureTheory MeasurableSpace Set
open scoped ENNReal

namespace PrimeDegreePackets

lemma observationSigma_comp_le {Y α β : Type*} (P : Y → α) (f : α → β) :
    observationSigma (fun y => f (P y)) ≤ observationSigma P := by
  rintro s ⟨t,_,rfl⟩
  exact ⟨f ⁻¹' t, trivial, rfl⟩

lemma observationSigma_comp_injective {Y α β : Type*} (P : Y → α) (f : α → β)
    (hf : Function.Injective f) :
    observationSigma (fun y => f (P y)) = observationSigma P := by
  apply le_antisymm (observationSigma_comp_le P f)
  rintro s ⟨t,_,rfl⟩
  refine ⟨f '' t, trivial, ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_image, hf.eq_iff]
  exact ⟨fun ⟨a,ha,h⟩ => h ▸ ha, fun h => ⟨P y,h,rfl⟩⟩

variable (Y : Type*) [mY : MeasurableSpace Y] [CountablyGenerated Y]

def finiteGeneratingBits (n : ℕ) (y : Y) : Fin n → Bool :=
  fun i => mapNatBool Y y i.val

lemma finiteGeneratingBits_measurable (n : ℕ) : Measurable (finiteGeneratingBits Y n) :=
  measurable_pi_iff.mpr (fun i => (measurable_pi_apply i.val).comp (measurable_mapNatBool Y))

lemma finiteGeneratingBits_monotone :
    Monotone (fun n => observationSigma (finiteGeneratingBits Y n)) := by
  intro n m hnm s hs
  obtain ⟨t,_,rfl⟩ := hs
  refine ⟨{v : Fin m → Bool | (fun i : Fin n => v ⟨i.val, lt_of_lt_of_le i.isLt hnm⟩) ∈ t},
    trivial, ?_⟩
  rfl

lemma finiteGeneratingBits_generate :
    (⨆ n, observationSigma (finiteGeneratingBits Y n)) = mY := by
  apply le_antisymm
  · apply iSup_le
    intro n
    exact observationSigma_le _ (fun b => (finiteGeneratingBits_measurable Y n)
      (measurableSet_singleton b))
  · apply le_trans (le_of_eq (generateFrom_natGeneratingSequence Y).symm)
    apply MeasurableSpace.generateFrom_le
    rintro s ⟨n,rfl⟩
    apply (le_iSup (fun n => observationSigma (finiteGeneratingBits Y n)) (n+1))
    refine ⟨{v : Fin (n+1) → Bool | v ⟨n, Nat.lt_succ_self n⟩ = true}, trivial, ?_⟩
    ext y
    simp [finiteGeneratingBits, mapNatBool]

def finiteGeneratingObservation (n : ℕ) (y : Y) :
    Fin (Fintype.card (Fin n → Bool)) :=
  Fintype.equivFin (Fin n → Bool) (finiteGeneratingBits Y n y)

lemma finiteGeneratingObservation_sigma (n : ℕ) :
    observationSigma (finiteGeneratingObservation Y n) =
      observationSigma (finiteGeneratingBits Y n) :=
  observationSigma_comp_injective _ _ (Fintype.equivFin (Fin n → Bool)).injective

lemma finiteGeneratingObservation_measurable (n : ℕ) :
    Measurable (finiteGeneratingObservation Y n) :=
  (measurable_of_finite (Fintype.equivFin (Fin n → Bool))).comp
    (finiteGeneratingBits_measurable Y n)

lemma finiteGeneratingObservation_monotone :
    Monotone (fun n => observationSigma (finiteGeneratingObservation Y n)) := by
  simpa only [finiteGeneratingObservation_sigma] using finiteGeneratingBits_monotone Y

lemma finiteGeneratingObservation_generate :
    (⨆ n, observationSigma (finiteGeneratingObservation Y n)) = mY := by
  simpa only [finiteGeneratingObservation_sigma] using finiteGeneratingBits_generate Y

/-- On any countably generated measurable space, an explicit sequence of
finite observations computes the full metric entropy. -/
theorem measureEntropy_eq_iSup_finiteGenerating
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) :
    measureEntropy μ T = ⨆ n, ENNReal.ofReal
      (observationEntropyRate μ T (finiteGeneratingObservation Y n)) :=
  measureEntropy_eq_iSup_generating μ hT (finiteGeneratingObservation Y)
    (fun n b => (finiteGeneratingObservation_measurable Y n) (measurableSet_singleton b))
    (finiteGeneratingObservation_monotone Y) (finiteGeneratingObservation_generate Y)

end PrimeDegreePackets

end

end OAI
