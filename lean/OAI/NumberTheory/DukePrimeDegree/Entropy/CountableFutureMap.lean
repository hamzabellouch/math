import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableFutureSigma
import Mathlib.Probability.Kernel.MeasurableLIntegral

namespace OAI

/-! # The entire future as a measurable sequence

This representation makes future-measurable events constant on each
complete future fiber. It is used to restrict local disintegrations to
saturated events when gluing them.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

def entireFutureObservation {Y : Type*} (T : Y → Y) (Q : Y → ℕ)
    (y : Y) : ℕ → ℕ := fun k => Q (T^[k+1] y)

lemma entireFutureObservation_measurable {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q) :
    Measurable (entireFutureObservation T Q) :=
  measurable_pi_iff.mpr fun k => hQ.comp (hT.iterate (k+1))

lemma countableFutureSigma_eq_comap {Y : Type*} (T : Y → Y) (Q : Y → ℕ) :
    (⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y))) =
      MeasurableSpace.comap (entireFutureObservation T Q)
        (inferInstance : MeasurableSpace (ℕ → ℕ)) := by
  exact (MeasurableSpace.comap_process_pi
    (fun k : ℕ => fun y : Y => Q (T^[k+1] y))).symm

lemma transverseCountableFutureSigma_eq_comap {S V Y : Type*}
    [MeasurableSpace S] [MeasurableSpace V]
    (T : Y → Y) (Q : Y → ℕ) (F : S × V → Y) :
    (⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))) =
      MeasurableSpace.comap (fun z => (z.1, entireFutureObservation T Q (F z)))
        (inferInstance : MeasurableSpace (S × (ℕ → ℕ))) := by
  rw [transverseCountableFutureSigma_eq_sup]
  calc
    _ = MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S) ⊔
        MeasurableSpace.comap (entireFutureObservation T Q ∘ F)
          (inferInstance : MeasurableSpace (ℕ → ℕ)) := by
      rw [countableFutureSigma_eq_comap, MeasurableSpace.comap_comp]
    _ = _ := (MeasurableSpace.comap_prodMk
      (Prod.fst : S × V → S) (entireFutureObservation T Q ∘ F)).symm

lemma countableFutureFiber_eq_of_mem {S V Y : Type*}
    (T : Y → Y) (Q : Y → ℕ) (F : S × V → Y)
    (z : S × V) {u : V} (hu : u ∈ countableFutureFiber T Q F z) :
    countableFutureFiber T Q F (z.1,u) = countableFutureFiber T Q F z := by
  ext v
  constructor
  · intro hv k
    exact (hv k).trans (hu k)
  · intro hv k
    exact (hv k).trans (hu k).symm

/-- Every event in the complete transverse-future sigma algebra is
constant along its future fibers, with no exceptional set needed. -/
theorem mem_future_event_iff {S V Y : Type*}
    [MeasurableSpace S] [MeasurableSpace V]
    (T : Y → Y) (Q : Y → ℕ) (F : S × V → Y)
    {E : Set (S × V)}
    (hE : MeasurableSet[⨆ m, transverseLabelSigma
      (fun z => countableFutureCode T Q m (F z))] E)
    (z : S × V) {u : V} (hu : u ∈ countableFutureFiber T Q F z) :
    (z.1,u) ∈ E ↔ z ∈ E := by
  rw [transverseCountableFutureSigma_eq_comap] at hE
  obtain ⟨A, _hA, rfl⟩ := hE
  change (z.1, entireFutureObservation T Q (F (z.1,u))) ∈ A ↔
    (z.1, entireFutureObservation T Q (F z)) ∈ A
  have he : entireFutureObservation T Q (F (z.1,u)) =
      entireFutureObservation T Q (F z) := funext hu
  rw [he]

/-- Fiber masses of a kernel depending only on the transverse coordinate
are measurable in the transverse-future sigma algebra itself. Thus mass
conditions used to select boxes really are future events. -/
theorem measurable_countableFuture_mass {S V Y : Type*}
    [MeasurableSpace S] [MeasurableSpace V] [MeasurableSpace Y]
    (κ : Kernel S V) [IsSFiniteKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F)
    (A : Set (S × V)) (hA : MeasurableSet A) :
    Measurable[⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))]
      (fun z => κ z.1 ({t | (z.1,t) ∈ A} ∩ countableFutureFiber T Q F z)) := by
  let q := entireFutureObservation T Q
  have hq : Measurable q := entireFutureObservation_measurable hT hQ
  have hrel : MeasurableSet {p : (S × (ℕ → ℕ)) × V |
      (p.1.1,p.2) ∈ A ∧ q (F (p.1.1,p.2)) = p.1.2} :=
    (hA.preimage (measurable_fst.fst.prodMk measurable_snd)).inter
      (measurableSet_eq_fun
        (hq.comp (hF.comp (measurable_fst.fst.prodMk measurable_snd))) measurable_fst.snd)
  have H : Measurable (fun b : S × (ℕ → ℕ) =>
      κ b.1 {t | (b.1,t) ∈ A ∧ q (F (b.1,t)) = b.2}) :=
    Kernel.measurable_kernel_prodMk_left (κ := κ.prodMkRight (ℕ → ℕ)) hrel
  have hη : Measurable[⨆ m, transverseLabelSigma
      (fun z => countableFutureCode T Q m (F z))]
      (fun z => (z.1,q (F z))) := by
    rw [transverseCountableFutureSigma_eq_comap]
    exact comap_measurable _
  convert H.comp hη using 1
  funext z
  congr 1
  ext t
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, countableFutureFiber,
    q, entireFutureObservation, funext_iff]

/-- The event that a complete future fiber has no mass outside a fixed
time domain is measurable using only the transverse coordinate and the
future name. -/
theorem measurableSet_future_mass_contained {S V Y : Type*}
    [MeasurableSpace S] [MeasurableSpace V] [MeasurableSpace Y]
    (κ : Kernel S V) [IsSFiniteKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F)
    (B : Set V) (hB : MeasurableSet B) :
    MeasurableSet[⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))]
      {z | κ z.1 (countableFutureFiber T Q F z \ B) = 0} := by
  have hm := measurable_countableFuture_mass κ hT hQ hF
    (Prod.snd ⁻¹' Bᶜ) (hB.compl.preimage measurable_snd)
  have he := measurableSet_eq_fun hm (measurable_const (a := (0 : ℝ≥0∞)))
  change MeasurableSet[⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))]
    {z | κ z.1 (Bᶜ ∩ countableFutureFiber T Q F z) = 0} at he
  simpa only [Set.sdiff_eq, Set.inter_comm] using he

end DukePrimeDegree

end

end OAI
