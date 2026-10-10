import Mathlib
import OAI.Analysis.CoulombIonization.Localization.ObservationLikelihood

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ArraySymmetry_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace CoulombObservation

def arrayReindex {J I : Type*} [Fintype J] [Fintype I] (e : Equiv.Perm I) :
    (J × I → ℝ) ≃ᵐ (J × I → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) ((Equiv.refl J).prodCongr e.symm)

@[simp] lemma arrayReindex_apply {J I : Type*} [Fintype J] [Fintype I]
    (e : Equiv.Perm I) (u : J × I → ℝ) (q : J × I) :
    arrayReindex e u q = u (q.1,e q.2) := by
  rcases q with ⟨j,i⟩
  simp [arrayReindex, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft]

lemma arrayReindex_preserving {J I : Type*} [Fintype J] [Fintype I]
    (e : Equiv.Perm I) :
    MeasurePreserving (arrayReindex (J := J) e)
      (Measure.pi (fun _ : J × I => compactNoiseLaw))
      (Measure.pi (fun _ : J × I => compactNoiseLaw)) :=
  measurePreserving_piCongrLeft (fun _ => compactNoiseLaw) _

lemma arrayLikelihood_reindex {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s)
    (e : Equiv.Perm I) (hinv : ∀ u, arrayReindex (J := J) e u ∈ s ↔ u ∈ s)
    (x : I → ℝ) : arrayLikelihood b s (x ∘ e) = arrayLikelihood b s x := by
  rw [arrayLikelihood_eq_probability b hs, arrayLikelihood_eq_probability b hs]
  unfold Measure.real
  congr 1
  have hset : (arrayReindex (J := J) e) ⁻¹'
      shiftedObservationEvent s (observationPlacement b (x ∘ e)) =
      shiftedObservationEvent s (observationPlacement b x) := by
    ext u
    change observationPlacement b (x ∘ e) + arrayReindex e u ∈ s ↔
      observationPlacement b x + u ∈ s
    have he : observationPlacement b (x ∘ e) + arrayReindex e u =
        arrayReindex e (observationPlacement b x + u) := by
      ext q
      simp only [Pi.add_apply, observationPlacement_apply, Function.comp_apply, arrayReindex_apply]
    rw [he]
    exact hinv _
  rw [← (arrayReindex_preserving e).measure_preimage
    (shiftedObservationEvent_measurable hs _).nullMeasurableSet, hset]

end CoulombObservation

end Work_ArraySymmetry_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombAtom
open CoulombObservation

def flattenConfiguration (N : ℕ) : Configuration N →L[ℝ] (Fin N × Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun q => (EuclideanSpace.proj q.2).comp
    (ContinuousLinearMap.proj q.1))

@[simp] lemma flattenConfiguration_apply {N : ℕ} (x : Configuration N)
    (q : Fin N × Fin 3) : flattenConfiguration N x q = x q.1 q.2 := rfl

@[simp] lemma flattenConfiguration_direction {N : ℕ} (i : Fin N) (a : Fin 3) :
    flattenConfiguration N (direction i a) = Pi.single (i,a) 1 := by
  ext ⟨j,c⟩
  simp only [flattenConfiguration_apply, direction, Pi.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

lemma lineDeriv_flattenConfiguration {N : ℕ} (f : (Fin N × Fin 3 → ℝ) → ℝ)
    (x : Configuration N) (i : Fin N) (a : Fin 3) :
    lineDeriv ℝ (fun y => f (flattenConfiguration N y)) x (direction i a) =
      lineDeriv ℝ f (flattenConfiguration N x) (Pi.single (i,a) 1) := by
  unfold lineDeriv
  simp only [map_add, map_smul, flattenConfiguration_direction]

def flatRawLaw {N : ℕ} (F : fermionGraph N) : Measure (Fin N × Fin 3 → ℝ) :=
  Measure.map (flattenConfiguration N) (graphRawLaw F)

lemma flatRawLaw_probability {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖^2 = 1) : IsProbabilityMeasure (flatRawLaw F) := by
  let := graphRawLaw_probability F hn
  unfold flatRawLaw
  infer_instance

def quantumEventLikelihood {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) (s : Set (J × (Fin N × Fin 3) → ℝ)) (x : Configuration N) : ℝ :=
  arrayLikelihood b s (flattenConfiguration N x)

def quantumEventProbability {N : ℕ} {J : Type*} [Fintype J]
    (F : fermionGraph N) (b : J → ℝ) (s : Set (J × (Fin N × Fin 3) → ℝ)) : ℝ :=
  ∫ x, quantumEventLikelihood b s x ∂graphRawLaw F

lemma quantumEventProbability_eq_flat {N : ℕ} {J : Type*} [Fintype J]
    (F : fermionGraph N) (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)}
    (hs : MeasurableSet s) :
    quantumEventProbability F b s = ∫ x, arrayLikelihood b s x ∂flatRawLaw F := by
  symm
  exact integral_map (flattenConfiguration N).measurable.aemeasurable
    ((arrayLikelihood_contDiff b hs (n := 1)).continuous.measurable.aestronglyMeasurable)

lemma quantumEventLikelihood_nonneg {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (x : Configuration N) : 0 ≤ quantumEventLikelihood b s x :=
  arrayLikelihood_nonneg b hs _

lemma quantumEventLikelihood_le_one {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (x : Configuration N) : quantumEventLikelihood b s x ≤ 1 :=
  arrayLikelihood_le_one b hs _

lemma quantumEventLikelihood_measurable {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s) :
    Measurable (quantumEventLikelihood b s) :=
  (arrayLikelihood_contDiff b hs (n := 1)).continuous.measurable.comp
    (flattenConfiguration N).measurable

def QuantumEventSymmetric {N : ℕ} {J : Type*} [Fintype J]
    (s : Set (J × (Fin N × Fin 3) → ℝ)) : Prop :=
  ∀ (π : Equiv.Perm (Fin N)) u,
    arrayReindex (J := J) (π.prodCongr (Equiv.refl (Fin 3))) u ∈ s ↔ u ∈ s

lemma quantumEventLikelihood_symmetric {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) (π : Equiv.Perm (Fin N)) (x : Configuration N) :
    quantumEventLikelihood b s (x ∘ π) = quantumEventLikelihood b s x := by
  have he : flattenConfiguration N (x ∘ π) =
      flattenConfiguration N x ∘ (π.prodCongr (Equiv.refl (Fin 3))) := by
    ext ⟨i,a⟩
    rfl
  unfold quantumEventLikelihood
  rw [he]
  exact arrayLikelihood_reindex b hs _ (hsy π) _

end CoulombAtom

end

end OAI
