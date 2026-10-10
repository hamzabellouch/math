import Mathlib
import OAI.Analysis.CoulombIonization.Localization.UnorderedObservations

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set

namespace CoulombAtom
open CoulombObservation

def arrayObservedConfiguration {N K : ℕ} (k : Fin K)
    (u : Fin K × (Fin N × Fin 3) → ℝ) : Configuration N :=
  fun i => WithLp.toLp 2 (fun a => u (k,i,a))

def arrayUnorderedConfiguration {N K : ℕ} (k : Fin K)
    (u : Fin K × (Fin N × Fin 3) → ℝ) : UnorderedConfiguration N :=
  unorderedConfiguration (arrayObservedConfiguration k u)

lemma arrayUnorderedConfiguration_measurable {N K : ℕ} (k : Fin K) :
    Measurable (arrayUnorderedConfiguration (N := N) k) := by
  apply unorderedConfiguration_measurable.comp
  apply Measurable.of_eval
  intro i
  apply (Continuous.measurable (by fun_prop : Continuous (WithLp.toLp 2 : (Fin 3 → ℝ) → Space))).comp
  apply Measurable.of_eval
  intro a
  exact measurable_pi_apply (k,i,a)

lemma arrayUnorderedConfiguration_reindex {N K : ℕ} (k : Fin K)
    (π : Equiv.Perm (Fin N)) (u : Fin K × (Fin N × Fin 3) → ℝ) :
    arrayUnorderedConfiguration k (arrayReindex (π.prodCongr (Equiv.refl (Fin 3))) u) =
      arrayUnorderedConfiguration k u := by
  apply Quotient.sound
  refine ⟨π.symm, ?_⟩
  intro i
  ext a
  simp [arrayObservedConfiguration, arrayReindex_apply]

@[instance_reducible] def arrayObservationInformation (N K j : ℕ) :
    MeasurableSpace (Fin K × (Fin N × Fin 3) → ℝ) :=
  ⨆ k : Fin K, if j ≤ k.val then
    MeasurableSpace.comap (arrayUnorderedConfiguration (N := N) k) inferInstance else ⊥

lemma arrayObservationInformation_le (N K j : ℕ) :
    arrayObservationInformation N K j ≤
      (inferInstance : MeasurableSpace (Fin K × (Fin N × Fin 3) → ℝ)) := by
  apply iSup_le
  intro k
  split_ifs
  · exact (arrayUnorderedConfiguration_measurable k).comap_le
  · exact bot_le

lemma observationInformation_eq_arrayComap {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    observationInformation (N := N) ell j =
      (arrayObservationInformation N K j).comap (physicalObservationArray ell) := by
  unfold observationInformation arrayObservationInformation
  rw [MeasurableSpace.comap_iSup]
  congr 1
  funext k
  split_ifs
  · rw [MeasurableSpace.comap_comp]
    rfl
  · exact MeasurableSpace.comap_bot.symm

@[instance_reducible] def symmetricArraySpace (N K : ℕ) : MeasurableSpace (Fin K × (Fin N × Fin 3) → ℝ) where
  MeasurableSet' := QuantumEventSymmetric
  measurableSet_empty := fun _ _ => Iff.rfl
  measurableSet_compl := fun _ h π u => not_congr (h π u)
  measurableSet_iUnion := by
    intro f h π u
    simp only [mem_iUnion]
    exact exists_congr (fun n => h n π u)

lemma arrayObservationInformation_le_symmetric (N K j : ℕ) :
    arrayObservationInformation N K j ≤ symmetricArraySpace N K := by
  apply iSup_le
  intro k
  split_ifs
  · intro A hA
    obtain ⟨B, _, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
    intro π u
    change arrayUnorderedConfiguration k (arrayReindex _ u) ∈ B ↔
      arrayUnorderedConfiguration k u ∈ B
    rw [arrayUnorderedConfiguration_reindex]
  · exact bot_le

theorem observation_event_symmetric_representation {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) :
    ∃ B : Set (Fin K × (Fin N × Fin 3) → ℝ),
      MeasurableSet B ∧ QuantumEventSymmetric B ∧ physicalObservationEvent ell B = A := by
  rw [observationInformation_eq_arrayComap] at hA
  obtain ⟨B,hB,hBA⟩ := MeasurableSpace.measurableSet_comap.mp hA
  exact ⟨B,arrayObservationInformation_le N K j _ hB,
    arrayObservationInformation_le_symmetric N K j _ hB,hBA⟩

end CoulombAtom

end

end OAI
