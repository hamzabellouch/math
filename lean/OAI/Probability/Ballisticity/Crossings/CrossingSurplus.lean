import Mathlib
import OAI.Probability.Ballisticity.Coupling.FreshCrossing
import OAI.Probability.Ballisticity.Crossings.CrossingGapDecay
import OAI.Probability.Ballisticity.Estimates.RapidDecayTail

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma measureReal_iUnion_le_of_summable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (A : ℕ → Set α)
    (hs : Summable (fun n => μ.real (A n))) :
    μ.real (⋃ n, A n) ≤ ∑' n, μ.real (A n) := by
  have he : (∑' n, μ (A n))=ENNReal.ofReal (∑' n, μ.real (A n)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg) hs]
    simp only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top μ _)]
  have hh := ENNReal.toReal_mono (by rw [he]; exact ENNReal.ofReal_ne_top) (measure_iUnion_le A)
  rw [he, ENNReal.toReal_ofReal (tsum_nonneg (fun n => measureReal_nonneg))] at hh
  exact hh

lemma antitone_sdiff_iInter_subset {α : Type*} (A : ℕ → Set α) (hA : Antitone A) (N : ℕ) :
    A N \ (⋂ k, A k) ⊆ ⋃ k, A (N+k) \ A (N+k+1) := by
  intro x hx
  have hex : ∃ k, x ∉ A (N+k) := by
    by_contra hh
    push Not at hh
    apply hx.2
    apply Set.mem_iInter.mpr
    intro k
    exact hA (by omega : k ≤ N+k) (hh k)
  have hpos : 0<Nat.find hex := by
    by_contra hh
    have hz : Nat.find hex=0 := by omega
    have hm := Nat.find_spec hex
    rw [hz,Nat.add_zero] at hm
    exact hm hx.1
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Nat.find hex≠0)
  refine Set.mem_iUnion.mpr ⟨k,?_,?_⟩
  · by_contra hh
    exact Nat.find_min hex (by omega : k<Nat.find hex) hh
  · simpa only [hk,Nat.succ_eq_add_one,Nat.add_assoc] using Nat.find_spec hex

lemma cross_failure_subset_gaps {d : ℕ} (e : Direction d) (N : ℕ) :
    Cross (realPosition (step e)) 0 N \ NoDrop (realPosition (step e)) 0 ⊆
      ⋃ k, CrossingGap e (N+k) := by
  have hh := antitone_sdiff_iInter_subset
    (fun k => Cross (realPosition (step e)) 0 k)
      (fun i j hij => cross_antitone _ _ (Nat.cast_le.mpr hij)) N
  have hs := Set.Subset.trans (Set.sdiff_subset_sdiff_right (iInter_cross_subset_noDrop (realPosition (step e)) 0)) hh
  simpa only [CrossingGap, Nat.cast_add, Nat.cast_one] using hs

lemma crossing_failure_rapidDecay {d : ℕ} (hd : 2≤d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    RapidDecay (fun N => (annealedLaw ν).real
      (Cross (realPosition (step e)) 0 N \ NoDrop (realPosition (step e)) 0)) := by
  have hg := crossingGap_rapidDecay hd ν hue e htrans
  apply (hg.tail (fun _ => measureReal_nonneg)).of_le (fun _ => measureReal_nonneg)
  apply Eventually.of_forall
  intro N
  calc
    _ ≤ (annealedLaw ν).real (⋃ k, CrossingGap e (N+k)) :=
      measureReal_mono (cross_failure_subset_gaps e N)
    _ ≤ _ := measureReal_iUnion_le_of_summable _ _ (by
      simpa only [Nat.add_comm N] using (summable_nat_add_iff N).mpr hg.summable)

lemma annealed_record_event_cross_failure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (n : ℕ) (hn : 0<n)
    (A : Set (Path d)) (_ : MeasurableSet A) (hA : PrefixDetermined n A)
    (hr : ∀ X ∈ A, StrictRecord ℓ X n) (H : ℝ) (hH : 0<H) :
    (annealedLaw ν).real ((A ∩ FutureEvent (fun x => Cross ℓ x H) n) \ FutureNoDrop ℓ n)=
      (annealedLaw ν).real A*(annealedLaw ν).real (Cross ℓ 0 H \ NoDrop ℓ 0) := by
  let μ := annealedLaw ν
  have hsub : ∀ᵐ X ∂μ, X ∈ A ∩ FutureNoDrop ℓ n → X ∈ A ∩ FutureEvent (fun x => Cross ℓ x H) n := by
    filter_upwards [htrans] with X ht hX
    refine ⟨hX.1,?_⟩
    apply noDrop_subset_cross_of_tendsto ℓ (X n) (fun j => X (n+j))
    · exact ht.comp (by
        change Tendsto (fun i : ℕ => n+i) atTop atTop
        simpa only [Nat.add_comm] using tendsto_add_atTop_nat n)
    · exact hX.2
  have hraw : ∀ᵐ X ∂μ, X ∈ NoDrop ℓ 0 → X ∈ Cross ℓ 0 H := by
    filter_upwards [htrans] with X ht hX
    exact noDrop_subset_cross_of_tendsto ℓ 0 X ht hX H
  have hi : ((A ∩ FutureEvent (fun x => Cross ℓ x H) n) ∩ FutureNoDrop ℓ n : Set (Path d)) =ᵐ[μ]
      (A ∩ FutureNoDrop ℓ n : Set (Path d)) := by
    filter_upwards [hsub] with X hX
    exact propext ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨hX h,h.2⟩⟩
  have hi0 : (Cross ℓ 0 H ∩ NoDrop ℓ 0 : Set (Path d)) =ᵐ[μ] NoDrop ℓ 0 := by
    filter_upwards [hraw] with X hX
    exact propext ⟨And.right,fun h => ⟨hX h,h⟩⟩
  have hf := congrArg ENNReal.toReal (annealed_record_event_cross ν ℓ n hn A hA hr H hH)
  have hp := congrArg ENNReal.toReal (annealed_record_event_noDrop ν ℓ n hn A hA hr)
  have hs := measureReal_inter_add_sdiff (μ := μ) (s := A ∩ FutureEvent (fun x => Cross ℓ x H) n)
    (measurableSet_futureNoDrop ℓ n)
  have hs0 := measureReal_inter_add_sdiff (μ := μ) (s := Cross ℓ 0 H) (measurableSet_noDrop ℓ 0)
  rw [measureReal_congr hi] at hs
  rw [measureReal_congr hi0] at hs0
  simp only [ENNReal.toReal_mul] at hf hp
  change μ.real (A ∩ FutureEvent (fun x => Cross ℓ x H) n)=μ.real A*μ.real (Cross ℓ 0 H) at hf
  change μ.real (A ∩ FutureNoDrop ℓ n)=μ.real A*μ.real (NoDrop ℓ 0) at hp
  change μ.real _=μ.real A*μ.real _
  rw [← hs0,mul_add,← hp] at hf
  linarith

end DirectionalTransience

end

end OAI
