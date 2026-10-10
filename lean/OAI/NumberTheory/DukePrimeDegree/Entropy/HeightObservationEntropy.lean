import OAI.NumberTheory.PrimePackets.FutureConditionalEntropy

namespace OAI

/-! # Entropy controlled by the increments of a height

A finite label reconstructed from its next value and a finite increment
code has entropy rate bounded by the entropy of that code. In particular,
all finite truncations of a height changing by at most one have entropy
rate at most `log 3`, regardless of the height's integrability.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

variable {Y : Type*} [MeasurableSpace Y]

section Recoding
variable {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]

lemma observationEntropy_recode_le (μ : Measure Y) [IsFiniteMeasure μ]
    (P : Y → α) (hP : Measurable P) (f : α → β) :
    observationEntropy μ (f ∘ P) ≤ observationEntropy μ P := by
  have hfP : Measurable (f ∘ P) := (measurable_of_finite f).comp hP
  have H := conditionalObservationEntropy_nonneg μ P (f ∘ P)
    (fun a => hP (measurableSet_singleton a))
    (fun b => hfP (measurableSet_singleton b))
  have he := observationEntropy_injective μ P (fun a => (f a,a))
    (fun _ _ h => congrArg Prod.snd h)
  change observationEntropy μ (fun y => ((f ∘ P) y,P y)) = observationEntropy μ P at he
  unfold conditionalObservationEntropy at H
  rw [he] at H
  linarith

omit [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] in
lemma observationEntropyRate_le_oneStep (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (P : Y → α) (hP : Measurable P) :
    observationEntropyRate μ T P ≤ conditionalObservationEntropy μ P (P ∘ T) := by
  have hp a := hP (measurableSet_singleton a)
  have H := le_of_tendsto (futureConditionalEntropy_tendsto_rate μ hT P hp)
    ((eventually_ge_atTop 1).mono fun N hN =>
      futureConditionalEntropy_antitone μ hT.measurable P hp hN)
  have he : conditionalObservationEntropy μ P (futureName T P 1) =
      conditionalObservationEntropy μ P (P ∘ T) := by
    change conditionalObservationEntropy μ P (fun y => orbitName T P 1 (T y)) = _
    rw [orbitName_one]
    change conditionalObservationEntropy μ P (fun y (_ : Fin 1) => P (T y)) = _
    exact conditionalObservationEntropy_injective μ P (P ∘ T) id
      (fun a (_ : Fin 1) => a) Function.injective_id (fun _ _ h => congrFun h 0)
  change observationEntropyRate μ T P ≤ conditionalObservationEntropy μ P (futureName T P 1) at H
  rwa [he] at H

/-- A one-step reconstruction code bounds the entropy rate. -/
theorem observationEntropyRate_le_incrementEntropy
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : Measurable P) (D : Y → β) (hD : Measurable D)
    (decode : α → β → α) (hdecode : ∀ y, decode (P (T y)) (D y)=P y) :
    observationEntropyRate μ T P ≤ observationEntropy μ D := by
  have hnext := hP.comp hT.measurable
  have H := observationEntropy_recode_le μ (fun y => (P (T y),D y))
    (hnext.prodMk hD) (fun z => (z.1,decode z.1 z.2))
  have he : (fun y => (P (T y),decode (P (T y)) (D y))) =
      (fun y => (P (T y),P y)) := by funext y; rw [hdecode]
  change observationEntropy μ (fun y => (P (T y),decode (P (T y)) (D y))) ≤ _ at H
  rw [he] at H
  have H' := observationEntropy_joint_le μ (P ∘ T) D
    (fun a => hnext (measurableSet_singleton a))
    (fun b => hD (measurableSet_singleton b))
  change observationEntropy μ (fun y => (P (T y),D y)) ≤
    observationEntropy μ (P ∘ T) + observationEntropy μ D at H'
  have hc : conditionalObservationEntropy μ P (P ∘ T) ≤ observationEntropy μ D := by
    unfold conditionalObservationEntropy
    change observationEntropy μ (fun y => (P (T y),P y)) -
      observationEntropy μ (P ∘ T) ≤ _
    linarith
  exact (observationEntropyRate_le_oneStep μ hT P hP).trans hc

end Recoding

def heightClip (H : Y → ℕ) (N : ℕ) (y : Y) : Fin (N+1) :=
  ⟨min (H y) N,Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma heightClip_measurable {H : Y → ℕ} (hH : Measurable H) (N : ℕ) :
    Measurable (heightClip H N) :=
  (measurable_of_countable (fun k : ℕ =>
    (⟨min k N,Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (N+1)))).comp hH

/-- A finite clipped height is reconstructed from its next value and a
three-valued increment; the middle code means that the label did not change. -/
theorem heightClip_increment_model {T : Y → Y} (hT : Measurable T)
    (H : Y → ℕ) (hH : Measurable H)
    (hstep : ∀ y, H (T y) ≤ H y+1 ∧ H y ≤ H (T y)+1) (N : ℕ) :
    ∃ (D : Y → Fin 3) (decode : Fin (N+1) → Fin 3 → Fin (N+1)),
      Measurable D ∧
      (∀ y, decode (heightClip H N (T y)) (D y)=heightClip H N y) ∧
      (∀ y, D y=1 ↔ heightClip H N (T y)=heightClip H N y) := by
  classical
  let P := heightClip H N
  have hP : Measurable P := heightClip_measurable hH N
  let D : Y → Fin 3 := fun y =>
    if P y < P (T y) then 0 else if P (T y) < P y then 2 else 1
  have hD : Measurable D := by
    have hc : Measurable (fun z : Fin (N+1) × Fin (N+1) =>
        (if z.1 < z.2 then 0 else if z.2 < z.1 then 2 else 1 : Fin 3)) :=
      measurable_of_finite _
    exact hc.comp (hP.prodMk (hP.comp hT))
  let decode : Fin (N+1) → Fin 3 → Fin (N+1) := fun p q =>
    ⟨min N (if q=0 then p.val-1 else if q=2 then p.val+1 else p.val),
      Nat.lt_succ_of_le (min_le_left _ _)⟩
  have hdecode (y : Y) : decode (P (T y)) (D y)=P y := by
    have hs := hstep y
    by_cases hlt : P y < P (T y)
    · have he : D y=0 := by simp only [D,hlt,ite_true]
      rw [he]
      apply Fin.ext
      change min N (min (H (T y)) N-1)=min (H y) N
      change min (H y) N < min (H (T y)) N at hlt
      omega
    · by_cases hgt : P (T y) < P y
      · have he : D y=2 := by simp only [D,hlt,hgt,ite_false,ite_true]
        rw [he]
        apply Fin.ext
        change min N (min (H (T y)) N+1)=min (H y) N
        change min (H (T y)) N < min (H y) N at hgt
        omega
      · have he : D y=1 := by simp only [D,hlt,hgt,ite_false]
        rw [he]
        apply Fin.ext
        change min N (min (H (T y)) N)=min (H y) N
        change ¬min (H y) N < min (H (T y)) N at hlt
        change ¬min (H (T y)) N < min (H y) N at hgt
        omega
  refine ⟨D,decode,hD,hdecode,?_⟩
  intro y
  change D y=1 ↔ P (T y)=P y
  by_cases hlt : P y < P (T y)
  · have hn : P (T y) ≠ P y := ne_of_gt hlt
    simp [D,hlt,hn]
  · by_cases hgt : P (T y) < P y
    · have hn : P (T y) ≠ P y := ne_of_lt hgt
      simp [D,hlt,hgt,hn]
    · have he : P (T y)=P y := le_antisymm (le_of_not_gt hlt) (le_of_not_gt hgt)
      simp [D,he]

theorem heightClip_entropyRate_le_log_three
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (H : Y → ℕ) (hH : Measurable H)
    (hstep : ∀ y, H (T y) ≤ H y+1 ∧ H y ≤ H (T y)+1) (N : ℕ) :
    observationEntropyRate μ T (heightClip H N) ≤ Real.log 3 := by
  obtain ⟨D,decode,hD,hdecode,_⟩ := heightClip_increment_model hT.measurable H hH hstep N
  let P := heightClip H N
  have hP : Measurable P := heightClip_measurable hH N
  apply (observationEntropyRate_le_incrementEntropy μ hT P hP D hD decode hdecode).trans
  have he := finiteShannon_le_log_card (fun b =>
    measureReal_nonneg (μ := μ) (s := {y | D y=b}))
    (observation_distribution_sum μ D (fun b => hD (measurableSet_singleton b)))
  simpa only [observationEntropy,Fintype.card_fin,Nat.cast_ofNat] using he

end DukePrimeDegree

end

end OAI
